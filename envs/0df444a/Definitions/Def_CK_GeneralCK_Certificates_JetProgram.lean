-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_JetProgram
-- name    : CK_GeneralCK_Certificates_JetProgram
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:18:10.886816+00:00
-- url     : https://prove2.me/theorems/93ab9b85-4fc1-47e2-a0b4-bf88fef45725
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.JetProgram` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.JetProgram` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.JetProgram` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.JetProgram (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/JetProgram.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicContactBounds

namespace GeneralCK.Certificates.JetProgram

/-- Every nonlinear witness is checked; none is a semantic hypothesis. -/
inductive Op (p : ℕ) where
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | log (arg : ℕ) (lower upper : DyadicLog.Witness)
  | contact (arg : ℕ) (c B : DyadicInterval p) (outer : DyadicJetEnclosure p)
      (bracket : DyadicContact.BracketWitness p) (denominator : DyadicEntropy.BWitness p)

def zeroBox (p : ℕ) : DyadicJetEnclosure p := DyadicJetEnclosure.const p 0
def zeroJet : Jet2 := Jet2.const 0

namespace Op

def InRange {p : ℕ} (op : Op p) (n : ℕ) : Prop := match op with
  | .add i j | .mul i j => i<n ∧ j<n
  | .neg i | .inv i | .log i _ _ | .contact i _ _ _ _ _ => i<n

instance {p : ℕ} (op : Op p) (n : ℕ) : Decidable (op.InRange n) := by
  cases op <;> unfold InRange <;> infer_instance

noncomputable def eval {p : ℕ} (op : Op p) (jets : List Jet2) : Jet2 := match op with
  | .add i j => (jets.getD i zeroJet).add (jets.getD j zeroJet)
  | .neg i => (jets.getD i zeroJet).neg
  | .mul i j => (jets.getD i zeroJet).mul (jets.getD j zeroJet)
  | .inv i => (jets.getD i zeroJet).inv
  | .log i _ _ => (jets.getD i zeroJet).log
  | .contact i _ _ _ _ _ => reflectionContactJet.comp (jets.getD i zeroJet)

def check {p : ℕ} (op : Op p) (boxes : List (DyadicJetEnclosure p))
    (out : DyadicJetEnclosure p) : Bool :=
  decide (op.InRange boxes.length) && match op with
  | .add i j => ((boxes.getD i (zeroBox p)).add (boxes.getD j (zeroBox p))).subsetCheck out
  | .neg i => (boxes.getD i (zeroBox p)).neg.subsetCheck out
  | .mul i j => ((boxes.getD i (zeroBox p)).mul (boxes.getD j (zeroBox p))).subsetCheck out
  | .inv i => (boxes.getD i (zeroBox p)).invCheck out
  | .log i wl wu => DyadicLog.checkJet (boxes.getD i (zeroBox p)) out wl wu
  | .contact i c B outer w bw =>
      DyadicContact.jetCheck (boxes.getD i (zeroBox p)).value c B outer w bw &&
        (outer.comp (boxes.getD i (zeroBox p))).subsetCheck out

end Op

structure Instruction (p : ℕ) where
  op : Op p
  proposed : DyadicJetEnclosure p

def check {p : ℕ} : List (Instruction p) → List (DyadicJetEnclosure p) → Bool
  | [], _ => true
  | ins::rest, boxes => ins.op.check boxes ins.proposed && check rest (ins.proposed::boxes)

def finalBoxes {p : ℕ} : List (Instruction p) → List (DyadicJetEnclosure p) → List (DyadicJetEnclosure p)
  | [], boxes => boxes
  | ins::rest, boxes => finalBoxes rest (ins.proposed::boxes)

noncomputable def finalJets {p : ℕ} : List (Instruction p) → List Jet2 → List Jet2
  | [], jets => jets
  | ins::rest, jets => finalJets rest (ins.op.eval jets::jets)

def RegistersContain {p : ℕ} (boxes : List (DyadicJetEnclosure p)) (jets : List Jet2) (t : ℝ) : Prop :=
  boxes.length=jets.length ∧ ∀ i, (boxes.getD i (zeroBox p)).Contains (jets.getD i zeroJet) t

def RegistersSound (jets : List Jet2) (t : ℝ) : Prop := ∀ i, (jets.getD i zeroJet).SoundAt t

theorem RegistersContain.cons {p : ℕ} {boxes : List (DyadicJetEnclosure p)} {jets : List Jet2}
    {t : ℝ} {box : DyadicJetEnclosure p} {jet : Jet2} (h : RegistersContain boxes jets t)
    (hj : box.Contains jet t) : RegistersContain (box::boxes) (jet::jets) t := by
  refine ⟨by simpa using h.1,?_⟩
  intro i
  cases i with
  | zero => simpa using hj
  | succ i => simpa using h.2 i

theorem RegistersSound.cons {jets : List Jet2} {jet : Jet2} {t : ℝ}
    (h : RegistersSound jets t) (hj : jet.SoundAt t) : RegistersSound (jet::jets) t := by
  intro i
  cases i with
  | zero => simpa using hj
  | succ i => simpa using h i

theorem Op.check_encloses {p : ℕ} (op : Op p) {boxes : List (DyadicJetEnclosure p)}
    {jets : List Jet2} {out : DyadicJetEnclosure p} {t : ℝ}
    (h : RegistersContain boxes jets t) (hc : op.check boxes out=true) : out.Contains (op.eval jets) t := by
  have hd := (Bool.and_eq_true_iff.mp hc).2
  cases op with
  | add i j => exact DyadicJetEnclosure.subsetCheck_sound hd ((h.2 i).add (h.2 j))
  | neg i => exact DyadicJetEnclosure.subsetCheck_sound hd (h.2 i).neg
  | mul i j => exact DyadicJetEnclosure.subsetCheck_sound hd ((h.2 i).mul (h.2 j))
  | inv i => exact DyadicJetEnclosure.invCheck_sound hd (h.2 i)
  | log i wl wu => exact DyadicLog.checkJet_sound hd (h.2 i)
  | contact i c B outer w bw =>
    have hh := Bool.and_eq_true_iff.mp hd
    exact DyadicJetEnclosure.subsetCheck_sound hh.2 (DyadicContact.jetCheck_comp_sound hh.1 (h.2 i))

theorem Op.check_soundAt {p : ℕ} (op : Op p) {boxes : List (DyadicJetEnclosure p)}
    {jets : List Jet2} {out : DyadicJetEnclosure p} {t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets t)
    (hc : op.check boxes out=true) : (op.eval jets).SoundAt t := by
  have hd := (Bool.and_eq_true_iff.mp hc).2
  cases op with
  | add i j => exact (hs i).add (hs j)
  | neg i => exact (hs i).neg
  | mul i j => exact (hs i).mul (hs j)
  | inv i =>
    have hpos := DyadicInterval.positiveCheck_sound (Bool.and_eq_true_iff.mp hd).1 (h.2 i).1
    exact (hs i).inv hpos.ne'
  | log i wl wu =>
    have he := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hd).1).1
    have hp := DyadicLog.checkEndpoint_pos he
    have hpos := DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact (hs i).log hpos.ne'
  | contact i c B outer w bw =>
    have hj := (Bool.and_eq_true_iff.mp hd).1
    have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hj).1).1).1
    have hp := DyadicContact.bracketCheck_positive hb
    have hpos := DyadicInterval.positiveCheck_sound (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact reflectionContactJet_comp_soundAt (hs i) hpos

/-- Acceptance preserves enclosure semantics for every register. -/
theorem check_encloses {p : ℕ} (program : List (Instruction p)) {boxes : List (DyadicJetEnclosure p)}
    {jets : List Jet2} {t : ℝ} (h : RegistersContain boxes jets t) (hc : check program boxes=true) :
    RegistersContain (finalBoxes program boxes) (finalJets program jets) t := by
  induction program generalizing boxes jets with
  | nil => exact h
  | cons ins rest ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    exact ih (h.cons (ins.op.check_encloses h hh.1)) hh.2

/-- Domain guards and input soundness also preserve the actual derivative chain. -/
theorem check_preserves_sound {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicJetEnclosure p)} {jets : List Jet2} {t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets t) (hc : check program boxes=true) :
    RegistersSound (finalJets program jets) t := by
  induction program generalizing boxes jets with
  | nil => exact hs
  | cons ins rest ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    exact ih (h.cons (ins.op.check_encloses h hh.1))
      (hs.cons (ins.op.check_soundAt h hs hh.1)) hh.2

theorem check_encloses_on {p : ℕ} (program : List (Instruction p)) {boxes : List (DyadicJetEnclosure p)}
    {jets : List Jet2} {s : Set ℝ} (h : ∀ t ∈ s, RegistersContain boxes jets t)
    (hc : check program boxes=true) :
    ∀ t ∈ s, RegistersContain (finalBoxes program boxes) (finalJets program jets) t :=
  fun t ht => check_encloses program (h t ht) hc

theorem check_preserves_soundOn {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicJetEnclosure p)} {jets : List Jet2} {s : Set ℝ}
    (h : ∀ t ∈ s, RegistersContain boxes jets t) (hs : ∀ i, (jets.getD i zeroJet).SoundOn s)
    (hc : check program boxes=true) : ∀ i, ((finalJets program jets).getD i zeroJet).SoundOn s :=
  fun i t ht => check_preserves_sound program (h t ht) (fun i => hs i t ht) hc i

end GeneralCK.Certificates.JetProgram


