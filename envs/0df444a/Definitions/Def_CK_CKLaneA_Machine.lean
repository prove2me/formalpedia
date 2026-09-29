-- Prove2me | Definitions.Def_CK_CKLaneA_Machine
-- name    : CK_CKLaneA_Machine
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:43:42.927695+00:00
-- url     : https://prove2.me/theorems/86e7dfa5-7e93-4b5f-b8ca-0e05eecd869b
-- title:
--   Courtade–Kumar proof module `CKLaneA.Machine` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA.Machine` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA.Machine` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA.Machine (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA/Machine.lean)

import Definitions.Def_CK_CKLaneA_LogKap
import Definitions.Def_CK_GeneralCK_Certificates_BivariateJetProgramTaylor

/-!
# Lane A: a register machine of second-order bivariate jet enclosures

`evalProg` computes (does not merely check) enclosures; `realProg` is the exact real
jet semantics. `evalProg_sound` is proved once for every program.
-/

namespace CKLaneA
open GeneralCK GeneralCK.Certificates

inductive Op where
  | cst (z : ℤ)
  | add (i j : ℕ)
  | neg (i : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  | log (i : ℕ)
  | psi (i : ℕ)
  | kap (i : ℕ)
  deriving Repr

section Machine
variable {p : ℕ}

abbrev DJ (p : ℕ) := DyadicBivariateJetEnclosure p
abbrev BJ := BivariateJet2

def zeroDJ : DJ p := ⟨DI.zero, DI.zero, DI.zero, DI.zero, DI.zero, DI.zero⟩
def zeroBJ : BJ := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def cstDJ (z : ℤ) : DJ p := ⟨DI.pt z, DI.zero, DI.zero, DI.zero, DI.zero, DI.zero⟩
def cstBJ (x : ℝ) : BJ := ⟨fun _ => x, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def evalOp (L2 : DyadicInterval p) (hint : ℤ × ℤ) (op : Op) (regs : List (DJ p)) : Option (DJ p) :=
  match op with
  | .cst z => some (cstDJ z)
  | .add i j => some ((regs.getD i zeroDJ).add (regs.getD j zeroDJ))
  | .neg i => some (regs.getD i zeroDJ).neg
  | .mul i j => some ((regs.getD i zeroDJ).mul (regs.getD j zeroDJ))
  | .inv i => if 0 < (regs.getD i zeroDJ).value.lo then some (regs.getD i zeroDJ).inv else none
  | .log i => if logIvOK (regs.getD i zeroDJ).value then
      some (DyadicBivariateJetEnclosure.outerCompose (logJetEnc L2 (regs.getD i zeroDJ).value)
        (regs.getD i zeroDJ)) else none
  | .psi i => if psiOKA (regs.getD i zeroDJ).value then
      some (DyadicBivariateJetEnclosure.outerCompose (psiEncA (regs.getD i zeroDJ).value)
        (regs.getD i zeroDJ)) else none
  | .kap i => if kapOK L2 hint (regs.getD i zeroDJ).value then
      some (DyadicBivariateJetEnclosure.outerCompose (kapEnc L2 hint) (regs.getD i zeroDJ)) else none

noncomputable def realOp (p : ℕ) (op : Op) (regs : List BJ) : BJ :=
  match op with
  | .cst z => cstBJ ((z : ℝ) / DyadicInterval.scale p)
  | .add i j => (regs.getD i zeroBJ).add (regs.getD j zeroBJ)
  | .neg i => (regs.getD i zeroBJ).neg
  | .mul i j => (regs.getD i zeroBJ).mul (regs.getD j zeroBJ)
  | .inv i => BivariateJet2.outerCompose Jet2.variableJet.inv (regs.getD i zeroBJ)
  | .log i => BivariateJet2.outerCompose (Jet2.log Jet2.variableJet) (regs.getD i zeroBJ)
  | .psi i => BivariateJet2.outerCompose psiJet (regs.getD i zeroBJ)
  | .kap i => BivariateJet2.outerCompose kapJet (regs.getD i zeroBJ)

def evalProg (L2 : DyadicInterval p) (hint : ℤ × ℤ) : List Op → List (DJ p) → Option (List (DJ p))
  | [], regs => some regs
  | op :: rest, regs =>
    match evalOp L2 hint op regs with
    | some o => evalProg L2 hint rest (o :: regs)
    | none => none

noncomputable def realProg (p : ℕ) : List Op → List BJ → List BJ
  | [], regs => regs
  | op :: rest, regs => realProg p rest (realOp p op regs :: regs)

/-- the invariant: every register encloses and is a sound jet at `t` -/
def Regs (boxes : List (DJ p)) (jets : List BJ) (da dz t : ℝ) : Prop :=
  ∀ i, (boxes.getD i zeroDJ).Contains (jets.getD i zeroBJ) t ∧
    (jets.getD i zeroBJ).DirectionalSoundAt da dz t

theorem zeroDJ_contains (t : ℝ) : (zeroDJ : DJ p).Contains zeroBJ t := by
  refine ⟨DI.zero_contains, DI.zero_contains, DI.zero_contains, DI.zero_contains,
    DI.zero_contains, DI.zero_contains⟩

theorem cstBJ_sound (x da dz t : ℝ) : (cstBJ x).DirectionalSoundAt da dz t := by
  constructor
  · simpa [cstBJ, BivariateJet2.projection] using hasDerivAt_const t x
  · simpa [cstBJ, BivariateJet2.projection] using hasDerivAt_const t (0:ℝ)

theorem zeroBJ_sound (da dz t : ℝ) : (zeroBJ).DirectionalSoundAt da dz t := by
  have := cstBJ_sound 0 da dz t
  simpa [cstBJ, zeroBJ] using this

theorem Regs.cons {boxes : List (DJ p)} {jets : List BJ} {da dz t : ℝ} (h : Regs boxes jets da dz t)
    {o : DJ p} {j : BJ} (ho : o.Contains j t) (hj : j.DirectionalSoundAt da dz t) :
    Regs (o :: boxes) (j :: jets) da dz t := by
  intro i
  cases i with
  | zero => exact ⟨ho, hj⟩
  | succ i => simpa using h i

theorem evalOp_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2)) {hint : ℤ × ℤ}
    {op : Op} {boxes : List (DJ p)} {jets : List BJ} {da dz t : ℝ}
    (hr : Regs boxes jets da dz t) {o : DJ p} (h : evalOp L2 hint op boxes = some o) :
    o.Contains (realOp p op jets) t ∧ (realOp p op jets).DirectionalSoundAt da dz t := by
  cases op with
  | cst z =>
    simp only [evalOp, Option.some.injEq] at h
    subst h
    refine ⟨⟨DI.pt_contains z, DI.zero_contains, DI.zero_contains, DI.zero_contains,
      DI.zero_contains, DI.zero_contains⟩, cstBJ_sound _ _ _ _⟩
  | add i j =>
    simp only [evalOp, Option.some.injEq] at h
    subst h
    exact ⟨(hr i).1.add (hr j).1, (hr i).2.add (hr j).2⟩
  | neg i =>
    simp only [evalOp, Option.some.injEq] at h
    subst h
    exact ⟨(hr i).1.neg, (hr i).2.neg⟩
  | mul i j =>
    simp only [evalOp, Option.some.injEq] at h
    subst h
    exact ⟨(hr i).1.mul (hr j).1, (hr i).2.mul (hr j).2⟩
  | inv i =>
    simp only [evalOp] at h
    split_ifs at h with hpos
    simp only [Option.some.injEq] at h
    subst h
    have hv := (hr i).1
    have hvpos : 0 < (jets.getD i zeroBJ).value t := pos_of_lo_pos hv.1 hpos
    refine ⟨hv.inv hpos, ?_⟩
    exact BivariateJet2.DirectionalSoundAt.outerCompose
      ((Jet2.soundAt_variable _).inv (by simpa [Jet2.variableJet] using hvpos.ne')) (hr i).2
  | log i =>
    simp only [evalOp] at h
    split_ifs at h with hok
    simp only [Option.some.injEq] at h
    subst h
    have hv := (hr i).1
    obtain ⟨hc, hpos⟩ := logJetEnc_sound hL2 hok hv.1
    refine ⟨DyadicBivariateJetEnclosure.Contains.outerCompose hc hv, ?_⟩
    exact BivariateJet2.DirectionalSoundAt.outerCompose
      ((Jet2.soundAt_variable _).log (by simpa [Jet2.variableJet] using hpos.ne')) (hr i).2
  | psi i =>
    simp only [evalOp] at h
    split_ifs at h with hok
    simp only [Option.some.injEq] at h
    subst h
    have hv := (hr i).1
    obtain ⟨hc, habs⟩ := psiEncA_sound hok hv.1
    exact ⟨DyadicBivariateJetEnclosure.Contains.outerCompose hc hv,
      BivariateJet2.DirectionalSoundAt.outerCompose (psiJet_soundAt habs) (hr i).2⟩
  | kap i =>
    simp only [evalOp] at h
    split_ifs at h with hok
    simp only [Option.some.injEq] at h
    subst h
    have hv := (hr i).1
    exact ⟨DyadicBivariateJetEnclosure.Contains.outerCompose (kapEnc_sound hL2 hok hv.1) hv,
      BivariateJet2.DirectionalSoundAt.outerCompose (kapJet_soundAt _) (hr i).2⟩

theorem evalProg_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2)) {hint : ℤ × ℤ} :
    ∀ (prog : List Op) {boxes : List (DJ p)} {jets : List BJ} {da dz t : ℝ}
      (hr : Regs boxes jets da dz t) {out : List (DJ p)}
      (h : evalProg L2 hint prog boxes = some out), Regs out (realProg p prog jets) da dz t
  | [], boxes, jets, da, dz, t, hr, out, h => by
    simp only [evalProg, Option.some.injEq] at h
    subst h; exact hr
  | op :: rest, boxes, jets, da, dz, t, hr, out, h => by
    simp only [evalProg] at h
    split at h
    · next o ho =>
      obtain ⟨hc, hs⟩ := evalOp_sound hL2 hr ho
      exact evalProg_sound hL2 rest (hr.cons hc hs) h
    · exact absurd h (by simp)

/-! ## scalar (value) semantics -/

noncomputable def valOp (p : ℕ) (op : Op) (vals : List ℝ) : ℝ :=
  match op with
  | .cst z => (z : ℝ) / DyadicInterval.scale p
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .neg i => -vals.getD i 0
  | .mul i j => vals.getD i 0 * vals.getD j 0
  | .inv i => (vals.getD i 0)⁻¹
  | .log i => Real.log (vals.getD i 0)
  | .psi i => psi (vals.getD i 0)
  | .kap i => Reflection.regularContact (vals.getD i 0)

noncomputable def valProg (p : ℕ) : List Op → List ℝ → List ℝ
  | [], vals => vals
  | op :: rest, vals => valProg p rest (valOp p op vals :: vals)

theorem getD_value (jets : List BJ) (i : ℕ) (t : ℝ) :
    (jets.getD i zeroBJ).value t = (jets.map (fun j => j.value t)).getD i 0 := by
  induction jets generalizing i with
  | nil => simp [zeroBJ]
  | cons j rest ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem realOp_value (op : Op) (jets : List BJ) (t : ℝ) :
    (realOp p op jets).value t = valOp p op (jets.map (fun j => j.value t)) := by
  cases op <;>
    simp only [realOp, valOp, cstBJ, BivariateJet2.add, BivariateJet2.neg, BivariateJet2.mul,
      BivariateJet2.outerCompose, Jet2.inv, Jet2.log, Jet2.variableJet, psiJet, kapJet, getD_value, id]

theorem realProg_value : ∀ (prog : List Op) (jets : List BJ) (t : ℝ),
    (realProg p prog jets).map (fun j => j.value t) = valProg p prog (jets.map (fun j => j.value t))
  | [], jets, t => rfl
  | op :: rest, jets, t => by
    simp only [realProg, valProg]
    rw [realProg_value rest _ t]
    simp only [List.map_cons, realOp_value]

end Machine
end CKLaneA


