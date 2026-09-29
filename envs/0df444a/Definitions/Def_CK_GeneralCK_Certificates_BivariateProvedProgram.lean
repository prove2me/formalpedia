-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
-- name    : CK_GeneralCK_Certificates_BivariateProvedProgram
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:29.09875+00:00
-- url     : https://prove2.me/theorems/17022cfc-0dac-4f5c-96c9-39da6d345109
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.BivariateProvedProgram` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.BivariateProvedProgram` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.BivariateProvedProgram` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.BivariateProvedProgram (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/BivariateProvedProgram.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ProvedTranscendental
import Definitions.Def_CK_GeneralCK_Certificates_BivariateJetProgramTaylor
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

-- ===== source module GeneralCK.Certificates.BivariateProvedProgram =====
section

namespace GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set















































theorem finalJets_eq_executeShapes {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) : finalJets program jets=executeShapes (shapes program) jets := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih => simpa only [finalJets,shapes,List.map_cons,executeShapes] using ih (ins.shape.eval jets::jets)

theorem finalJets_eq_of_shapes_eq {p q : ℕ} {left : List (Instruction p)}
    {right : List (Instruction q)} (h : shapes left=shapes right) (jets : List BivariateJet2) :
    finalJets left jets=finalJets right jets := by
  rw [finalJets_eq_executeShapes,finalJets_eq_executeShapes,h]

/-- A new proof-based program has exactly the old program semantics when its
operation list agrees. Interval proposals and proof formats cannot alter it. -/
theorem finalJets_eq_old {p q : ℕ} {program : List (Instruction p)}
    {old : List (BivariateJetProgram.Instruction q)}
    (h : shapes program=BivariateJetProgram.shapes old) (jets : List BivariateJet2) :
    finalJets program jets=BivariateJetProgram.finalJets old jets := by
  rw [finalJets_eq_executeShapes,BivariateJetProgram.finalJets_eq_executeShapes,h]

theorem StepValid.encloses {p : ℕ} (shape : Shape)
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {out : DyadicBivariateJetEnclosure p} {t : ℝ}
    (h : RegistersContain boxes jets t) (hc : StepValid shape boxes out) :
    out.Contains (shape.eval jets) t := by
  have hd := hc.2
  cases shape with
  | add i j => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd ((h.2 i).add (h.2 j))
  | neg i => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd (h.2 i).neg
  | mul i j => exact DyadicBivariateJetEnclosure.subsetCheck_sound hd ((h.2 i).mul (h.2 j))
  | inv i => simpa only [Shape.eval,BivariateJet2.inv_eq_outerCompose] using
      DyadicBivariateJetEnclosure.invCheck_sound hd (h.2 i)
  | log i =>
    simpa only [Shape.eval,BivariateJet2.log_eq_outerCompose] using
      DyadicBivariateJetEnclosure.subsetCheck_sound hd.2.2
        (ProvedTranscendental.bivariateLog_sound (h.2 i) hd.1 hd.2.1)
  | contact i =>
    obtain ⟨outer,ho,hsub⟩ := hd.2
    exact DyadicBivariateJetEnclosure.subsetCheck_sound hsub
      (DyadicBivariateJetEnclosure.Contains.outerCompose (ho _ (h.2 i).1) (h.2 i))

theorem StepValid.soundAt {p : ℕ} (shape : Shape)
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {out : DyadicBivariateJetEnclosure p} {da dz t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets da dz t)
    (hc : StepValid shape boxes out) : (shape.eval jets).DirectionalSoundAt da dz t := by
  have hd := hc.2
  cases shape with
  | add i j => exact (hs i).add (hs j)
  | neg i => exact (hs i).neg
  | mul i j => exact (hs i).mul (hs j)
  | inv i =>
    have hp := DyadicBivariateJetEnclosure.invCheck_positive hd
    have hpos := DyadicInterval.positiveCheck_sound
      (by simpa [DyadicInterval.positiveCheck] using hp) (h.2 i).1
    exact (hs i).inv hpos.ne'
  | log i =>
    have hpos := DyadicInterval.positiveCheck_sound
      (by simpa [DyadicInterval.positiveCheck] using hd.1) (h.2 i).1
    exact (hs i).log hpos.ne'
  | contact i =>
    have hpos := DyadicInterval.positiveCheck_sound
      (by simpa [DyadicInterval.positiveCheck] using hd.1) (h.2 i).1
    exact BivariateJet2.DirectionalSoundAt.outerCompose (reflectionContactJet_soundAt hpos) (hs i)

theorem Accepted.encloses {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2} {t : ℝ}
    (h : RegistersContain boxes jets t) (hc : Accepted program boxes) :
    RegistersContain (finalBoxes program boxes) (finalJets program jets) t := by
  induction program generalizing boxes jets with
  | nil => exact h
  | cons ins rest ih => exact ih (h.cons (StepValid.encloses ins.shape h hc.1)) hc.2

theorem Accepted.preserves_sound {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2} {da dz t : ℝ}
    (h : RegistersContain boxes jets t) (hs : RegistersSound jets da dz t)
    (hc : Accepted program boxes) : RegistersSound (finalJets program jets) da dz t := by
  induction program generalizing boxes jets with
  | nil => exact hs
  | cons ins rest ih =>
    exact ih (h.cons (StepValid.encloses ins.shape h hc.1))
      (hs.cons (StepValid.soundAt ins.shape h hs hc.1)) hc.2

theorem Accepted.preserves_soundOn {p : ℕ} (program : List (Instruction p))
    {boxes : List (DyadicBivariateJetEnclosure p)} {jets : List BivariateJet2}
    {s : Set ℝ} {da dz : ℝ}
    (h : ∀ t ∈ s, RegistersContain boxes jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz s)
    (hc : Accepted program boxes) :
    ∀ i, ((finalJets program jets).getD i zeroJet).DirectionalSoundOn da dz s :=
  fun i t ht => hc.preserves_sound program (h t ht) (fun i => hs i t ht) i

theorem value_pos_of_accepted_taylor {p q : ℕ}
    (center : List (Instruction p)) (whole : List (Instruction q))
    {centerInputs : List (DyadicBivariateJetEnclosure p)}
    {wholeInputs : List (DyadicBivariateJetEnclosure q)} {jets : List BivariateJet2}
    (i : ℕ) {da dz ra rz : ℝ}
    (hshape : shapes center=shapes whole)
    (hc : RegistersContain centerInputs jets 0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInputs jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hcc : Accepted center centerInputs) (hwc : Accepted whole wholeInputs)
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower
      ((finalBoxes center centerInputs).getD i (zeroBox p)).toReal
      ((finalBoxes whole wholeInputs).getD i (zeroBox q)).toReal ra rz) :
    0<((finalJets whole jets).getD i zeroJet).value 1 := by
  have heq := finalJets_eq_of_shapes_eq hshape jets
  have hcenter := (Accepted.encloses center hc hcc).2 i
  rw [heq] at hcenter
  exact DyadicBivariateJetEnclosure.value_pos_of_separate_taylor
    (Accepted.preserves_soundOn whole hw hs hwc i) hcenter
    (fun t ht => (Accepted.encloses whole (hw t ht) hwc).2 i) hra hrz hda hdz ht

theorem step_rejects_invalid_index {p : ℕ} {shape : Shape}
    {boxes : List (DyadicBivariateJetEnclosure p)} {out : DyadicBivariateJetEnclosure p}
    (h : ¬InRange shape boxes.length) : ¬StepValid shape boxes out := fun hv => h hv.1









theorem eval_value (shape : Shape) (jets : List BivariateJet2) (t : ℝ) :
    (shape.eval jets).value t=evalReal shape (jets.map (fun j => j.value t)) := by
  cases shape <;> simp only [Shape.eval,evalReal,BivariateJet2.add,BivariateJet2.neg,
    BivariateJet2.mul,BivariateJet2.inv,BivariateJet2.log,BivariateJet2.outerCompose,
    reflectionContactJet,BivariateJetProgram.value_getD]





theorem finalJets_values {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) (t : ℝ) :
    (finalJets program jets).map (fun j => j.value t)=
      evalRealProgram program (jets.map (fun j => j.value t)) := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih =>
    simpa only [finalJets,evalRealProgram,List.map_cons,eval_value] using
      ih (ins.shape.eval jets::jets)

theorem finalJet_value {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) (i : ℕ) (t : ℝ) :
    ((finalJets program jets).getD i zeroJet).value t=
      (evalRealProgram program (jets.map (fun j => j.value t))).getD i 0 := by
  rw [BivariateJetProgram.value_getD,finalJets_values]

end GeneralCK.Certificates.BivariateProvedProgram

end


