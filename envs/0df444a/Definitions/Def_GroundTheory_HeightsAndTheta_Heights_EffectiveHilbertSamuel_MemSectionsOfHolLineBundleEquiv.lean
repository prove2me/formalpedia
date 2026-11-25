-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
-- name    : GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:00.451909+00:00
-- url     : https://prove2.me/theorems/92fef9cd-a6fc-452b-b9b5-e7bf04878b6e
-- title:
--   Mem Sections Of Hol Line Bundle Equiv
-- statement:
--   Definitions and structural lemmas for Mem Sections Of Hol Line Bundle Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/MemSectionsOfHolLineBundleEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HolLineBundle_sections_eq_sectionSpace_f575eeea46f9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.EffectiveHS
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS (topForms topFormWeightedL2 twist wAdd fsPhi HermSpace FSData HSData
  secMul l2n tuples jacDet)
open scoped ENNReal
noncomputable section
namespace TranslateEq
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
theorem jac_eq_jacDet (j k : Fin A.n) (x : X) : jac A j k x = jacDet A j k x := rfl
theorem twist_g (L₂ L : HolLineBundle A) (m : ℕ) (j k : Fin A.n) (x : X) :
    (twist L₂.toIndefiniteRowSideFullHecke L.toIndefiniteRowSideFullHecke m).g j k x = L₂.g j k x * L.g j k x ^ m := rfl
theorem topSections_eq_topForms (L₂ L : HolLineBundle A) (m : ℕ) :
    topSections A L₂ L m = topForms (twist L₂.toIndefiniteRowSideFullHecke L.toIndefiniteRowSideFullHecke m) := by
  ext u
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h3, fun j k x hx => ?_⟩
    rw [h2 j k x hx, twist_g, jac_eq_jacDet]; ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j k x hx => ?_, h2⟩
    rw [h3 j k x hx, twist_g, jac_eq_jacDet]; ring
theorem log_normSq_mul_pow {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℕ) :
    Real.log (‖a * b ^ m‖ ^ 2) = Real.log (‖a‖ ^ 2) + m * Real.log (‖b‖ ^ 2) := by
  have h : ‖a * b ^ m‖ ^ 2 = ‖a‖ ^ 2 * (‖b‖ ^ 2) ^ m := by rw [norm_mul, norm_pow]; ring
  rw [h, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ha))
    (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 hb))), Real.log_pow (‖b‖ ^ 2) m]
theorem isWeight_wAdd {L₂ L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A}
    {ψ φ : Fin A.n → X → ℝ} (hψ : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L₂ ψ)
    (hφ : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L φ) (m : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight (twist L₂ L m) (wAdd ψ φ m) := by
  refine ⟨fun j l => (hψ.1 j l).add (contDiffOn_const.mul (hφ.1 j l)), fun j k x hx => ?_⟩
  show ψ j x + m * φ j x = ψ k x + m * φ k x + Real.log (‖L₂.g j k x * L.g j k x ^ m‖ ^ 2)
  rw [log_normSq_mul_pow (L₂.ne_zero j k x hx) (L.ne_zero j k x hx), hψ.2 j k x hx, hφ.2 j k x hx]
  ring
theorem noCommonZero_iff {N : ℕ} (L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (e : Fin N → Fin A.n → X → ℂ) (he : ∀ i, e i ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L 1) :
    NoCommonZero A e ↔ ∀ j, ∀ x ∈ (A.chart j).source, ∃ i, e i j x ≠ 0 := by
  constructor
  · intro h j x hx
    obtain ⟨i, hi⟩ := h x
    refine ⟨i, fun h0 => hi ?_⟩
    obtain ⟨-, -, hc⟩ := he i
    rw [hc (chartIdx A x) j x ⟨Classical.choose_spec (A.cover x), hx⟩, h0, mul_zero]
  · intro h x
    exact h _ x (Classical.choose_spec (A.cover x))
theorem mem_sections_of_holLineBundle_equiv (L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    {f : Fin A.n → X → ℂ} (hf : f ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L 1) :
    f ∈ (HolLineBundle.split_model_to_place_model L).sections 1 := by
  rw [HolLineBundle.sections_eq_sectionSpace]; exact hf
section FS
variable {Y : Type} [TopologicalSpace Y] (d : FSData A Y)
end FS
section Translate
variable {Y : Type} [TopologicalSpace Y]
def toEmbDatum [T2Space X] (d : FSData A Y) (hA : IsAlgCover A) : EmbDatum D where
  U := X
  A := A
  cover := hA
  L := HolLineBundle.split_model_to_place_model d.L
  L₂ := HolLineBundle.split_model_to_place_model d.L₂
  N := d.W.n
  N₂ := d.W₂.n
  e := d.W.e
  e₂ := d.W₂.e
  e_mem i := mem_sections_of_holLineBundle_equiv d.L (d.W.mem i)
  e₂_mem i := mem_sections_of_holLineBundle_equiv d.L₂ (d.W₂.mem i)
  gen := (noCommonZero_iff d.L d.W.e d.W.mem).2 d.gen
  gen₂ := (noCommonZero_iff d.L₂ d.W₂.e d.W₂.mem).2 d.gen₂
theorem sec_single {B : Submodule ℂ (Fin A.n → X → ℂ)} (H : HermSpace B) (i : Fin H.n) :
    H.sec (Pi.single i 1) = H.e i := by
  unfold IndefiniteRowSideFullHecke.EffectiveHS.HermSpace.sec
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
def toZeroDatum [T2Space X] (d : FSData A Y) (hA : IsAlgCover A) (s : Fin D → Fin d.W.n → ℂ)
    (hs : d.IsGoodS s) (hfl : FLBound A d.W.e fun i => d.W.sec (s i)) :
    ZeroDatum (toEmbDatum d hA) where
  c := s
  finite := hs.finite
  nondeg := hs.etale
  fl := hfl
def toZeroDatumOf (hFL : FLBoundOfGoodS.Statement) [T2Space X] [CompactSpace Y] (d : FSData A Y)
    (hA : IsAlgCover A) (s : Fin D → Fin d.W.n → ℂ) (hs : d.IsGoodS s) :
    ZeroDatum (toEmbDatum d hA) :=
  toZeroDatum d hA s hs (hFL D X Y A d s hs)
def toTwistWeight (d : HSData A Y) :
    TwistWeight A (HolLineBundle.split_model_to_place_model d.L₂) (HolLineBundle.split_model_to_place_model d.L) D where
  φ := d.φA
  smooth := d.isWeightA.1
  compat j k x hx := by
    show d.φA j x = d.φA k x + Real.log (‖d.L₂.g j k x‖ ^ 2) + D * Real.log (‖d.L.g j k x‖ ^ 2)
    rw [d.isWeightA.2 j k x hx]
    show d.φA k x + Real.log (‖d.L₂.g j k x * d.L.g j k x ^ D‖ ^ 2) = _
    rw [log_normSq_mul_pow (d.L₂.ne_zero j k x hx) (d.L.ne_zero j k x hx)]; ring
  psh j y hy w := (d.pshA j j).2 y ⟨hy, (A.chart j).map_target hy⟩ w
theorem space_le_topForms (d : HSData A Y) (j : ℕ) :
    (d.V j).space ≤ topForms (twist d.L₂ d.L (D + j)) :=
  Submodule.span_le.2 (Set.range_subset_iff.2 (d.V j).mem)
def toSpaceDatum [T2Space X] [SecondCountableTopology X] (hN : TopFormNormEqIntegral.Statement)
    (hV : NatSpaceEqVnat.Statement) (d : HSData A Y) (hA : IsAlgCover A) (h0 : d.H0')
    (h1 : d.H1) (h2 : d.H2') : SpaceDatum (toEmbDatum d.toFSData hA) d.T where
  β := d.β
  one_le_β := d.one_le_β
  φA := toTwistWeight d
  φA_le := d.boundA
  V j := (d.V j).space
  V_le j := by
    rw [topSections_eq_topForms]
    exact space_le_topForms d j
  normT := (d.V d.T).hnorm
  sections_zero_mem_natural F hF := (Set.ext_iff.1 (hV D X Y A d 0) F).1 (h0.1 hF)
  sections_top_mem_natural F hF := h0.2 ((Set.ext_iff.1 (hV D X Y A d D) F).2 hF)
  H1 j hj i F hF := by
    have h := (h1 j hj (Pi.single (show Fin d.W.n from i) 1) F hF).1
    rw [sec_single] at h
    exact h
  H2 F hF := by
    have e := hN D X A _ _ F (isWeight_wAdd d.isWeight₂ d.isWeight (D + d.T))
      (space_le_topForms d d.T hF)
    exact (h2 F hF).trans_eq (congrArg _ e.symm)
end Translate
end TranslateEq
end
end GroundTheory.Heights₂.Heights.EffectiveHS


