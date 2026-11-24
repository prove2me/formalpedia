-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:09.038623+00:00
-- url     : https://prove2.me/theorems/e489172a-e1a8-4083-bccd-b9a91f748e70
-- title:
--   Compact Haar Right Invariant Inst
-- statement:
--   Definitions and structural lemmas for Compact Haar Right Invariant Inst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactHaarRightInvariantInst.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory MeasureTheory.Measure
noncomputable section
namespace Formalism.REAL
section P0KLinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end P0KLinfty
lemma compact_haar_probability (n : ℕ) (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) := by
  unfold muK
  constructor
  have h := MeasureTheory.Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KG ε)))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
instance compact_haar_probability_inst (n : ℕ) (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) := compact_haar_probability n ε
lemma compact_haar_unique_left {n : ℕ} {ε : Fin n → Bool} (ν : Measure (KG ε)) [IsMulLeftInvariant ν]
    [IsProbabilityMeasure ν] : ν = muK ε := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    TopologicalSpace.secondCountableTopology_induced _ _ MulOpposite.unop
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    TopologicalSpace.secondCountableTopology_induced _ _ (Units.embedProduct _)
  haveI : SecondCountableTopology (UJ ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ)
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := MeasureTheory.Measure.haarMeasure_unique ν (⊤ : TopologicalSpace.PositiveCompacts (KG ε))
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, measure_univ, one_smul]
  rfl
lemma compact_haar_right_invariant (n : ℕ) (ε : Fin n → Bool) (k : KG ε) :
    Measure.map (fun x => x * k) (muK ε) = muK ε := by
  haveI : IsMulLeftInvariant (muK ε) := by
    unfold muK
    infer_instance
  have hm : Measurable (fun x : KG ε => x * k) := measurable_mul_const k
  haveI : IsProbabilityMeasure (Measure.map (fun x => x * k) (muK ε)) :=
    isProbabilityMeasure_map hm.aemeasurable
  haveI : IsMulLeftInvariant (Measure.map (fun x => x * k) (muK ε)) := by
    constructor
    intro g
    rw [Measure.map_map (measurable_const_mul g) hm]
    have e : ((g * ·) ∘ (· * k)) = ((· * k) ∘ (g * ·) : KG ε → KG ε) := by
      funext x
      simp [mul_assoc]
    rw [e, ← Measure.map_map hm (measurable_const_mul g), map_mul_left_eq_self]
  exact compact_haar_unique_left _
instance compact_haar_right_invariant_inst (n : ℕ) (ε : Fin n → Bool) : IsMulRightInvariant (muK ε) :=
  ⟨fun k => compact_haar_right_invariant n ε k⟩
end Formalism.REAL


