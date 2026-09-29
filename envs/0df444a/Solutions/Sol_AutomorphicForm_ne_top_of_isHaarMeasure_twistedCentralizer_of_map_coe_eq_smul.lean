-- Prove2me | solution 1 for AutomorphicForm.ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0c9d7a29-7454-5d50-bd08-80166a64aea7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

namespace HsFinite28

end HsFinite28

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (hτa : τa.IsHaarMeasure)
    (s : ℝ≥0∞) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ ν : Measure (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
          ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa =
        s • ν →
      s ≠ ⊤ := by
  intro ν hmap

  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI hTR := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI hT2 := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI hTG := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI hLC := AutomorphicForm.locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)

  have hσcont : Continuous (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) := by
    have h := IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L (InfiniteAdeleRing K) σ.toAlgHom).toLinearMap
    convert h using 1
    rfl
  have hσGL : Continuous (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)
      exact Units.continuous_val.matrix_map hσcont
    · have : (fun t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => ((AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ t)⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).val) =
          fun t => ((t⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) := by
        funext t; rw [← map_inv]; rfl
      rw [this]
      exact Units.continuous_coe_inv.matrix_map hσcont

  have hclosed : IsClosed (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := by
    have : (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        (fun t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => t * δ * (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ t)⁻¹) ⁻¹' {δ} := by
      ext t; exact Iff.rfl
    rw [this]
    exact (isClosed_singleton).preimage ((continuous_id.mul continuous_const).mul (hσGL.inv))
  haveI hLC' : LocallyCompactSpace ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := hclosed.locallyCompactSpace
  haveI := hτa

  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (1 : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ))
  have hpos : 0 < τa C := Measure.measure_pos_of_mem_nhds τa hCn
  have hfin : τa C < ⊤ := hCc.measure_lt_top

  letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  have hcoe : Continuous fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) => ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinj : Function.Injective fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) => ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    fun a b h => Subtype.ext (Units.ext h)
  have hmeasC : MeasurableSet ((fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) => ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) '' C) :=
    (hCc.image hcoe).isClosed.measurableSet
  have heval := congr_arg (fun m : Measure (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) => m ((fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) => ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) '' C)) hmap
  simp only [Measure.map_apply hcoe.measurable hmeasC, Set.preimage_image_eq _ hinj, Measure.smul_apply,
    smul_eq_mul] at heval

  intro hs
  rw [hs, ENNReal.top_mul'] at heval
  split_ifs at heval
  · exact hpos.ne' heval
  · exact hfin.ne heval

end S_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_ne_top_of_isHaarMeasure_twistedCentralizer_of_map_coe_eq_smul (solution)
