-- Prove2me | solution 1 for AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/20cec186-031e-5906-8cc7-9ca8f1fc7370

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det

set_option autoImplicit false

open NumberField

namespace EntryPreimage

noncomputable section

variable (F : Type) [Field F]

open scoped Classical in
private theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

open scoped Classical in
private theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_ringEquiv_mixedSpace F).comp (hval.matrix_elem i j)

open scoped Classical in
private theorem of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix.of (AutomorphicForm.archEntries F g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F →+* mixedEmbedding.mixedSpace F).mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  Matrix.ext fun _ _ => rfl

open scoped Classical in

private theorem isUnit_det_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    IsUnit (Matrix.det (Matrix.of (AutomorphicForm.archEntries F g))) := by
  rw [of_archEntries, ← RingHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).map _

open scoped Classical in

private theorem continuous_symm_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  by_cases hv : InfinitePlace.IsReal v
  · have h : (fun y : mixedEmbedding.mixedSpace F => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv _ = _
      rw [IsometryEquiv.apply_symm_apply]
      have hy := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hy
      exact congrFun (congrArg Prod.fst hy) ⟨v, hv⟩
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hv' : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have h : (fun y : mixedEmbedding.mixedSpace F => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').injective
      change InfinitePlace.Completion.extensionEmbedding v _ = _
      rw [IsometryEquiv.apply_symm_apply]
      have hy := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hy
      exact congrFun (congrArg Prod.snd hy) ⟨v, hv'⟩
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

open scoped Classical in

private def adeleMatrix (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :
    mixedEmbedding.mixedSpace F →+* InfiniteAdeleRing F).mapMatrix (Matrix.of E)

open scoped Classical in
private theorem continuous_adeleMatrix : Continuous (adeleMatrix F) := by
  refine continuous_matrix fun i j => ?_
  simp only [adeleMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingEquiv.coe_toRingHom]
  exact (continuous_symm_ringEquiv_mixedSpace F).comp ((continuous_apply j).comp (continuous_apply i))

open scoped Classical in
private theorem isUnit_det_adeleMatrix (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (hE : IsUnit (Matrix.det (Matrix.of E))) : IsUnit (adeleMatrix F E).det := by
  unfold adeleMatrix
  rw [← RingHom.map_det]
  exact hE.map _

private theorem continuousAt_inverse [NumberField F] (u : (InfiniteAdeleRing F)ˣ) :
    ContinuousAt (Ring.inverse : InfiniteAdeleRing F → InfiniteAdeleRing F) u := by
  letI : NormedRing (InfiniteAdeleRing F) :=
    inferInstanceAs (NormedRing ((v : InfinitePlace F) → v.Completion))
  letI : CompleteSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (CompleteSpace ((v : InfinitePlace F) → v.Completion))
  exact NormedRing.inverse_continuousAt u

open scoped Classical in

private noncomputable def sectionGL
    (E : {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F // IsUnit (Matrix.det (Matrix.of E))}) :
    GL (Fin 2) (InfiniteAdeleRing F) :=
  ⟨adeleMatrix F E.1, (adeleMatrix F E.1)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_det_adeleMatrix F E.1 E.2),
    Matrix.nonsing_inv_mul _ (isUnit_det_adeleMatrix F E.1 E.2)⟩

open scoped Classical in
private theorem continuous_sectionGL [NumberField F] : Continuous (sectionGL F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_adeleMatrix F).comp continuous_subtype_val
  · change Continuous fun E : {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F //
      IsUnit (Matrix.det (Matrix.of E))} => (adeleMatrix F E.1)⁻¹
    refine continuous_iff_continuousAt.2 fun E => ?_
    have hdet : ContinuousAt Ring.inverse (adeleMatrix F E.1).det := by
      obtain ⟨u, hu⟩ := isUnit_det_adeleMatrix F E.1 E.2
      rw [← hu]
      exact continuousAt_inverse F u
    exact ContinuousAt.comp (g := Inv.inv)
      (f := fun E' : {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F // IsUnit (Matrix.det (Matrix.of E))} =>
        adeleMatrix F E'.1)
      (continuousAt_matrix_inv _ hdet) ((continuous_adeleMatrix F).comp continuous_subtype_val).continuousAt

open scoped Classical in
open Topology in

private theorem isCompact_preimage_archEntries [NumberField F]
    (K : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)) (hK : IsCompact K)
    (hKU : K ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsCompact (AutomorphicForm.archEntries F ⁻¹' K) := by
  have hKs : IsCompact (Subtype.val ⁻¹' K :
      Set {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F // IsUnit (Matrix.det (Matrix.of E))}) := by
    refine (IsInducing.subtypeVal.isCompact_preimage_iff ?_).2 hK
    rw [Subtype.range_coe]
    exact hKU
  refine (hKs.image (continuous_sectionGL F)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_archEntries F)) fun g hg => ?_
  refine ⟨⟨AutomorphicForm.archEntries F g, isUnit_det_of_archEntries F g⟩, hg, ?_⟩
  apply Units.ext
  change adeleMatrix F (AutomorphicForm.archEntries F g) = (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
  refine Matrix.ext fun i j => ?_
  simp only [adeleMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingEquiv.coe_toRingHom,
    AutomorphicForm.archEntries_apply, RingEquiv.symm_apply_apply]

end

end EntryPreimage

open scoped Classical in
open AutomorphicForm in

theorem solution
    (F : Type) [Field F] [NumberField F] (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsArchTestFactor F fun g => Φ (archEntries F g) := by
  refine ⟨⟨Φ, hΦ, fun _ => rfl⟩, ?_⟩
  refine (EntryPreimage.isCompact_preimage_archEntries F (tsupport Φ) hc hU).of_isClosed_subset
    (isClosed_tsupport _) ?_
  exact closure_minimal (fun g hg => subset_tsupport Φ hg)
    ((isClosed_tsupport Φ).preimage (EntryPreimage.continuous_archEntries F))

end S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
end P2MW
export P2MW.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det (solution)
