-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:56:33.126838+00:00
-- url     : https://prove2.me/theorems/a6066281-78ba-46de-a99c-b6228e7747ef
-- title:
--   Fubini Study
-- statement:
--   Definitions and structural lemmas for Fubini Study, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudy.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
public import Mathlib.Topology.Instances.Matrix
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
namespace Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma toEuclideanLin_apply_continuous (v : EuclideanSpace ℂ ι) :
    Continuous (fun M : Matrix ι ι ℂ => (Matrix.toEuclideanLin M) v) := by
  show Continuous (fun M : Matrix ι ι ℂ =>
      (WithLp.toLp 2 (M *ᵥ (WithLp.ofLp v))
        : EuclideanSpace ℂ ι))
  refine (PiLp.continuous_toLp _ _).comp ?_
  exact Continuous.matrix_mulVec continuous_id continuous_const
lemma toEuclideanLin_unitary_apply_ne_zero
    (U : Matrix.unitaryGroup ι ℂ)
    {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  apply hv
  exact (toEuclideanLinearEquiv U).injective (h.trans (LinearEquiv.map_zero _).symm)
noncomputable def orbitMap (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    Matrix.unitaryGroup ι ℂ → ℙ ℂ (EuclideanSpace ℂ ι) :=
  fun U => U • p₀
lemma orbit_map_continuous (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    Continuous (orbitMap p) := by
  -- Rewrite the orbit map as Projectivization.mk' of the matrix action on p.rep.
  have h_eq : orbitMap p = fun U : Matrix.unitaryGroup ι ℂ =>
      Projectivization.mk' ℂ
        ⟨(Matrix.toEuclideanLin U.val) p.rep,
         toEuclideanLin_unitary_apply_ne_zero U p.rep_nonzero⟩ := by
    funext U
    show U • p = _
    conv_lhs => rw [← p.mk_rep]
    rfl
  rw [h_eq]
  refine Projectivization.continuous_mk'.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact (toEuclideanLin_apply_continuous p.rep).comp continuous_subtype_val
lemma orbit_map_measurable (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    Measurable (orbitMap p) :=
  (orbit_map_continuous p).measurable
noncomputable def fsMeasure (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    Measure (ℙ ℂ (EuclideanSpace ℂ ι)) :=
  Measure.map (orbitMap p₀) unitaryHaarProb
instance instIsProbabilityMeasureFsMeasure
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    IsProbabilityMeasure (fsMeasure p₀) := by
  unfold fsMeasure
  exact Measure.isProbabilityMeasure_map (orbit_map_measurable p₀).aemeasurable
end Matrix.UnitaryGroup


