-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudyUnique
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudyUnique
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:56:54.553641+00:00
-- url     : https://prove2.me/theorems/d683b4c5-c40d-4990-971d-16b69335bab0
-- title:
--   Fubini Study Unique
-- statement:
--   Definitions and structural lemmas for Fubini Study Unique, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudyUnique.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Instances.Matrix
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Matrix
open scoped LinearAlgebra.Projectivization
namespace Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
instance instContinuousSMul_projectivization :
    ContinuousSMul (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) where
  continuous_smul := by
    -- Open-quotient structure: id × mk' is an open quotient on G × V₀.
    rw [← (IsOpenQuotientMap.id.prodMap
            Projectivization.isOpenQuotientMap_mk').continuous_comp_iff]
    -- After the rewrite, the goal is:
    --   Continuous (fun (Uv : G × {v // v ≠ 0}) =>
    --     Uv.1 • Projectivization.mk' ℂ Uv.2)
    -- which by definitional unfolding (compHom action + mapEquiv +
    -- Projectivization.map_mk) equals
    --   Continuous (fun Uv => mk' ⟨(toEuclideanLin Uv.1.val) Uv.2.1, ...⟩).
    -- Compose continuous_mk' with subtype_mk on the matrix-vector-mul
    -- composition (which is jointly continuous in (M, v)).
    refine Projectivization.continuous_mk'.comp ?_
    refine Continuous.subtype_mk ?_ _
    -- Goal: Continuous (fun (Uv : G × {v // v ≠ 0}) =>
    --   (toEuclideanLin Uv.1.val) Uv.2.1)
    -- This is the WithLp.toLp ∘ (M *ᵥ ofLp) composition.
    show Continuous (fun (Uv : Matrix.unitaryGroup ι ℂ
                          × {v : EuclideanSpace ℂ ι // v ≠ 0}) =>
        WithLp.toLp 2 ((Uv.1.val : Matrix ι ι ℂ)
            *ᵥ (Uv.2.val.ofLp : ι → ℂ)))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · -- Continuous (fun Uv => Uv.1.val) — subtype_val ∘ fst
      exact continuous_subtype_val.comp continuous_fst
    · -- Continuous (fun Uv => Uv.2.val.ofLp) — ofLp ∘ subtype_val ∘ snd
      exact (PiLp.continuous_ofLp _ _).comp
              (continuous_subtype_val.comp continuous_snd)
instance instIsMulRightInvariantUnitaryHaarProb (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasureTheory.Measure.IsMulRightInvariant
      (unitaryHaarProb : MeasureTheory.Measure (Matrix.unitaryGroup ι ℂ)) where
  map_mul_right_eq_self g := by
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.map (· * g)
          (unitaryHaarProb : MeasureTheory.Measure
            (Matrix.unitaryGroup ι ℂ))) :=
      MeasureTheory.Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
end Matrix.UnitaryGroup


