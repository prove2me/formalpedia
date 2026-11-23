-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StIntegralFormCovolume
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StIntegralFormCovolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:24.644324+00:00
-- url     : https://prove2.me/theorems/dba09532-d818-48dc-af2b-2a4753b1a13b
-- title:
--   St Integral Form Covolume
-- statement:
--   Definitions and structural lemmas for St Integral Form Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StIntegralFormCovolume.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory
noncomputable section
variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]
def IntegralFormCovolume.Statement : Prop :=
  ∀ (ψ : Q →+ V) (e : Basis K ℚ Q) (T : LinearMap.BilinForm ℚ Q) (μ : Measure V),
    μ.IsAddHaarMeasure → T.Nondegenerate → LinearIndependent ℝ (fun k => ψ (e k)) →
    finrank ℝ V = Fintype.card K →
    ∃ C : ℝ, ∀ (L : AddSubgroup Q) (k : ℤ), k ≠ 0 → L.FG → Submodule.span ℚ (L : Set Q) = ⊤ →
      (∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, T x y = n) →
      (∀ y : Q, (∀ x ∈ L, ∃ n : ℤ, T y x = n) → k • y ∈ L) →
      ∃ _ : DiscreteTopology (AddSubgroup.toIntSubmodule (L.map ψ)),
        IsZLattice ℝ (AddSubgroup.toIntSubmodule (L.map ψ)) ∧
        ZLattice.covolume (AddSubgroup.toIntSubmodule (L.map ψ)) μ ^ 2 ≤
          C * |(k : ℝ)| ^ Fintype.card K
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


