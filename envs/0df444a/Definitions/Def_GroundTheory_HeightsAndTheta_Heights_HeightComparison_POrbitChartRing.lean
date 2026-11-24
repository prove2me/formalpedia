-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartRing
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:21.358175+00:00
-- url     : https://prove2.me/theorems/6f8787a1-e6ad-44ef-af8f-a331cd2721f6
-- title:
--   POrbit Chart Ring
-- statement:
--   Definitions and structural lemmas for POrbit Chart Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
theorem mem_closure_chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (z : ratioField x) :
    z ∈ Subfield.closure (Set.range (chartRatio x c)) := by
  set T := Subfield.closure (Set.range (chartRatio x c))
  let T' : Subfield (AlgebraicClosure ℚ) := T.map (ratioField x).val.toRingHom
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    T'.toIntermediateField fun q ↦ by
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem T' q
  have hE : ratioField x ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    refine ⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩,
      div_mem (Subfield.subset_closure (Set.mem_range_self _))
        (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩
    simp [chartRatio, div_div_div_cancel_right₀ (hc k)]
  obtain ⟨t, ht, hzt⟩ := hE z.2
  have : t = z := Subtype.ext hzt
  exact this ▸ ht
theorem OrbitChartRing.proof : OrbitChartRing.Statement := by
  intro ι _ _ n x c hc
  refine ⟨(Subalgebra.fg_iff_finiteType _).mp
    ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_
    exact Subtype.ext h
  · have hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring :=
      Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)
    by_cases hb0 : b = 0
    · refine ⟨(0, 1), ?_⟩
      rw [hb0, div_zero] at hab
      simp [← hab]
    · have hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      refine ⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      change z * b = a
      rw [← hab, div_mul_cancel₀ _ hb0]
  · rw [Subtype.val_injective h]
example : Algebra.FiniteType ℤ (chartRing samplePoint (fun _ ↦ 0)) ∧
    IsFractionRing (chartRing samplePoint (fun _ ↦ 0)) (ratioField samplePoint) :=
  OrbitChartRing.proof Unit _ samplePoint _ fun _ ↦ by simp [samplePoint]
end
end GroundTheory.Heights₂.Heights


