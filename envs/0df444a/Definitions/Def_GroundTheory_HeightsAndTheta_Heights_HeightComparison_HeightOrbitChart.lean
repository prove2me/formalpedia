-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:43.81521+00:00
-- url     : https://prove2.me/theorems/698a1a0e-d2fc-4cc1-995f-1dd8ea43177c
-- title:
--   Height Orbit Chart
-- statement:
--   Definitions and structural lemmas for Height Orbit Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
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
def chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (p : Coord n) :
    ratioField x :=
  ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x p.1 p.2 (c p.1)⟩
def chartRing (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Subalgebra ℤ (ratioField x) :=
  Algebra.adjoin ℤ (Set.range (chartRatio x c))
def chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] chartRing x c :=
  aeval fun p ↦ ⟨chartRatio x c p, Algebra.subset_adjoin (Set.mem_range_self p)⟩
def chartPoint (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (V : Ideal (MvPolynomial (Coord n) ℤ)) : Ideal (chartRing x c) :=
  Ideal.map (chartEval x c) V
def AbsCentredAt {L : Type*} [Field L] (O : Subalgebra ℤ L) (m : Ideal O) (φ : L → ℝ) : Prop :=
  (∀ u : O, φ u ≤ 1) ∧ ∀ u : O, φ u < 1 ↔ u ∈ m
def localQuotLength {O : Type*} [CommRing O] (m : Ideal O) [m.IsPrime] (f : O) : ℕ :=
  (Module.length (Localization.AtPrime m)
    (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f})).toNat
example : ((chartEval samplePoint (fun _ ↦ 0) (X ⟨(), 1⟩) : ratioField samplePoint) :
    AlgebraicClosure ℚ) = 2 := by
  simp [chartEval, chartRatio, samplePoint]
open Classical in

example {L : Type*} [Field L] (O : Subalgebra ℤ L) :
    AbsCentredAt O ⊥ fun t ↦ if t = 0 then 0 else 1 := by
  refine ⟨fun u ↦ by dsimp only; split_ifs <;> norm_num, fun u ↦ ?_⟩
  rw [Ideal.mem_bot]
  constructor
  · intro h
    dsimp only at h
    split_ifs at h with h0
    · exact Subtype.ext h0
    · exact absurd h (lt_irrefl 1)
  · rintro rfl
    simp
end
end GroundTheory.Heights₂.Heights


