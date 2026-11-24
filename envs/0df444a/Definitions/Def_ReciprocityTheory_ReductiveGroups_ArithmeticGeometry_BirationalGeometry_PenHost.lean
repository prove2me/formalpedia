-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenHost
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenHost
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:14.948112+00:00
-- url     : https://prove2.me/theorems/dbf44d13-3def-4de7-902f-67f03ef77f1c
-- title:
--   Pen Host
-- statement:
--   Definitions and structural lemmas for Pen Host, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenHost.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter NumberField
section Host
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
def LiesOver {F : Type*} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ)
    (z : (Σ k, ι k) → ℂ) : Prop :=
  ∀ (d : K → ℕ) (g h : MRing ι) (θ : F), IsMultiHomog g d → IsMultiHomog h d →
    aeval y g = algebraMap F Ω θ * aeval y h →
    eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)
end Host
def ArithmeticHilbertSamuelUpperBoundNumberField : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    IsConjInvariantH A → (∀ sg, 0 < Λ sg) → (∀ sg, Λ (ComplexEmbedding.conjugate sg) = Λ sg) →
    ∑ sg, Real.log (Λ sg) ≤ 0 →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z) →
    limsup (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
end ReciprocityTheory.ChartRestriction.G.Geo


