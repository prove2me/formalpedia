-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenHSRes
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenHSRes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:08.538868+00:00
-- url     : https://prove2.me/theorems/2805dd36-358b-49f8-8711-ab31b2681083
-- title:
--   Pen HSRes
-- statement:
--   Definitions and structural lemmas for Pen HSRes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenHSRes.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
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
open MvPolynomial Filter
def HeightBoundResolution : Prop :=
  ResExistsStatement → ResBridgeStatement → ∀ (ι0 : Type) [Fintype ι0] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (x : ι0 → Ω) (D : ℕ)
    (A : HermLine (fun _ : Unit => ι0))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → A.a = 1 →
    IsArithVar (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (D + 1) →
    Birational (fun p : Σ _ : Unit, ι0 => x p.2) →
    IsSemipositiveH (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) A → IsConjInvariantH A →
    II Unit (fun _ => ι0) (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (D + 1) (fun _ => A) ≤
      liminf (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (fun p => x p.2) A)
          (fun τ => secM (fun p : Σ _ : Unit, ι0 => x p.2) (fun _ => τ)) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop
def SuccessiveMinimaResolution : Prop :=
  ResExistsStatement → ResBridgeStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι)
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSemipositiveH (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D
end ReciprocityTheory.ChartRestriction.G.Geo


