-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MoriwakiSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_MoriwakiSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:51.031542+00:00
-- url     : https://prove2.me/theorems/4a3a99b2-2fcb-4442-8f15-042bcb785e65
-- title:
--   Moriwaki St
-- statement:
--   Definitions and structural lemmas for Moriwaki St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/MoriwakiSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenHost
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def NefOnGeneric (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W A 1
def HeightsNonneg (II : IntersectionSystem) (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A]
def MoriwakiHSStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    HeightsNonneg II (mCoordIdeal y) A →
    Tendsto (fun n : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n /
        ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop
      (𝓝 (II K ι (mCoordIdeal y) (D + 1) fun _ => A))
def MoriwakiBigStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    NefOnFibres (mCoordIdeal y) A.a → NefOnGeneric (mCoordIdeal y) A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


