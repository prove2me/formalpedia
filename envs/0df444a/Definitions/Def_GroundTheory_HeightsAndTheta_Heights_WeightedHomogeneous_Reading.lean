-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:41.689533+00:00
-- url     : https://prove2.me/theorems/464ee18d-3262-4b3c-a0fe-50ab5e21f526
-- title:
--   Reading
-- statement:
--   Definitions and structural lemmas for Reading, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def HermLine.ConjInvariant (A : HermLine n) : Prop :=
  ∀ z : Cone n ℂ, BlockNonzero z → A.metric (fun k i ↦ starRingEnd ℂ (z k i)) = A.metric z
def HermLine.ofGeo (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N) : HermLine n where
  deg := N.a
  metric z := N.h (flatCone z)
  metric_pos z hz := N.pos _ ((blockNonzero_unflatCone_iff _).mp hz)
  metric_smul c z hc _ := N.smul c (flatCone z) hc
  metric_smooth := by
    have hu : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ flatCone z) :=
      contDiff_pi.2 fun p ↦ ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n p.1 + 1) ↦ ℂ) p.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) p.1)).contDiff
    exact hN.comp hu.contDiffOn fun z hz ↦ (blockNonzero_unflatCone_iff _).mp hz
namespace ArithVariety
variable (P : ArithVariety n)
def IsSmallFor (A : HermLine n) (t : P.FunField) : Prop :=
  ∀ (p q : MvPolynomial (Coord n) ℤ) (δp δq : ι → ℕ), IsWeightedHomogeneous (coordDeg n) p δp →
    IsWeightedHomogeneous (coordDeg n) q δq → (∀ k, (δp k : ℤ) = δq k + A.deg k) →
    P.mkF p = t * P.mkF q → ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ ‖evalCone z q‖ * A.metric z
structure IsNormalSection (a : ι → ℤ) (t : P.FunField) : Prop where
  degree : P.IsOfDegree a t
  integral : ∀ c, P.IsLive c → t / P.chartPow c a ∈ integralClosure (P.chartRing c) P.FunField
def Reads {Ω : Type} [Field Ω] (y : Coord n → Ω) (a : ι → ℤ) (s : Ω) (t : P.FunField) : Prop :=
  ∀ (g h : MvPolynomial (Coord n) ℤ) (δg δh : ι → ℕ), IsWeightedHomogeneous (coordDeg n) g δg →
    IsWeightedHomogeneous (coordDeg n) h δh → (∀ k, (δg k : ℤ) = δh k + a k) →
    (aeval y g = s * aeval y h ↔ P.mkF g = t * P.mkF h)
end ArithVariety
namespace AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
def plusCoord {Ω : Type} (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) : Coord D.extSizes → Ω
  | ⟨none, j⟩ => x' j
  | ⟨some k, i⟩ => y ⟨k, i⟩
def oldFlat {F : Type*} (w : Coord D.extSizes → F) : Coord n → F := fun p ↦ w ⟨some p.1, p.2⟩
structure BlockReading {Ω : Type} [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) : Prop where
  ideal_eq : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y
  ext_eq : D.extIdeal = Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')
  reads : ∀ j, P.Reads y D.deg (x' j) (D.elt j)
def InducesMetric {Ω : Type} [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω)
    (N : Geo.HermLine (blockIdx n)) (Ap : Geo.HermLine (blockIdx D.extSizes)) : Prop :=
  ∀ (j : Fin (D.size + 1)) (g m : MvPolynomial (Coord n) ℤ) (dg dm : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) g dg → Geo.IsMultiHomog (ι := blockIdx n) m dm →
    (∀ k, (dg k : ℤ) = dm k + N.a k) → aeval y g = aeval y m * x' j →
    ∀ z ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')),
      ‖z ⟨none, j⟩‖ * ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) m)‖ * N.h (D.oldFlat z) =
        ‖eval (D.oldFlat z) (map (Int.castRingHom ℂ) g)‖ * Ap.h z
end AddBlockData
def IsSupSmallBlock {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    (y : Coord n' → Ω) (k₀ : κ) (A : Geo.HermLine (blockIdx n')) (τ : ℕ) (s : Ω) : Prop :=
  ∀ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f (Pi.single k₀ τ) →
    aeval y f = s → ∀ z ∈ Geo.mcPts (ι := blockIdx n') (Geo.mCoordIdeal (ι := blockIdx n') y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤ A.h z ^ τ
def monomialValues {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) : Set Ω :=
  {s | ∃ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧ s = ∏ p, y p ^ μ p}
section Examples
variable (n)
def wholePoint : Coord n → (ArithVariety.whole n).FunField := fun v ↦ (ArithVariety.whole n).mkF (X v)
def unitPoint : Coord (fun _ : Unit ↦ 0) → ℚ := fun _ ↦ 1
end Examples
end
end GroundTheory.Heights₂.Heights


