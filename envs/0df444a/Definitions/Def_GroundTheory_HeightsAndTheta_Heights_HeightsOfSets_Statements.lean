-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:38.266866+00:00
-- url     : https://prove2.me/theorems/7edf9e63-18a3-47a9-85fa-678a96f4e280
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
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
open MvPolynomial NumberField
noncomputable section
def HeightLowerBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n)
    (J : Type) [Fintype J] (s : J → IntegralSection P A.deg) (C : ℝ),
    (∀ j, (s j).SupNormLE A C) →
    (∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x) →
    ∀ x ∈ P.points (AlgebraicClosure ℚ), -C ≤ height A x
def HeightMetricChange.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A A' : HermLine n),
    A.deg = A'.deg → ∀ B : ℝ,
    (∀ z ∈ P.points ℂ, |Real.log (A.metric z) - Real.log (A'.metric z)| ≤ B) →
    ∀ x ∈ P.points (AlgebraicClosure ℚ), |height A x - height A' x| ≤ B
def HeightLocalAgreement.Statement : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (n : ι → ℕ)
    (n' : ι' → ℕ) (A : HermLine n) (A' : HermLine n') (x : Cone n (AlgebraicClosure ℚ))
    (x' : Cone n' (AlgebraicClosure ℚ)), BlockNonzero x → BlockNonzero x' →
    ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L] (hx : ∀ k i, x k i ∈ L)
      (hx' : ∀ k i, x' k i ∈ L),
      (∀ v : FinitePlace L, finiteTerm A v (coordIn L x hx) = finiteTerm A' v (coordIn L x' hx')) →
      (∀ σ : L →+* ℂ, A.metric (fun k i ↦ σ (coordIn L x hx k i)) =
        A'.metric (fun k i ↦ σ (coordIn L x' hx' k i))) →
      height A x = height A' x'
def HeightPullback.Statement : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (n' : ι' → ℕ)
    (j : ι → ι') (hj : Function.Injective j) (A : HermLine (n' ∘ j))
    (x : Cone n' (AlgebraicClosure ℚ)), BlockNonzero x →
    height (A.pullback j hj) x = height A (HermLine.project j x)
def HeightComparison.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n),
    ∃ (k : ℕ) (C : ℝ), ∀ x ∈ P.points (AlgebraicClosure ℚ),
      |height A x| ≤ k * height (HermLine.standard n) x + C
def DenseBoundedHeight.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n),
    ∃ (S : Set (Cone n (AlgebraicClosure ℚ))) (C : ℝ), S ⊆ P.points (AlgebraicClosure ℚ) ∧
      P.ZariskiDense S ∧ ∀ x ∈ S, height (HermLine.standard n) x ≤ C
def SlopeMaxExtension.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E' E E'' : HermitianBundle.{0} K),
    HermitianExtension E' E E'' → E.slopeMax ≤ max E'.slopeMax E''.slopeMax
def FlagDegreeBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ)
    (F : Fin (r + 1) → Submodule (𝓞 K) E.carrier), Monotone F → (∀ i, E.Saturated (F i)) →
    (∀ i, E.rank (F i) = i) →
    ∀ i, -((E.normDegree (F i) : ℝ) : EReal) ≥ -(((i : ℕ) : EReal) * E.slopeMax)
section Inhabitants
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
end Inhabitants
end
end GroundTheory.Heights₂.Heights


