-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:33.59313+00:00
-- url     : https://prove2.me/theorems/d830bb6f-a55a-45f7-b032-5b4199277a0e
-- title:
--   Statements Flag Bundle Section Div
-- statement:
--   Definitions and structural lemmas for Statements Flag Bundle Section Div, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsFlagBundleSectionDiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open Classical in

def FlagBundleSectionDiv.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N, 1 ≤ (i : ℕ) →
    ∀ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
      IsMultiHomog f bf → IsMultiHomog g bg →
      (fun o => (bf o : ℤ) - bg o) = zetaDeg + liftDeg (b i - a) →
      g ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) →
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g →
      ∀ W : Ideal (MRing (bundleIdx ι M) F),
        ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
          if W = projIdeal F y w φ (truncCoord t i) then 1 else 0
abbrev lineGenT : Fin 2 → FractionRing (MvPolynomial (Fin 2) LineFieldTwoElement) :=
  fun j => algebraMap (MvPolynomial (Fin 2) LineFieldTwoElement) (FractionRing (MvPolynomial (Fin 2) LineFieldTwoElement))
    (X j)
end
end GroundTheory.Heights₂.Heights.NumbersDVR


