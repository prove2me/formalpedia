-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeComplexBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:32.378852+00:00
-- url     : https://prove2.me/theorems/aafa17ff-ff1b-4beb-86d7-85823ba3abf8
-- title:
--   Statements Cone Complex Base Change
-- statement:
--   Definitions and structural lemmas for Statements Cone Complex Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsConeComplexBaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsConeBranchLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def ConeComplexBaseChange.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (W' : Ideal (MRing ι)) (Wa : Ideal (MRingOver ℂ ι)),
    IsArithVar P (n + 2) → s ∉ P → W' ∈ divSupp P s → IsHorizontal W' →
    Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
      (P.map (MvPolynomial.map (Int.castRingHom ℂ))).IsRadical ∧
      (∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
        ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((n + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ∧
          MvPolynomial.map (Int.castRingHom ℂ) s ∉ Q) ∧
      Wa ∈ ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Targets


