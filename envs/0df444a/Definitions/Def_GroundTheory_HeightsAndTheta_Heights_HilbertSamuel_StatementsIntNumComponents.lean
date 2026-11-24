-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIntNumComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIntNumComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:01.486275+00:00
-- url     : https://prove2.me/theorems/6c1e2323-b997-4db0-a07e-a7815c09eee3
-- title:
--   Statements Int Num Components
-- statement:
--   Definitions and structural lemmas for Statements Int Num Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsIntNumComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def IntNumComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (a : Fin e → K → ℤ) (S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ))),
    IsArithVar P (e + 1) →
    (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) →
    NumbersDVR.intNum ℂ (⨅ W ∈ S, W) a = ∑ W ∈ S, NumbersDVR.intNum ℂ W a
section Inhabitants
open GroundTheory.Heights₂.Heights.Inter
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


