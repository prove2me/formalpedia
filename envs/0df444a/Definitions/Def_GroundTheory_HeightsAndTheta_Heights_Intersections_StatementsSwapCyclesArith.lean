-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:30.196707+00:00
-- url     : https://prove2.me/theorems/f0c0b351-c14b-43ef-9c85-cd5b9ca96812
-- title:
--   Statements Swap Cycles Arith
-- statement:
--   Definitions and structural lemmas for Statements Swap Cycles Arith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSwapCyclesArith.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def SwapCyclesArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    (∀ U : Ideal (MRing ι), IsRelevant U → U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes →
      ringKrullDim (MRing ι ⧸ U) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) ∧
      (U.map (Ideal.Quotient.mk P)).IsPrime ∧
      ∀ [(U.map (Ideal.Quotient.mk P)).IsPrime],
        ringKrullDim (Localization.AtPrime (U.map (Ideal.Quotient.mk P))) = 2) ∧
    (∀ W ∈ divSupp P s, ∀ U ∈ divSupp W s',
      U ∈ (P ⊔ Ideal.span {s} ⊔ Ideal.span {s'}).minimalPrimes) ∧
    ((divCycle P s).sum (fun W m => m • divCycle W s') =
      (divCycle P s').sum (fun W m => m • divCycle W s)) ∧
    ((divCycle P s).sum (fun W m => m • horCycle W s') =
      (divCycle P s').sum (fun W m => m • horCycle W s)) ∧
    ((divCycle P s).sum (fun W m => m • vertCycle W s') =
      (divCycle P s').sum (fun W m => m • vertCycle W s))
end
end GroundTheory.Heights₂.Heights.Inter


