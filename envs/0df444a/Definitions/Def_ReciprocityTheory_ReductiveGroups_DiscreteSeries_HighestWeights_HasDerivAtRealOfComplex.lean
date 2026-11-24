-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HasDerivAtRealOfComplex
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:35:17.166614+00:00
-- url     : https://prove2.me/theorems/683ceee1-7b58-40c2-9d6a-0048d03d3357
-- title:
--   Has Deriv At Real Of Complex
-- statement:
--   Definitions and structural lemmas for Has Deriv At Real Of Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/HasDerivAtRealOfComplex.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OpEqExp
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
def kunits {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : Fin n → Fin n → Module.End ℂ T.V :=
  fun a b => ((T.dτ (Matrix.single a b 1) : T.V →L[ℂ] T.V) : Module.End ℂ T.V)
section MatDeriv
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end MatDeriv
def kp1 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.single a b 1 - Matrix.single b a 1)
def kp2 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (Matrix.single a b 1 + Matrix.single b a 1)
end ReciprocityTheory.ChartRestriction.DS.HW


