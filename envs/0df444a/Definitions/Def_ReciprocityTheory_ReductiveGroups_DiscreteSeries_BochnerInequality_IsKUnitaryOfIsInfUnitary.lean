-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:36:01.530304+00:00
-- url     : https://prove2.me/theorems/035fa9f1-f35b-48de-913e-52bd90a74a30
-- title:
--   Is KUnitary Of Is Inf Unitary
-- statement:
--   Definitions and structural lemmas for Is KUnitary Of Is Inf Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section KUnit
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
def IsKUnitary (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ x y : X, inner ℂ (A a b x) y = inner ℂ x (A b a y)
def kUnitNatB (a b : Fin 2) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  LinearMap.smulRight (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).toLinearMap
    (EuclideanSpace.single a 1)
def kUnitWtLin (μ : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) * μ c
end KUnit
end ReciprocityTheory.ChartRestriction.DS


