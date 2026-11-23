-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_FiberCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:28.535987+00:00
-- url     : https://prove2.me/theorems/645891c1-2a23-43c8-988b-cb26cd7d3c2a
-- title:
--   Fiber Card
-- statement:
--   Definitions and structural lemmas for Fiber Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/FiberCard.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.DensSplitW
def FiberCard : Prop :=
  ∀ (K V U : Type) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U), Function.Surjective φ →
    ∀ (k : ℕ) (g : Fin k → U),
      Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
        Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
            Module.finrank K (LinearMap.ker φ)) *
          ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
            (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i)
end PI.DensSplitW


