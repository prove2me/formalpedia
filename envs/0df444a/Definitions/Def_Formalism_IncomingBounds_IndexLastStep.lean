-- Prove2me | Definitions.Def_Formalism_IncomingBounds_IndexLastStep
-- name    : Formalism_IncomingBounds_IndexLastStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:38:43.472902+00:00
-- url     : https://prove2.me/theorems/43aebd66-7e3a-45c7-b159-769b57461267
-- title:
--   Index Last Step
-- statement:
--   Definitions and structural lemmas for Index Last Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/IndexLastStep.lean

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.IncomingBounds
open Module
def IndexLastStep : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℤ) (M Θ : Submodule O X), Formalism.LatticeIndexTer.IsLat O K X M → Formalism.LatticeIndexTer.IsLat O K X Θ →
      ∀ W : Submodule K X,
        Formalism.LatticeIndexTer.idx O X (M ⊓ W.restrictScalars O) (Θ ⊓ W.restrictScalars O) ≤
          e * (finrank K W : ℤ) +
            ((Formalism.LatticeIndexTer.qlen O X
              (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O) ⊔ Θ)
              Θ).toNat : ℤ)
end Formalism.IncomingBounds


