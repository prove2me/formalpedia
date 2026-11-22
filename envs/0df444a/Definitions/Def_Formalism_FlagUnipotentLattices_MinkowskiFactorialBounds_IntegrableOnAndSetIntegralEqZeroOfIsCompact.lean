-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnAndSetIntegralEqZeroOfIsCompact
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnAndSetIntegralEqZeroOfIsCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:53.818454+00:00
-- url     : https://prove2.me/theorems/bf0aa875-3794-4b9f-8edb-7456952d69ae
-- title:
--   Integrable On And Set Integral Eq Zero Of Is Compact
-- statement:
--   Definitions and structural lemmas for Integrable On And Set Integral Eq Zero Of Is Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnAndSetIntegralEqZeroOfIsCompact.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_BlockDistFromLows
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_InterlacingOfBlocksSecondCase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Finset MeasureTheory Filter Topology TensorProduct
set_option linter.all false
noncomputable section
namespace Formalism.HermitianLatticeCounting.P
example (f : Fin 2 → ℝ) (g : ℝ) : (∑ i, f i + g) = (∑ i, f i) + g := rfl
def continuousTestFunctions {X : Type} [TopologicalSpace X] (𝒜 : Set (X → ℂ)) : Set C(X, ℂ) := {a | (a : X → ℂ) ∈ 𝒜}
end Formalism.HermitianLatticeCounting.P


