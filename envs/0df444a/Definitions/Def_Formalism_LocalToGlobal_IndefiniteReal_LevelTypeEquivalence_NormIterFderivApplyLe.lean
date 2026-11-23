-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:32.610968+00:00
-- url     : https://prove2.me/theorems/fed6d5ae-966d-4524-b4f2-2be3735b2c3d
-- title:
--   Norm Iter Fderiv Apply Le
-- statement:
--   Definitions and structural lemmas for Norm Iter Fderiv Apply Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/NormIterFderivApplyLe.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
section MD
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
noncomputable def md (φ : V → ℂ) : (n : ℕ) → (Fin n → V) → ℝ → V → ℂ
  | 0, _, _, a => φ a
  | n + 1, v, h, a => (md φ n (Fin.tail v) h (a + h • v 0) - md φ n (Fin.tail v) h a) / h
end MD
section MD2
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
end MD2
section MD3
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
end MD3
end Formalism.IndefR.Eqv


