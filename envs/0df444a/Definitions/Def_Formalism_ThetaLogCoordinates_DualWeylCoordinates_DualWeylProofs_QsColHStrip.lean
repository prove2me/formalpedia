-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:55.726323+00:00
-- url     : https://prove2.me/theorems/a5675bc7-35d5-4e52-bc0d-f3babdb920c3
-- title:
--   Qs Col HStrip
-- statement:
--   Definitions and structural lemmas for Qs Col HStrip, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
def qs_D (lam kap : Fin n → ℤ) : Finset ℤ :=
  (Finset.Ioc (lam (lastIdx n)) (kap 0)).filter fun c => colH kap c = colH lam c + 1
def qs_mc (lam kap : Fin n → ℤ) : ↥(qs_D lam kap) → Fin n := fun c =>
  ⟨colH lam c.1, by have := (Finset.mem_filter.1 c.2).2; have := colH_le kap c.1; omega⟩
end Formalism.InvariantFactorPaths.ColumnFamilies


