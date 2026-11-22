-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:55.520061+00:00
-- url     : https://prove2.me/theorems/2db91d0c-3c93-49bc-94c7-3b72c3c6400e
-- title:
--   Level Decomp
-- statement:
--   Definitions and structural lemmas for Level Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelDecomp.lean

import Definitions.Def_Formalism_MahlerMeasure_LevelDecompR
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}
end
section fockSec
open Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end fockSec
section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}
end
section fockSec
open Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} {w e : Fin r → σ}
end fockSec
end Formalism.GM


