-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:22.662571+00:00
-- url     : https://prove2.me/theorems/aeeb05d3-b6ea-4f32-8d4b-dd837d96b2c2
-- title:
--   Mirabolic
-- statement:
--   Definitions and structural lemmas for Mirabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/Mirabolic.lean

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
def pairU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + t • vecMulVec (fun a => h a l.castSucc) (Pi.single s.succ 1)
def pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + t • vecMulVec (Pi.single l.castSucc 1) (fun b => h s.succ b)
end Formalism.EigenvalueLevelCeiling


