-- Prove2me | Definitions.Def_ZOGlobalLB_Supplement_transcriptPrefix
-- name    : ZOGlobalLB_Supplement_transcriptPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:49:24.063366+00:00
-- url     : https://prove2.me/theorems/d7bed11a-512e-4199-b592-ee35a617d921
-- title:
--   Response history before an adaptive query round
-- statement:
--   For a finite response transcript $(Y_1,\ldots,Y_n)$, the prefix before round $i$ is the list of responses from all earlier rounds. It is the realized history held fixed when the conditional likelihood at round $i$ is differentiated in Theorem A.4.
--
--   **Formalization Note** Rounds are zero-based, so the prefix at `i : Fin n` is indexed by `Fin i.val`.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem A.4, pp.34-35

import Mathlib

namespace ZOGlobalLB

namespace Supplement

/-- The realized response history strictly before round `i` of a finite transcript.
This is the zero-based Lean encoding of `T_{i-1}` in Xia--Yuan,
arXiv:2610.19652, Theorem A.4, pp.34--35. -/
def transcriptPrefix {n : ℕ} {Ω : Type*} (Y : Ω → Fin n → ℝ) (i : Fin n) (ω : Ω) :
    Fin i.val → ℝ :=
  fun j => Y ω ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

end Supplement

end ZOGlobalLB


