-- Prove2me | Definitions.Def_BlockBochner_matH
-- name    : BlockBochner_matH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:04.352676+00:00
-- url     : https://prove2.me/theorems/ffa95954-7363-47f3-94bd-18cf7d9ba6e3
-- title:
--   $H=I-D^{-1/2}CD^{-1/2}$
-- statement:
--   With $C$ and $D$ as above,
--   $$H=I-D^{-1/2}CD^{-1/2}.$$
--   Theorem 3 bounds the block spectral gap by $(1-\lambda_{\max}(H))/m$; note $1-\lambda_{\max}(H)=\lambda_{\min}(D^{-1/2}CD^{-1/2})$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4

import Mathlib
import Definitions.Def_BlockBochner_matD
import Definitions.Def_BlockBochner_invSqrt

namespace BlockBochner

/-- **`H = I − D^{−1/2} C D^{−1/2}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4. -/
noncomputable def matH {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (A : Matrix V V ℝ)
    (T : Fin m → Finset V) : Matrix (blockUnion T) (blockUnion T) ℝ :=
  1 - invSqrt (matD A T) * matC A T * invSqrt (matD A T)

end BlockBochner


