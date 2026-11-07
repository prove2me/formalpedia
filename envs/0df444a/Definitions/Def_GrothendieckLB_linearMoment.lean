-- Prove2me | Definitions.Def_GrothendieckLB_linearMoment
-- name    : GrothendieckLB_linearMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:15.583195+00:00
-- url     : https://prove2.me/theorems/50d4abcd-3b8f-4a56-81f4-69aa5a4d791a
-- title:
--   First moment $\mathbb E[F(X)X_i]$
-- statement:
--   For $F:\mathbb R^d\to\mathbb R$ and a coordinate $i$, this is $\mathbb E[F(X)X_i]$, the $i$-th entry of the vector $c_F=\mathbb E[F(X)X]\in\mathbb R^d$. It is the coefficient of $F$ on the degree-one Hermite $X_i$, so that $P_1F=\langle c_F,X\rangle$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_gaussExp

namespace GrothendieckLB

/-- The first-moment coordinate `E[F(X) X_i]`, the `i`-th entry of `c_F = E[F(X)X]`
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31). -/
noncomputable def linearMoment {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) : ℝ :=
  gaussExp fun x => F x * x i

end GrothendieckLB


