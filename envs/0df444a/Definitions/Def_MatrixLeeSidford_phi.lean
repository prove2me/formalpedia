-- Prove2me | Definitions.Def_MatrixLeeSidford_phi
-- name    : MatrixLeeSidford_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:41.514497+00:00
-- url     : https://prove2.me/theorems/00a1ec95-5022-4f9b-b13c-8ad8df35075f
-- title:
--   Potential as a function of the slack, $\varphi(S)$
-- statement:
--   For a positive definite slack matrix $S$ and an integer $s\ge2$,
--   $$
--   \varphi(S)=\frac12\min_{G\succ0} f_S(G),
--   $$
--   where $f_S$ is the Lewis-weight objective built from $S^{-1/2}A_iS^{-1/2}$. Then $\Phi_p(y)=\varphi(S(y))$.
--
--   **Formalization Note** The minimum is written as an infimum over the positive definite $m\times m$ matrices (Lean's real infimum is $0$ on a set unbounded below); that it is attained at a unique point is a theorem (Lemma 4.4), not part of the definition.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Section 5.1, p.37; Eq. (4.6), p.34

import Mathlib
import Definitions.Def_MatrixLeeSidford_fObj

open Matrix

namespace MatrixLeeSidford

/-- The potential as a function of the slack, `φ(S) := ½ min_{G ≻ 0} f_S(G)` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Section 5.1,
p.37; Definition 4.3, Eq. (4.6), p.34).

**Formalization Note** The minimum is written as an infimum `⨅` over the positive definite
`m × m` matrices; Lean's real `⨅` is `0` on a set that is unbounded below. Attainment and
uniqueness of the minimizer are theorems of the mission (Lemma 4.4, Theorem 2.1(a)), not part of
the definition. -/
noncomputable def phi {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ⨅ G : {G : Matrix (Fin m) (Fin m) ℝ // G.PosDef}, fObj A S s G.1

end MatrixLeeSidford


