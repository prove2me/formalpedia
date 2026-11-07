-- Prove2me | Definitions.Def_KServerConj_IsRun
-- name    : KServerConj_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:36.300645+00:00
-- url     : https://prove2.me/theorems/f8156490-ca0a-41d8-b946-c5c4488218fc
-- title:
--   A run of the algebraic update: initialization (7), normalization, row replacement (12)
-- statement:
--   Let $k=m+1$, let $C_0=\{s_1,\dots,s_k\}$, and let $r_1,\dots,r_T$ be requests. A **run** is a sequence of column families $q^{(0)},q^{(1)},\dots,q^{(T)}$ (with normalized families $\tilde q^{(t)}$) such that
--
--   1. $q^{(0)}$ is the initial family (7);
--   2. for each $1\le t\le T$ there is a $k\times k$ matrix $B$ with $\det B=1$ and $Bq^{(t-1)}_{r_t}=e_1$ (Lemma 2.2), and $\tilde q^{(t)}_x=Bq^{(t-1)}_x$ for every point $x$;
--   3. $q^{(t)}$ is obtained from $\tilde q^{(t)}$ by the row replacement (12) with the fresh row $\delta_x=\xi_{t,x}z^{d(r_t,x)}$ (11).
--
--   This is the paper's procedure: "the initialization (7) and the determinant-preserving normalization followed by (12)". The potential at time $t$ is $\Psi_t=\mu(Q)$ for the family $q^{(t)}$.
--
--   **Formalization Note** Every normalizing matrix with these two properties is allowed; the paper's matrix from Gaussian elimination is one. Since $\det B=1$, no $k$-column determinant depends on the choice.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.2–2.3 and Theorem 2.4, pp.6–8 (pdf pp.7–9)

import Mathlib
import Definitions.Def_KServerConj_initCols
import Definitions.Def_KServerConj_rowReplace

namespace KServerConj

/-- **A run of the algebraic update**, Coester, Koutsoupias, Zbysiński, *The k-server conjecture is
true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §2.2–2.3 and Theorem 2.4,
printed pp.6–8 (PDF pp.7–9): "the initialization (7) and the determinant-preserving normalization
followed by (12)".

`IsRun s r T q qn` says:
1. `q 0` is the initial family of columns (7) for the initial servers `s`;
2. for each request `1 ≤ t ≤ T`, there is a matrix `B` with `det B = 1` and `B q_{r_t} = e₁`
   (Lemma 2.2), and `qn t x = B (q (t-1) x)` for every point `x` (the normalized columns, which the
   paper continues to call `q_x`);
3. `q t` is obtained from `qn t` by replacing the first coordinate of every column by
   `δ_x = ξ_{t,x} z^{d(r_t, x)}` (11)–(12).

**Formalization Note.** Here `k = m + 1`, with first coordinate `0 : Fin (m+1)` and
`e₁ = Pi.single 0 1`. Every matrix `B` with these two properties is allowed: the paper's `B` (from
Gaussian elimination) is one of them, and no `k`-column determinant depends on the choice, since
`det B = 1`. The potential at time `t` is computed from `q t`; `qn t` is the state "before
processing the request" in the coordinates where `q_{r_t} = e₁`. -/
def IsRun {m : ℕ} {M : Type*} [PseudoMetricSpace M] (s : Fin (m + 1) → M) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (m + 1) → K (m + 1) M) : Prop :=
  q 0 = initCols s ∧ ∀ t, 1 ≤ t → t ≤ T →
    (∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) (K (m + 1) M), B.det = 1 ∧
      B.mulVec (q (t - 1) (r t)) = Pi.single 0 1 ∧ ∀ x, qn t x = B.mulVec (q (t - 1) x)) ∧
    q t = rowReplace (qn t) (freshRow r t)

end KServerConj


