-- Prove2me | Definitions.Def_CandesTao_Shared_StrongIncoherence
-- name    : CandesTao_Shared_StrongIncoherence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:40:48.709263+00:00
-- url     : https://prove2.me/theorems/b48d1cbd-b7df-4a42-9c75-1e901c135435
-- title:
--   Strong incoherence property with parameter μ (A1–A2, Eqs. (I.8a), (I.8b), (I.9))
-- statement:
--   Let $M \in \mathbb{R}^{n_1\times n_2}$ have a rank-$r$ singular value decomposition
--   $$M = \sum_{k=1}^r \sigma_k u_k v_k^*,$$
--   with $\sigma_k > 0$ and orthonormal families $u_1,\dots,u_r \in \mathbb{R}^{n_1}$ and $v_1,\dots,v_r \in \mathbb{R}^{n_2}$. Write $P_U = \sum_k u_k u_k^*$ and $P_V = \sum_k v_k v_k^*$ for the orthogonal projections onto the column and row spaces, and $E = \sum_k u_k v_k^*$ for the sign matrix.
--
--   The matrix obeys the **strong incoherence property with parameter** $\mu > 0$ if
--
--   1. (I.8a) for all $a, a' \in [n_1]$,
--   $$\Bigl|\langle e_a, P_U e_{a'}\rangle - \frac{r}{n_1}1_{a=a'}\Bigr| \le \mu\frac{\sqrt r}{n_1};$$
--   2. (I.8b) for all $b, b' \in [n_2]$,
--   $$\Bigl|\langle e_b, P_V e_{b'}\rangle - \frac{r}{n_2}1_{b=b'}\Bigr| \le \mu\frac{\sqrt r}{n_2};$$
--   3. (I.9) for all $(a,b) \in [n_1]\times[n_2]$,
--   $$|E_{ab}| \le \mu \frac{\sqrt r}{\sqrt{n_1 n_2}}.$$
--
--   Here $\langle e_a, P_U e_{a'}\rangle = \sum_k u_k(a)u_k(a')$. The property says that the singular vectors are spread out: the projections $P_U, P_V$ are entrywise close to the scalar multiples $(r/n)I$, and the sign matrix has no large entry. It is the hypothesis of both main theorems of Candès and Tao. For $r \ge 1$ it forces $\mu \ge 1$, since $r = \sum_{a,b}|E_{ab}|^2 \le \mu^2 r$.
--
--   Used by two missions of this paper, both from the definition on p. 2055: 01-completion-i (Theorem 1.1, p. 2055; Theorem 3.4, Moment Bound I, and Corollary 3.5, p. 2063) and 02-completion-ii (Theorem 1.2, p. 2055; Theorem 3.6, Moment Bound II, and Corollary 3.7, p. 2063).
--
--   **Formalization Note** The paper introduces two parameters $\mu_1, \mu_2 > 0$ (A1, A2) and says the property holds with parameter $\mu$ when both can be taken $\le \mu$; this is equivalent to the three bounds above with $\mu$ itself and $\mu > 0$. Condition (I.9) reuses the platform predicate `A1` of `matrix_completion_svd`, whose bound $\mu\sqrt{r/(n_1 n_2)}$ equals $\mu\sqrt r/\sqrt{n_1n_2}$. The property depends only on $P_U$, $P_V$ and $E$, so it does not depend on the choice of SVD.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2055, assumptions A1, A2, Eqs. (I.8a), (I.8b), (I.9) and the definition of the strong incoherence property

import Definitions.Def_matrix_completion_svd

open MatrixCompletion

namespace CandesTao.Shared

/-- Condition (I.8a) (and, applied to the right singular vectors, (I.8b)) of
Candès–Tao: for an orthonormal family `u₀, …, u_{r-1}` in `ℝ^N` with projection
`P = ∑ₖ uₖ uₖ*`, every entry of `P` deviates from `(r/N)·1_{a=a'}` by at most
`μ √r / N`:
`|⟨e_a, P e_{a'}⟩ - (r/N) 1_{a=a'}| ≤ μ √r / N` for all `a, a'`. -/
def ProjectionIncoherent {N r : ℕ} (u : Fin r → (Fin N → ℝ)) (μ : ℝ) : Prop :=
  ∀ a a' : Fin N,
    |(∑ k : Fin r, u k a * u k a') - (if a = a' then (r : ℝ) / (N : ℝ) else 0)| ≤
      μ * Real.sqrt (r : ℝ) / (N : ℝ)

/-- Strong incoherence property with parameter `μ` (Candès–Tao, assumptions A1–A2,
p. 2055): `μ > 0`, the column-space projection `P_U` obeys (I.8a) and the row-space
projection `P_V` obeys (I.8b) with `μ₁ = μ`, and the sign matrix `E = ∑ₖ uₖ vₖ*`
obeys (I.9), `|E_ab| ≤ μ √(r / (n₁ n₂))`, with `μ₂ = μ` (the platform predicate `A1`). -/
def StrongIncoherence {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂} (S : SVD M r) (μ : ℝ) :
    Prop :=
  0 < μ ∧ ProjectionIncoherent S.u μ ∧ ProjectionIncoherent S.v μ ∧ A1 S μ

end CandesTao.Shared


