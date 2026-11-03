-- Prove2me | Definitions.Def_PLIAG_AssumptionB4
-- name    : PLIAG_AssumptionB4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:24.341226+00:00
-- url     : https://prove2.me/theorems/43f8f348-4d85-48bf-b4fa-12b5f40bd8bd
-- title:
--   Assumption B4: $D_w(v_k,v_j)\le\ell(k-j)\sum_{i=j}^{k-1}D_w(v_{i+1},v_i)$
-- statement:
--   **Assumption B4 (the inequality).** For a function $\ell$ and every sequence $\{v_1,v_2,\dots,v_k\}$ in $\operatorname{int}\operatorname{dom}w$,
--
--   $$
--   D_w(v_k,v_j)\ \le\ \ell(k-j)\sum_{i=j}^{k-1}D_w(v_{i+1},v_i)\qquad\text{for all }j\ge1,\ k>j+1 .
--   $$
--
--   In the paper B4 reads: if the smallest upper bound $\tau$ of the delays is positive, then there is a monotonically increasing $\ell$ with $\ell(1)=1$ satisfying this inequality. The theorems of the mission carry the remaining clauses as separate hypotheses ($\ell$ monotone, $\ell(1)=1$, and this inequality when $\tau>0$). For $w=\tfrac12\|x\|^2$ it holds with $\ell(n)=n$, by the Cauchy–Schwarz inequality.
--
--   **Formalization Note** The finite sequence is encoded as $v:\mathbb N\to\mathbb R^d$ with every term in $\operatorname{int}\operatorname{dom}w$; this is equivalent, since a finite sequence extends by repeating its last term and each inequality only reads $v_j,\dots,v_k$. $\ell:\mathbb N\to\mathbb R$; its value at $0$ is never read.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Assumption B4, §2.3, p.7

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_bregman

namespace PLIAG

/-- **Assumption B4, the inequality** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, §2.3, p.7): for any
sequence `{v_1, …, v_k}` in `int dom w`,
`D_w(v_k, v_j) ≤ ℓ(k − j) Σ_{i=j}^{k−1} D_w(v_{i+1}, v_i)` for all `j ≥ 1`, `k > j + 1`.

The rest of B4 — that this is required only when the smallest delay bound `τ` is positive, and that
`ℓ` is monotonically increasing with `ℓ(1) = 1` — is carried by the theorems as the hypotheses
`0 < τ → AssumptionB4 w ℓ`, `Monotone ℓ`, `ℓ 1 = 1`.

**Formalization Note.** The finite sequence is encoded as `v : ℕ → ℝ^d` with every term in
`int dom w`; this is equivalent (a finite sequence extends by repeating its last term, and the
inequality for `j, k` only reads `v_j, …, v_k`). `ℓ : ℕ → ℝ`; its value at `0` is never read. -/
def AssumptionB4 {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (ℓ : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → EuclideanSpace ℝ (Fin d), (∀ i, v i ∈ interior (AubinLipschitz.effDom w)) →
    ∀ j k : ℕ, 1 ≤ j → j + 1 < k →
      bregman w (v k) (v j) ≤ ((ℓ (k - j) : ℝ) : EReal) *
        ∑ i ∈ Finset.Ico j k, bregman w (v (i + 1)) (v i)

end PLIAG


