-- Prove2me | Definitions.Def_PrivBayesTest_Supplement_sbmWeight
-- name    : PrivBayesTest_Supplement_sbmWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:09:58.229799+00:00
-- url     : https://prove2.me/theorems/b60ee98c-f2a1-4f57-998b-32a9e021cf3b
-- title:
--   The stochastic block model $\mathrm{SBM}(n,p,W)$ and its logarithmic-degree regime $W=\log(n)Q/n$
-- statement:
--   Fix $k$ communities $[k]$, a prior $p\in[0,1]^k$ with $\sum_\ell p_\ell=1$ and a symmetric matrix $W\in[0,1]^{k\times k}$ of connection probabilities. A pair $(\sigma,G)\sim\mathrm{SBM}(n,p,W)$ consists of a label vector $\sigma\in[k]^n$ with i.i.d. components of law $p$ and a simple graph $G$ on $[n]$ in which, given $\sigma$, each unordered pair $\{u,v\}$, $u\ne v$, is an edge independently with probability $W_{\sigma_u\sigma_v}$. Its law is
--
--   $$\Pr[(\sigma,G)]=\prod_{v\in[n]}p_{\sigma_v}\prod_{u<v}\begin{cases}W_{\sigma_u\sigma_v}&uv\in E(G),\\ 1-W_{\sigma_u\sigma_v}&uv\notin E(G).\end{cases}$$
--
--   The **logarithmic-degree regime** $\mathrm{SBM}(n,p,\log(n)Q/n)$ takes, for a fixed symmetric $Q\in\mathbb R_+^{k\times k}$, the connection matrix with entries $\log(n)\,Q_{ab}/n$.
--
--   This is the random-graph model of the supplement's private exact-recovery theorems (Theorems 1.7 and 4.8).
--
--   **Formalization Note** Vertices are $\mathrm{Fin}\,n$ and communities $\mathrm{Fin}\,k$; the law is a finite weight function on pairs $(\sigma,G)$, and each unordered pair is counted once as $u<v$. For the finitely many $n$ at which $\log(n)Q_{ab}/n>1$ the entry is truncated at $1$; the theorems using it are limits as $n\to\infty$, which these $n$ do not affect.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Definition 1.5, p.6; SBM(n, p, log(n)Q/n), Theorem 1.7, p.8, and §4.1, p.16

import Mathlib

namespace PrivBayesTest

namespace Supplement

/-- The law of the **stochastic block model** `(σ, G) ∼ SBM(n, p, W)` (Jacobsen, *Optimal Error
Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256
abff2fdd…124ef), Definition 1.5, p.6, PDF p.6): the probability of the pair `(σ, G)`, where the
label vector `σ ∈ [k]ⁿ` has i.i.d. components with law `p` and, given `σ`, each unordered pair
`{u, v}` (`u ≠ v`) is an edge of the simple graph `G` independently with probability
`W_{σ_u, σ_v}`:

`sbmWeight p W σ G = ∏_v p_{σ_v} · ∏_{u < v} (W_{σ_u σ_v} if uv ∈ G, else 1 − W_{σ_u σ_v})`.

**Formalization Note**
* Vertices are `Fin n`, communities `Fin k`; the law is a finite weight function on
  `(Fin n → Fin k) × SimpleGraph (Fin n)`. It is a probability weight (nonnegative, total mass 1)
  whenever `p` is a probability vector and every `W a b ∈ [0, 1]`; the theorems of the supplement
  state the hypotheses on `p` and `Q` under which this holds.
* Each unordered pair is counted once, as the ordered pair `u < v`. -/
noncomputable def sbmWeight {k n : ℕ} (p : Fin k → ℝ) (W : Matrix (Fin k) (Fin k) ℝ)
    (σ : Fin n → Fin k) (G : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact (∏ v, p (σ v)) *
    ∏ u : Fin n, ∏ v ∈ Finset.univ.filter (fun v : Fin n => u < v),
      (if G.Adj u v then W (σ u) (σ v) else 1 - W (σ u) (σ v))

/-- The edge-probability matrix of the **logarithmic-degree regime** `SBM(n, p, log(n) Q / n)`
(Jacobsen, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Theorem 1.7, p.8, and §4,
p.16): the entry `(a, b)` is `log(n) Q_{ab} / n`.

**Formalization Note** For the finitely many `n` with `log(n) Q_{ab} / n > 1` the paper's
probability is undefined; the entry is truncated at `1` (`min 1 …`). Both theorems that use this
matrix are statements about limits `n → ∞`, which these finitely many `n` do not affect. At
`n = 0, 1` the entry is `0` (`Real.log 0 = Real.log 1 = 0`). -/
noncomputable def logRegime {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun a b => min 1 (Real.log n * Q a b / n)

end Supplement

end PrivBayesTest


