-- Prove2me | Definitions.Def_LowRankMarkov_RankMLE_Setting
-- name    : LowRankMarkov_RankMLE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:36.419466+00:00
-- url     : https://prove2.me/theorems/87b55bb3-156a-40ca-a30d-12e6a89efa0c
-- title:
--   Assumption 1, Remark 2, (2), (5), pp. 6–10, 14, ec1 — KL divergences, transition counts, likelihood ℓ_n, empirical KL, minoration, rank-constrained MLE
-- statement:
--   This file fixes the estimation problem of §3 of Zhu, Li, Wang and Zhang: estimating a low-rank transition matrix $P\in\mathbb R^{p\times p}$ from one trajectory $X_0,\dots,X_n$ of the chain.
--
--   1. **KL divergences.** For discrete distributions $u,v$ on $[p]$, $D_{\mathrm{KL}}(u,v)=\sum_j u_j\log(u_j/v_j)\,1_{\{u_j\neq0\}}$. For transition matrices $P,Q$ and the stationary law $\pi$ of $P$,
--   $$D_{\mathrm{KL}}(P,Q)=\sum_{i,j=1}^p\pi_iP_{ij}\log(P_{ij}/Q_{ij})\,1_{\{P_{ij}\neq0\}} .$$
--   2. **Counts and likelihood** (2). $n_{ij}=|\{1\le k\le n: X_{k-1}=s_i,\ X_k=s_j\}|$ and
--   $$\ell_n(Q)=-\frac1n\sum_{i=1}^p\sum_{j=1}^p n_{ij}\log Q_{ij}.$$
--   3. **Empirical KL** (p. 14). $\widetilde D_{\mathrm{KL}}(P,Q)=\ell_n(Q)-\ell_n(P)$.
--   4. **Assumption 1.** (i) $\operatorname{rank}(P)=r$; (ii) $P_{jk}\in\{0\}\cup[\alpha/p,\beta/p]$ for all $j,k$, for constants $\alpha,\beta>0$.
--   5. **Minoration** (Remark 2). $\alpha/p\le P_{jk}\le\beta/p$ for all $j,k$: Assumption 1(ii) with $0$ removed.
--   6. **Concentration class** (p. 14). $\mathcal C$ consists of the row-stochastic matrices $Q$ in the entrywise box with $\|Q-P\|_*\le4\sqrt2\|Q-P\|_F$; it has no rank constraint.
--   7. **Rank-constrained MLE** (5). The feasible set is $\{Q: Q1_p=1_p,\ \alpha/p\le Q_{ij}\le\beta/p\ \forall i,j,\ \operatorname{rank}(Q)\le r\}$, and $\widehat P^r$ is a minimizer of $\ell_n$ over it.
--
--   These are the objects of Theorem 2, the paper's KL error bound for $\widehat P^r$, and of the lemmas its proof uses.
--
--   **Formalization Note** `Real.log` is the natural logarithm. The indicator $1_{\{P_{ij}\ne0\}}$ is written out, so `Real.log 0 = 0` never enters $D_{\mathrm{KL}}$. In $\ell_n(P)$ a factor $\log P_{ij}$ with $P_{ij}=0$ multiplies a count that is $0$ on every trajectory of positive probability. "$\widehat P^r$ is a rank-constrained MLE" is the predicate `IsRankMLE`: the argmin need not be unique, and theorems quantify over every selection of minimizers. The positivity of $\alpha,\beta$ is a hypothesis of each theorem.
-- source:
--   Zhu, Li, Wang & Zhang, Learning Markov Models via Low-Rank Optimization, arXiv:1907.00113v2, p. 6 (D_KL), p. 8 ((2), Assumption 1, Remark 2), p. 10 ((5)), p. 14 (D̃_KL), ec1 (Lemma EC.1, D_KL(u, v))

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic
import Definitions.Def_LowRankMarkov_RankMLE_Chain

namespace LowRankMarkov.RankMLE

open Matrix
open CaiCandesShen.Convergence

/-- The Kullback–Leibler divergence of two discrete distributions `u, v` on `[p]`:
`D_KL(u, v) = ∑_j u_j log(u_j / v_j) 1{u_j ≠ 0}` (Lemma EC.1, ec1). -/
noncomputable def klVec {p : ℕ} (u v : Fin p → ℝ) : ℝ :=
  ∑ j, if u j = 0 then 0 else u j * Real.log (u j / v j)

/-- The KL divergence of transition matrices weighted by `π` (§3, p. 6):
`D_KL(P, Q) = ∑_{i,j} π_i P_ij log(P_ij / Q_ij) 1{P_ij ≠ 0}`. -/
noncomputable def klDiv {p : ℕ} (π : Fin p → ℝ) (P Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, if P i j = 0 then 0 else π i * P i j * Real.log (P i j / Q i j)

/-- The transition counts `n_ij := |{1 ≤ k ≤ n | X_{k−1} = s_i, X_k = s_j}|` of the trajectory
`x = (X₀, …, X_n)` (p. 8). -/
def transCount {p n : ℕ} (x : Fin (n + 1) → Fin p) (i j : Fin p) : ℕ :=
  (Finset.univ.filter fun k : Fin n => x k.castSucc = i ∧ x k.succ = j).card

/-- The averaged negative log-likelihood (2), p. 8:
`ℓ_n(Q) := −(1/n) ∑_{i,j} n_ij log(Q_ij)`. -/
noncomputable def negLogLik {p n : ℕ} (x : Fin (n + 1) → Fin p)
    (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  -(1 / (n : ℝ)) * ∑ i, ∑ j, (transCount x i j : ℝ) * Real.log (Q i j)

/-- The empirical KL divergence of `Q` from `P` (p. 14): `D̃_KL(P, Q) := ℓ_n(Q) − ℓ_n(P)`. -/
noncomputable def empKL {p n : ℕ} (x : Fin (n + 1) → Fin p)
    (P Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  negLogLik x Q - negLogLik x P

/-- Assumption 1 (p. 8): (i) `rank(P) = r`; (ii) `P_jk ∈ {0} ∪ [α/p, β/p]` for all `j, k`.
(The positivity `α, β > 0` is a separate hypothesis of each theorem.) -/
def Assumption1 {p : ℕ} (α β : ℝ) (r : ℕ) (P : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  P.rank = r ∧ ∀ j k, P j k = 0 ∨ (α / (p : ℝ) ≤ P j k ∧ P j k ≤ β / (p : ℝ))

/-- The `(α/p)`-minoration condition of Remark 2 (p. 8): Assumption 1(ii) with `0` removed from
the feasible range, `α/p ≤ P_jk ≤ β/p` for all `j, k`. -/
def Minorated {p : ℕ} (α β : ℝ) (P : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ j k, α / (p : ℝ) ≤ P j k ∧ P j k ≤ β / (p : ℝ)

/-- The feasible set of the rank-constrained MLE (5), p. 10:
`Q 1_p = 1_p`, `α/p ≤ Q_ij ≤ β/p` for all `i, j`, and `rank(Q) ≤ r`. -/
def RankFeasible {p : ℕ} (α β : ℝ) (r : ℕ) (Q : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  (∀ i, ∑ j, Q i j = 1) ∧ (∀ i j, α / (p : ℝ) ≤ Q i j ∧ Q i j ≤ β / (p : ℝ)) ∧ Q.rank ≤ r

/-- The class `𝒞` on p. 14. Its nuclear-norm cone has factor `4 × √2` and does not
impose a rank constraint. -/
noncomputable def ConcentrationClass {p : ℕ} (α β : ℝ)
    (P Q : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  nuclearNorm (Q - P) ≤ 4 * Real.sqrt 2 * frobNorm (Q - P) ∧
  (∀ i, ∑ j, Q i j = 1) ∧
  ∀ i j, α / (p : ℝ) ≤ Q i j ∧ Q i j ≤ β / (p : ℝ)

/-- `Q` is a rank-constrained MLE `P̂^r` for the trajectory `x` ((5), p. 10): `Q` is feasible for (5)
and minimizes `ℓ_n` over the feasible set. -/
def IsRankMLE {p n : ℕ} (α β : ℝ) (r : ℕ) (x : Fin (n + 1) → Fin p)
    (Q : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  RankFeasible α β r Q ∧ ∀ Q', RankFeasible α β r Q' → negLogLik x Q ≤ negLogLik x Q'

end LowRankMarkov.RankMLE


