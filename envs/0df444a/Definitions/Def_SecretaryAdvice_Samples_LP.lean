-- Prove2me | Definitions.Def_SecretaryAdvice_Samples_LP
-- name    : SecretaryAdvice_Samples_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:14.634511+00:00
-- url     : https://prove2.me/theorems/11611efa-ac3e-4cf8-9894-fe0e717507f1
-- title:
--   §5 p. 15, eq. (8) p. 13, proof of Theorem 16 p. 16 — the samples LP, its greedy dual solution and the perturbation Δ
-- statement:
--   This file defines the linear program of the secretary problem with $k$ samples and $n$ secretaries, as printed in §5, together with the objects used in the proof of Theorem 16. Rounds are $i\in[n]=\{1,\dots,n\}$ and signals are $s\in\mathcal S=\{0,1,\dots,k\}$.
--
--   1. **Coefficients**
--   $$a(i,s)=\frac{1}{k+1}\prod_{t=1}^{n-1}\frac{s+t}{k+t+1},\qquad c(i,s,j,s')=\begin{cases}\dfrac{1}{s+1}\displaystyle\prod_{t=1}^{j-1}\frac{s'+t}{s+t+1}, & s'\le s,\\[1ex] 0, & s'>s.\end{cases}$$
--   Neither depends on $i$.
--   2. **Primal LP**: maximize $\sum_i\sum_s z(i,s)\,a(i,s)$ subject to $z(i,s)\ge 0$ and
--   $$z(i,s)\le 1-\sum_{j<i}\sum_{s'\le s} z(j,s')\,c(i,s,j,s').$$
--   3. **Dual LP**: minimize $\sum_i\sum_s u(i,s)$ subject to $u(i,s)\ge 0$ and
--   $$u(i,s)+\sum_{j>i}\sum_{s'\ge s}u(j,s')\,c(j,s',i,s)\ge a(i,s).$$
--   4. **Greedy dual solution** (8): $u(n,s)=a(n,s)$ and, for $i<n$,
--   $$u(i,s)=\max\Bigl\{0,\;a(i,s)-\sum_{j>i}\sum_{s'\ge s}u(j,s')\,c(j,s',i,s)\Bigr\}.$$
--   5. **Threshold shape**: $z$ has the threshold shape for $t:\mathcal S\to\mathbb N$ if $z(i,s)=0$ for $i<t(s)$ and the primal $(i,s)$-constraint holds with equality for $i\ge t(s)$.
--   6. **Perturbation** $\Delta$ (proof of Theorem 16) for an index $i^*$, a signal $s^*$ and $\delta\in\mathbb R$: $\Delta(i^*,s^*)=-\delta$, $\Delta(i,s)=0$ for all other $i\ge i^*$, and for $i<i^*$
--   $$\Delta(i,s)=-\sum_{j=i+1}^{i^*}\sum_{s'\ge s}\Delta(j,s')\,c(j,s',i,s).$$
--   7. **Cumulative change** $R_i:=\sum_{j\ge i}\sum_{s\le s^*}\Delta(j,s)$.
--
--   The primal LP describes the stopping probabilities $z(i,s)=\mathbb P[i\text{ is picked}\mid T_i,s_i=s]$ that a policy can achieve; its value is the optimal winning probability. The greedy rule solves the dual by backward induction.
--
--   **Formalization Note** Variables are functions $\mathbb N\to\mathbb N\to\mathbb R$ read only on $[n]\times\mathcal S$; the feasibility predicates quantify over $1\le i\le n$, $0\le s\le k$. The greedy solution and $\Delta$ are defined by well-founded recursion downward from $n$ (resp. $i^*$). $R_i$ is summed for $j$ from $i$ to $i^*$, since $\Delta(j,\cdot)=0$ for $j>i^*$. Products over empty ranges equal $1$.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 13 (primal–dual pair, eq. (8)), p. 15 (§5 coefficients and samples LP), p. 16 (proof sketch of Theorem 16: Δ, R_i)

import Mathlib

namespace SecretaryAdvice.Samples

/-!
§5 *LP Formulation* (p. 15), equation (8) (p. 13) and the proof of Theorem 16 (p. 16 and
Appendix A, pp. 25–26) of Dütting et al., *Secretaries with Advice* (arXiv:2011.06726v1):
the primal–dual pair of the secretary problem with `k` samples, its greedy dual solution, and
the perturbation `Δ` of the optimality proof.

Rounds `i` are natural numbers `1, …, n` (1-based, as on the page) and signals are natural
numbers `s ∈ S = {0, …, k}`. Variables `z u : ℕ → ℕ → ℝ` are read only on `[1, n] × S`.
-/

open Finset

/-- `a(i,s) = 1/(k+1) · ∏_{t=1}^{n−1} (s+t)/(k+t+1)` (it does not depend on `i`). -/
noncomputable def aCoef (n k s : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1)

/-- `c(i,s,j,s′) = 1/(s+1) · ∏_{t=1}^{j−1} (s′+t)/(s+t+1)` if `s′ ≤ s`, and `0` otherwise
(it does not depend on `i`). -/
noncomputable def cCoef (_i s j s' : ℕ) : ℝ :=
  if s' ≤ s then
    1 / ((s : ℝ) + 1) * ∏ t ∈ Icc 1 (j - 1), ((s' : ℝ) + t) / ((s : ℝ) + t + 1)
  else 0

/-- Primal feasibility: `z(i,s) ≥ 0` and
`z(i,s) ≤ 1 − Σ_{j<i} Σ_{s′≤s} z(j,s′)·c(i,s,j,s′)` for `i ∈ [n]`, `s ∈ S`. -/
def PrimalFeasible (n k : ℕ) (z : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ Icc 1 n, ∀ s, s ≤ k →
    0 ≤ z i s ∧
      z i s ≤ 1 - ∑ j ∈ Ico 1 i, ∑ s' ∈ range (s + 1), z j s' * cCoef i s j s'

/-- Primal objective `Σ_i Σ_s z(i,s)·a(i,s)`. -/
noncomputable def primalObj (n k : ℕ) (z : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Icc 1 n, ∑ s ∈ range (k + 1), z i s * aCoef n k s

/-- Dual feasibility: `u(i,s) ≥ 0` and
`u(i,s) + Σ_{j>i} Σ_{s′≥s} u(j,s′)·c(j,s′,i,s) ≥ a(i,s)` for `i ∈ [n]`, `s ∈ S`. -/
def DualFeasible (n k : ℕ) (u : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ Icc 1 n, ∀ s, s ≤ k →
    0 ≤ u i s ∧
      aCoef n k s ≤ u i s + ∑ j ∈ Ioc i n, ∑ s' ∈ Icc s k, u j s' * cCoef j s' i s

/-- Dual objective `Σ_i Σ_s u(i,s)`. -/
noncomputable def dualObj (n k : ℕ) (u : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Icc 1 n, ∑ s ∈ range (k + 1), u i s

/-- The greedy dual solution (8): `u(n,s) = a(n,s)` and, for `i < n`,
`u(i,s) = max(0, a(i,s) − Σ_{j>i} Σ_{s′≥s} u(j,s′)·c(j,s′,i,s))`. -/
noncomputable def greedyU (n k : ℕ) (i s : ℕ) : ℝ :=
  if n ≤ i then aCoef n k s
  else max 0 (aCoef n k s -
    ∑ j ∈ (Ioc i n).attach, ∑ s' ∈ Icc s k, greedyU n k j.1 s' * cCoef j.1 s' i s)
termination_by n - i
decreasing_by
  have := (mem_Ioc.mp j.2)
  omega

/-- `z` has the threshold shape for `t`: `z(i,s) = 0` for `i < t(s)`, and the primal
`(i,s)`-constraint is tight for `i ≥ t(s)`. -/
def ThresholdShaped (n k : ℕ) (t : ℕ → ℕ) (z : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ Icc 1 n, ∀ s, s ≤ k →
    (i < t s → z i s = 0) ∧
      (t s ≤ i → z i s = 1 - ∑ j ∈ Ico 1 i, ∑ s' ∈ range (s + 1), z j s' * cCoef i s j s')

/-- The perturbation `Δ` of the proof of Theorem 16 (p. 16): `Δ(i*,s*) = −δ`, `Δ(i,s) = 0` for
all other `i ≥ i*`, and for `i < i*`
`Δ(i,s) = −Σ_{j=i+1}^{i*} Σ_{s′≥s} Δ(j,s′)·c(j,s′,i,s)`. -/
noncomputable def delta (k istar sstar : ℕ) (δ : ℝ) (i s : ℕ) : ℝ :=
  if istar ≤ i then (if i = istar ∧ s = sstar then -δ else 0)
  else -∑ j ∈ (Ioc i istar).attach, ∑ s' ∈ Icc s k,
    delta k istar sstar δ j.1 s' * cCoef j.1 s' i s
termination_by istar - i
decreasing_by
  have := (mem_Ioc.mp j.2)
  omega

/-- `R_i := Σ_{j≥i} Σ_{s≤s*} Δ(j,s)`, the cumulative change of the dual objective
(`Δ(j,·) = 0` for `j > i*`, so the sum stops at `i*`). -/
noncomputable def cumChange (k istar sstar : ℕ) (δ : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Icc i istar, ∑ s ∈ range (sstar + 1), delta k istar sstar δ j s

end SecretaryAdvice.Samples


