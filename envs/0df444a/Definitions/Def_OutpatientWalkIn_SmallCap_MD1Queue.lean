-- Prove2me | Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
-- name    : OutpatientWalkIn_SmallCap_MD1Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:00.428393+00:00
-- url     : https://prove2.me/theorems/5b17d254-623f-4d56-b601-2f579d291f3d
-- title:
--   Online App. C — the M/D/1/K−1+p queue: Poisson weights α_j, the a_j recursion, b_j, a′_K (26), the departure law q_j (27), α′_j (24), and the blocking probability π(δ, μ_S) (Cor. C.1)
-- statement:
--   This module defines the closed-form quantities of the **M/D/1/K−1+p queue** of Liu, van Jaarsveld, Wang and Xiao (Online Appendix C): a single server with deterministic service time $1/\mu_S$ and Poisson arrivals of rate $\lambda$, where an arrival joins if fewer than $K$ customers are in the system, joins with probability $p$ if exactly $K$ are present, and balks otherwise. Write $\rho = \lambda/\mu_S$.
--
--   1. **Poisson weights.** $\alpha_j = \rho^j e^{-\rho}/j!$, the probability of $j$ arrivals during one service slot.
--   2. **The sequence $a_j$** (Brun–Garcia). $a_0 = 1$ and, for $j \ge 1$,
--   $$a_j = e^{\rho}\Big(a_{j-1} - \sum_{i=1}^{j-1}\alpha_i a_{j-i} - \alpha_{j-1}a_0\Big),$$
--   which gives $a_1 = e^\rho - 1$.
--   3. **Partial sums.** $b_j = \sum_{i=0}^{j} a_i$.
--   4. **The term $a'_K$** of (26), for $0<p<1$ and $K \ge 1$:
--   $$a'_K = (e^{p\rho}-1)(1-p)^{-K+1} + (e^{p\rho} - p e^{p\rho} - 1)\sum_{i=1}^{K-1}(b_i - b_{i-1})(1-p)^{-K+i}.$$
--   5. **The departure-epoch law** $q_j$, $0 \le j \le K$. For $p = 1$: $q_0 = 1/b_K$ and $q_j = (b_j - b_{j-1})/b_K$ for $1 \le j \le K$. For $0<p<1$, (27): $q_0 = 1/(b_{K-1}+a'_K)$, $q_j = (b_j-b_{j-1})/(b_{K-1}+a'_K)$ for $1 \le j \le K-1$, and $q_K = a'_K/(b_{K-1}+a'_K)$. The quantity $q_0$ is singled out as its own definition.
--   6. **Partial-joining weights** (24): $\alpha'_j = \sum_{k \ge 0}(1-p)^k\alpha_{j+k}$, the probability that exactly $j$ customers join during a slot that starts with $K-j$ customers present.
--   7. **Buffer parameters.** For a delay threshold $\delta$ and service rate $\mu_S$: $K = \lceil \delta\mu_S \rceil$ and $p = \delta\mu_S + 1 - K$.
--   8. **Blocking probability** (Corollary C.1). For $\mu_S > 0$,
--   $$\pi(\delta,\mu_S) = 1 - \frac{1}{q_0 + \rho},$$
--   with $q_0$ computed from $K = \lceil\delta\mu_S\rceil$, $p = \delta\mu_S+1-K$ and $\rho = \lambda/\mu_S$. For $\mu_S = 0$, $\pi(\delta, 0) = 1$.
--
--   The appointment queue of the observable setting is this queue with buffer size $K - 1 + p = \delta\mu_S$ (Lemma C.1): a patient who sees $k$ patients waiting computes the delay $(k+\tilde u)/\mu_S$ and schedules when it is at most $\delta$. The blocking probability $\pi(\delta,\mu_S)$ is the fraction of strategic patients who do not schedule.
--
--   **Formalization Note** $(1-p)^{-n}$ is written $((1-p)^n)^{-1}$. The two cases $p = 1$ and $p < 1$ are separate branches, so no formula with $(1-p)^{-n}$ is evaluated at $p = 1$. At $\delta\mu_S = 0$ the definition gives $K = 0$, $p = 1$, $q_0 = 1/b_0 = 1$ and $\pi = \rho/(1+\rho)$, the M/D/1/1 loss probability of Remark C.1. The value $\pi(\delta,0) = 1$ is a convention: with no appointment hours every strategic patient is blocked, which is how the proof of Theorem 2 treats $\mu_S = 0$. The recursion for $a_j$ is written as one clause for all $j \ge 1$; at $j = 1$ it gives the printed $a_1 = e^\rho - 1$. $\alpha'_j$ is a `tsum`, and the series is summable because its terms are at most $\alpha_{j+k}$. Values of $q_j$ for $j > K$ carry no meaning. The paper only uses $\delta \ge 0$ and $\mu_S \ge 0$: for $\delta\mu_S \ge 0$ every natural-number subtraction in these formulas ($K-1$, $K-i$, $j-1$) is exact, while for $\delta\mu_S < 0$ the formulas return values without meaning. Every statement that uses $\pi$ therefore assumes $\delta \ge 0$.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix pp. 5–7, Appendix C: Lemma C.1, Remark C.1, (24), §C.1, (26), (27), Corollary C.1

import Mathlib

namespace OutpatientWalkIn.SmallCap

noncomputable section

open Finset

/-- Poisson weights (Online Appendix p. 6): `α_j(ρ) = ρ^j e^{-ρ} / j!`, the probability of `j`
arrivals during one deterministic service slot when `ρ = λ / μ_S`. -/
def alphaP (ρ : ℝ) (j : ℕ) : ℝ := Real.exp (-ρ) * ρ ^ j / (j.factorial : ℝ)

/-- The Brun–Garcia sequence (Online Appendix p. 6): `a_0 = 1` and, for `j = n + 1 ≥ 1`,
`a_j = e^ρ (a_{j-1} - Σ_{i=1}^{j-1} α_i a_{j-i} - α_{j-1} a_0)`.
The single clause for `j ≥ 1` reproduces the printed `a_1 = e^ρ - 1` (empty sum, `α_0 = e^{-ρ}`).
`attach` only records `1 ≤ i ≤ n` for the termination proof. -/
def aSeq (ρ : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Real.exp ρ *
      (aSeq ρ n - ∑ i ∈ (Ico 1 (n + 1)).attach, alphaP ρ i.1 * aSeq ρ (n + 1 - i.1)
        - alphaP ρ n * aSeq ρ 0)
termination_by n => n
decreasing_by
  all_goals first
    | omega
    | (have h := i.2; simp only [Finset.mem_Ico] at h; omega)

/-- Partial sums `b_j = Σ_{i=0}^{j} a_i` (Online Appendix p. 7). -/
def bSeq (ρ : ℝ) (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), aSeq ρ i

/-- `a'_K` of (26), Online Appendix p. 7, for `0 < p < 1` and `K ≥ 1`:
`(e^{pρ} - 1)(1-p)^{-K+1} + (e^{pρ} - p e^{pρ} - 1) Σ_{i=1}^{K-1} (b_i - b_{i-1})(1-p)^{-K+i}`,
with `(1-p)^{-n}` written `((1-p)^n)⁻¹`. -/
def aPrimeK (K : ℕ) (p ρ : ℝ) : ℝ :=
  (Real.exp (p * ρ) - 1) * ((1 - p) ^ (K - 1))⁻¹ +
    (Real.exp (p * ρ) - p * Real.exp (p * ρ) - 1) *
      ∑ i ∈ Ico 1 K, (bSeq ρ i - bSeq ρ (i - 1)) * ((1 - p) ^ (K - i))⁻¹

/-- The departure-epoch law of the `M/D/1/K-1+p` queue: §C.1 (`p = 1`, Online Appendix p. 7:
`q_0 = 1/b_K`, `q_j = (b_j - b_{j-1})/b_K`) and (27) (`0 < p < 1`). Meaningful for `j ≤ K`. -/
def qVec (K : ℕ) (p ρ : ℝ) (j : ℕ) : ℝ :=
  if p = 1 then
    (if j = 0 then 1 / bSeq ρ K else (bSeq ρ j - bSeq ρ (j - 1)) / bSeq ρ K)
  else
    (if j = 0 then 1 / (bSeq ρ (K - 1) + aPrimeK K p ρ)
     else if j ≤ K - 1 then (bSeq ρ j - bSeq ρ (j - 1)) / (bSeq ρ (K - 1) + aPrimeK K p ρ)
     else aPrimeK K p ρ / (bSeq ρ (K - 1) + aPrimeK K p ρ))

/-- `q_0` of (27) (and of §C.1 when `p = 1`). -/
def q0 (K : ℕ) (p ρ : ℝ) : ℝ :=
  if p = 1 then 1 / bSeq ρ K else 1 / (bSeq ρ (K - 1) + aPrimeK K p ρ)

/-- `α'_j = α_j + (1-p) α_{j+1} + (1-p)^2 α_{j+2} + ⋯` of (24), Online Appendix p. 6. -/
def alphaPrime (p ρ : ℝ) (j : ℕ) : ℝ := ∑' k : ℕ, (1 - p) ^ k * alphaP ρ (j + k)

/-- `K = ⌈δ μ_S⌉` (Online Appendix p. 5). -/
def bufferK (δ μS : ℝ) : ℕ := ⌈δ * μS⌉₊

/-- `p = δ μ_S + 1 - K` (Online Appendix p. 5). -/
def bufferP (δ μS : ℝ) : ℝ := δ * μS + 1 - (bufferK δ μS : ℝ)

/-- The blocking probability `π(δ, μ_S)` of the `M/D/1/δμ_S` queue with Poisson arrival rate `lam`
(Corollary C.1, Online Appendix p. 7): `π(δ, μ_S) = 1 - 1/(q_0 + ρ)` with `ρ = lam/μ_S`,
`K = ⌈δμ_S⌉`, `p = δμ_S + 1 - K`. With no appointment capacity (`μ_S = 0`) every arrival is
blocked: `π(δ, 0) := 1`. -/
def blockProb (lam δ μS : ℝ) : ℝ :=
  if μS = 0 then 1
  else 1 - 1 / (q0 (bufferK δ μS) (bufferP δ μS) (lam / μS) + lam / μS)

end

end OutpatientWalkIn.SmallCap


