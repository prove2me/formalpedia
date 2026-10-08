-- Prove2me | Definitions.Def_Reiman84_QueueLength_HeavyTraffic
-- name    : Reiman84_QueueLength_HeavyTraffic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:48:28.449578+00:00
-- url     : https://prove2.me/theorems/3c493041-fad4-4e40-a42c-c4316a49273c
-- title:
--   Section 3 — the heavy-traffic conditions (20)–(26), the diffusion scaling, and the covariance matrix (27)–(28)
-- statement:
--   This file states the assumptions of §3 of Reiman (1984) on a sequence of networks of §2, indexed by $n\ge1$, each on its own probability space $(\Omega^n,\mathcal F^n,P^n)$, with the same $K$, the same arrival set $\mathcal J$ and the same routing matrix $P$.
--
--   1. **Heavy-traffic conditions.** As $n\to\infty$, for $1\le k\le K$,
--   $$\mu_k(n)\to\mu_k,\quad\lambda_k(n)\to\lambda_k,\quad a_k(n)\to a_k,\quad s_k(n)\to s_k,\quad \sqrt n\,(\nu_k(n)-\mu_k(n))\equiv c_k(n)\to c_k,\qquad(20)\text{–}(24)$$
--   all limits finite, and
--   $$\max_{1\le k\le K}\sup_{n\ge1}E\{(v_k^1(n))^{2+\epsilon}\}<\infty,\qquad \max_{k}\sup_{n\ge1}E\{(u_k^1(n))^{2+\epsilon}\}<\infty\qquad(25),(26)$$
--   each for some $\epsilon>0$.
--
--   2. **Diffusion scaling.** For a path $x$, $t\mapsto n^{-1/2}x(nt)$; thus $Z^n(t)=n^{-1/2}Q^n(nt)$, $\zeta^n(t)=n^{-1/2}X^n(nt)$, $\tilde\zeta^n(t)=n^{-1/2}\tilde X^n(nt)$.
--
--   3. **The covariance matrix $\mathcal A$.**
--   $$\mathcal A_{ii}=\lambda_i^3a_i+\mu_i^3s_i(1-2p_{ii})+\sum_{j=1}^K\mu_jp_{ji}\big(1-p_{ji}+p_{ji}\mu_j^2s_j\big),\qquad(27)$$
--   $$\mathcal A_{ij}=-\Big[\mu_i^3s_ip_{ij}+\mu_j^3s_jp_{ji}+\sum_{k=1}^K\mu_kp_{ki}p_{kj}\big(1-\mu_k^2s_k\big)\Big],\quad i\ne j.\qquad(28)$$
--
--   Theorem 1 says that under these conditions the scaled queue length converges to a reflected Brownian motion with drift $c$ and covariance $\mathcal A$.
--
--   **Formalization Note** Networks are indexed by `n : ℕ`; the network at index $0$ is never used by the conclusions (convergence is as $n\to\infty$ and (25)–(26) are imposed for $n\ge1$). Condition (22) is imposed for $k\in\mathcal J$ only, where $a_k$ is defined; (21) is imposed for all $k$ with $\lambda_k(n)=0$ off $\mathcal J$. Condition (26) is printed with $\max_{1\le k\le K}$ but $u_k$ exists only for $k\in\mathcal J$, so it is imposed over $k\in\mathcal J$. The moments in (25)–(26) are Lebesgue integrals of nonnegative functions with a finite uniform bound. The page prints (28) for $i<j$; the expression is symmetric in $i,j$ and is used for every $i\ne j$. The scaling $n^{-1/2}$ is written $(\sqrt n)^{-1}$.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), pp. 446–447, Section 3, Eqs. (20)–(28)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory ProbabilityTheory Matrix

/-!
Reiman (1984), §3 (pp. 446–447): a sequence of networks of §2 indexed by `n ≥ 1` with the same
`K`, the same arrival set `𝒥` and the same routing matrix `P`; the heavy-traffic conditions
(20)–(26); the diffusion scaling `x ↦ n^{-1/2} x(n ·)`; and the covariance matrix `𝒜` of
(27)–(28).
-/

/-- The diffusion scaling `t ↦ n^{-1/2} x(nt)` (p. 447): `Zⁿ`, `ζⁿ`, `ζ̃ⁿ` are this scaling of
`Qⁿ`, `Xⁿ`, `X̃ⁿ`. -/
noncomputable def diffScale {K : ℕ} (n : ℕ) (x : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t => (Real.sqrt n)⁻¹ • x (n * t)

/-- The covariance matrix `𝒜` of (27)–(28), p. 447, built from the limits `λ, a, μ, s` and the
routing matrix `P`:
* (27) `𝒜_ii = λ_i³ a_i + μ_i³ s_i (1 − 2 p_ii) + ∑_j μ_j p_ji (1 − p_ji + p_ji μ_j² s_j)`;
* (28) `𝒜_ij = −[μ_i³ s_i p_ij + μ_j³ s_j p_ji + ∑_k μ_k p_ki p_kj (1 − μ_k² s_k)]` for `i ≠ j`
  (printed for `i < j`; the expression is symmetric in `i, j`, so `𝒜_ji = 𝒜_ij`). -/
noncomputable def covA {K : ℕ} (lam a mu s : Fin K → ℝ) (P : Matrix (Fin K) (Fin K) ℝ) :
    Matrix (Fin K) (Fin K) ℝ :=
  fun i j =>
    if i = j then
      lam i ^ 3 * a i + mu i ^ 3 * s i * (1 - 2 * P i i) +
        ∑ l, mu l * P l i * (1 - P l i + P l i * mu l ^ 2 * s l)
    else
      -(mu i ^ 3 * s i * P i j + mu j ^ 3 * s j * P j i +
        ∑ l, mu l * P l i * P l j * (1 - mu l ^ 2 * s l))

/-- The standing assumptions of §3 (pp. 446–447) on a sequence of networks `net n`
(`n ≥ 1`), with the routing matrix `R` and the finite limits `μ, s, λ, a, c`:
* the routing matrix of every network is `R` (`K`, `𝒥` are fixed by the type);
* (20) `μ_k(n) → μ_k`; (21) `λ_k(n) → λ_k`; (22) `a_k(n) → a_k` for `k ∈ 𝒥`; (23) `s_k(n) → s_k`;
* (24) `c_k(n) = √n (ν_k(n) − μ_k(n)) → c_k`;
* (25) for some `ε > 0`, `max_k sup_{n ≥ 1} E[(v_k¹(n))^{2+ε}] < ∞`;
* (26) for some `ε > 0`, `max_{k ∈ 𝒥} sup_{n ≥ 1} E[(u_k¹(n))^{2+ε}] < ∞`. -/
def HeavyTrafficAssumptions {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ) : Prop :=
  (∀ n, (net n).routing = R) ∧
  (∀ k, Tendsto (fun n => (net n).mu k) atTop (𝓝 (mu k))) ∧
  (∀ k, Tendsto (fun n => (net n).lam k) atTop (𝓝 (lam k))) ∧
  (∀ k ∈ J, Tendsto (fun n => (net n).aVar k) atTop (𝓝 (a k))) ∧
  (∀ k, Tendsto (fun n => (net n).sVar k) atTop (𝓝 (s k))) ∧
  (∀ k, Tendsto (fun n : ℕ => Real.sqrt n * ((net n).nu k - (net n).mu k)) atTop (𝓝 (c k))) ∧
  (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ n, 1 ≤ n → ∀ k,
    ∫⁻ ω, ENNReal.ofReal ((net n).v k 0 ω ^ (2 + ε)) ∂(P n) ≤ ENNReal.ofReal C) ∧
  (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ n, 1 ≤ n → ∀ k ∈ J,
    ∫⁻ ω, ENNReal.ofReal ((net n).u k 0 ω ^ (2 + ε)) ∂(P n) ≤ ENNReal.ofReal C)

end Reiman84.QueueLength


