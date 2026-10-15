-- Prove2me | Definitions.Def_SampleDrivenOS_Limit_Setting
-- name    : SampleDrivenOS_Limit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:32.925989+00:00
-- url     : https://prove2.me/theorems/4cc656c5-3f2d-47d6-ac52-b78bb8c22f2a
-- title:
--   §3.2, §4.2–4.3, (26) — the stopping program SDCLP_p, its value α(p), the threshold form (12), Lemma 6's times, and the equations of α̃ and α*
-- statement:
--   This file fixes the objects of §4.2–4.3 of Correa, Cristi, Epstein and Soto. Throughout, $p\in(0,1)$ is the sampling probability, ranks $k,\ell,i,j$ start at $1$, and a *stopping rule* is a function $q(t,\ell)\ge0$ of a time $t\in[p,1]$ and a rank $\ell\ge1$.
--
--   **The coefficient $F_k(q)$** ((4), p. 8). For $k\ge1$,
--   $$F_k(q)=\sum_{\ell=1}^{k}\int_p^1 q(t,\ell)\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell}\,dt .$$
--
--   **The program SDCLP$_p$ and its value $\alpha(p)$** (p. 15). A pair $(q,\alpha)$ is *feasible* when
--   1. $q(t,\ell)\ge0$ for all $t\in[p,1]$, $\ell\ge1$, and each $q(\cdot,\ell)$ is integrable on $[p,1]$;
--   2. (10): $t\,q(t,\ell)+\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau\le1$ for all $t\in[p,1]$ and $\ell\ge1$;
--   3. $\alpha\in[0,1]$ and (11): $\alpha\le F_k(q)/(1-p^k)$ for every $k\ge1$.
--
--   The optimal value is
--   $$\alpha(p)=\sup\{\alpha:\ (q,\alpha)\text{ is feasible for SDCLP}_p\}.$$
--
--   **The threshold form (12)** (p. 16). Given times $t_1\le t_2\le\cdots$ and $T_i=\prod_{j=1}^{i}t_j$, the stopping rule
--   $$q(\tau,\ell)=\begin{cases}T_i/\tau^{i+1}&\text{if }\tau\in[t_i,t_{i+1}),\ \ell\le i,\\ 0&\text{otherwise.}\end{cases}$$
--   Together with it, $\mu_k=\sum_{i=k}^{\infty}\frac{T_i}{t_i^{i-1}}\cdot\frac{1}{(i-2)(i-1)}$ (Lemma 5, used for $k\ge3$).
--
--   **Lemma 6's times** (p. 16). For $p,\alpha\in(0,1)$ let $\gamma_k=1-\alpha+\alpha[kp^{k-1}-(k-1)p^k]$ for $k\ge1$, $t_1=p$, $t_2=p\exp(\alpha(1-p)^2/p)$, and for $k\ge2$ let $t_{k+1}>0$ solve (17), $(t_k/t_{k+1})^{k-1}=\gamma_k/\gamma_{k-1}$, that is $t_{k+1}=t_k(\gamma_{k-1}/\gamma_k)^{1/(k-1)}$.
--
--   **The constants.** $\tilde\alpha$ is called a root of (19) at $p$ (Lemma 7, p. 17) when $0<\tilde\alpha<1$ and
--   $$\ln p+\frac{\tilde\alpha(1-p)^2}{p}=\sum_{i=1}^{\infty}\frac{\ln\bigl(1-\tilde\alpha+\tilde\alpha[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)} .$$
--   $\alpha^*$ is called a solution of the prophet equation (p. 17) when $0<\alpha^*<1$ and $\int_0^1\frac{dy}{y(1-\ln y)+1/\alpha^*-1}=1$. Finally, (26) (p. 35) is the ratio
--   $$h(p,\eta)=\frac{\sum_{i=1}^{\infty}\ln\bigl(1-\eta+\eta[(i+1)p^i-ip^{i+1}]\bigr)/(i(i+1))}{\ln p+\eta(1-p)^2/p}.$$
--
--   These are the objects of Theorem 8 and of every milestone of this mission.
--
--   **Formalization Note** A stopping rule is a function `q : ℝ → ℕ → ℝ`, a representative of the paper's $L^1([p,1]\times\mathbb N)$ class; its values at rank $0$ and outside $[p,1]$ are never used, and constraints are imposed pointwise on $[p,1]$ as printed (lowering an a.e.-feasible $q$ on a null set does not change any integral, so $\alpha(p)$ is unchanged). The integral of the series in (10) is a lower Lebesgue integral of an $[0,\infty]$-valued series, so it cannot collapse to a junk value. $\alpha(p)$ is `sSup` of a set that contains $0$ (take $q=0$) and is bounded by $1$, so it is the true supremum. In the threshold form the intervals are the half-open $[t_i,t_{i+1})$ of (7), not the closed ones printed in (12), which overlap at the $t_i$; the index $i$ is the least one with $\tau\in[t_i,t_{i+1})$. Lemma 6's sequence carries a placeholder $t_0=p$ that the paper does not have; it is never used for ranks $\ell\ge1$. The series in (19), (18), (26) and $\mu_k$ are written with the summation index shifted to start at $0$. $\tilde\alpha$ and $\alpha^*$ are predicates, not chosen functions.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 8, (4); p. 15, SDCLP_p (10)–(11); p. 16, (12), Lemma 5 (µ_k), Lemma 6 (γ_k, (17)); p. 17, (19) and the preamble of Theorem 8; p. 35, (26)

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory

namespace SampleDrivenOS.Limit

/-- `(q, α)` is feasible for SDCLP_p (p. 15): `q` satisfies (10) and nonnegativity,
`α ∈ [0, 1]`, and (11): `α ≤ F_k(q) / (1 - p^k)` for every `k ≥ 1`. -/
def IsSDFeasible (p : ℝ) (q : ℝ → ℕ → ℝ) (α : ℝ) : Prop :=
  SampleDrivenOS.Structure.IsFeasible p q ∧ 0 ≤ α ∧ α ≤ 1 ∧ ∀ k : ℕ, 1 ≤ k → α ≤ SampleDrivenOS.Structure.Fk p q k / (1 - p ^ k)

/-- `α(p)`, the optimal value of SDCLP_p (p. 15; p. 17, "α(p) is the optimal value of SDCLP_p").
The set contains `0` (take `q = 0`) and is bounded above by `1`, so `sSup` is the true supremum. -/
noncomputable def sdclpValue (p : ℝ) : ℝ :=
  sSup {α : ℝ | ∃ q : ℝ → ℕ → ℝ, IsSDFeasible p q α}

open Classical in
/-- The threshold form (12) (p. 16), with the half-open intervals of (7) (p. 8):
`q(τ, ℓ) = T_i / τ^{i+1}` if `τ ∈ [t_i, t_{i+1})` and `ℓ ≤ i`, and `0` otherwise. The index `i`
is the least one with `τ ∈ [t_i, t_{i+1})`; for thresholds that are nondecreasing from index `1`
on, these intervals are pairwise disjoint (for `i ≥ 1`), so there is at most one such `i ≥ 1`,
and `i = 0` only occurs below `t_1`, where `ℓ ≤ 0` never holds for `ℓ ≥ 1`. -/
noncomputable def thresholdQ (t : ℕ → ℝ) (τ : ℝ) (ℓ : ℕ) : ℝ :=
  if h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1) then
    (if ℓ ≤ Nat.find h then SampleDrivenOS.Structure.thresholdProd t (Nat.find h) / τ ^ (Nat.find h + 1) else 0)
  else 0

/-- `µ_k = ∑_{i=k}^{∞} T_i / t_i^{i-1} · 1 / ((i-2)(i-1))` (p. 16, Lemma 5), written with the
summation index shifted to start at `0` (term `i` of the paper is term `i - k` here).
Used only for `k ≥ 3`. -/
noncomputable def mu (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' i : ℕ, SampleDrivenOS.Structure.thresholdProd t (i + k) / t (i + k) ^ (i + k - 1) *
    (1 / ((((i + k : ℕ) : ℝ) - 2) * (((i + k : ℕ) : ℝ) - 1)))

/-- `γ_k = 1 - α + α[k p^{k-1} - (k-1) p^k]` (p. 16, Lemma 6). Used for `k ≥ 1`
(`γ_1 = 1`). -/
noncomputable def gammaK (p α : ℝ) (k : ℕ) : ℝ :=
  1 - α + α * ((k : ℝ) * p ^ (k - 1) - ((k : ℝ) - 1) * p ^ k)

/-- The sequence of times of Lemma 6 (p. 16): `t_1 = p`, `t_2 = p exp(α(1-p)²/p)`, and for
`k ≥ 2`, `t_{k+1}` is the positive real with `(t_k / t_{k+1})^{k-1} = γ_k / γ_{k-1}` (17), i.e.
`t_{k+1} = t_k (γ_{k-1}/γ_k)^{1/(k-1)}`. Index `0` is a placeholder (set to `p`) that the paper's
sequence does not have. -/
noncomputable def tSeq (p α : ℝ) : ℕ → ℝ
  | 0 => p
  | 1 => p
  | 2 => p * Real.exp (α * (1 - p) ^ 2 / p)
  | (k + 3) => tSeq p α (k + 2) *
      (gammaK p α (k + 1) / gammaK p α (k + 2)) ^ (1 / ((k : ℝ) + 1))

/-- `α̃` is a root of (19) in `(0, 1)` (p. 17, Lemma 7):
`ln p + α̃(1-p)²/p = ∑_{i=1}^{∞} ln(1 - α̃ + α̃[(i+1)p^i - i p^{i+1}]) / (i(i+1))`,
written with the summation index shifted by one (term `i` here is term `i + 1` of (19)). -/
def IsAlphaTilde (p a : ℝ) : Prop :=
  0 < a ∧ a < 1 ∧
    Real.log p + a * (1 - p) ^ 2 / p =
      ∑' i : ℕ, Real.log (1 - a + a * ((i + 2) * p ^ (i + 1) - (i + 1) * p ^ (i + 2))) /
        ((i + 1) * (i + 2))

/-- `α*` solves `∫_0^1 1 / (y(1 - ln y) + 1/α* - 1) dy = 1` with `0 < α* < 1` (p. 17,
preamble of Theorem 8). -/
def IsAlphaStar (s : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧ ∫ y in (0:ℝ)..1, 1 / (y * (1 - Real.log y) + 1 / s - 1) = 1

/-- The function `h(p, η)` of (26) (p. 35, proof of Theorem 8): the right-hand side of (19)
at `η` divided by its left-hand side, the summation index shifted by one as in `IsAlphaTilde`. -/
noncomputable def hFun (p η : ℝ) : ℝ :=
  (∑' i : ℕ, Real.log (1 - η + η * (((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2))) /
      (((i : ℝ) + 1) * ((i : ℝ) + 2))) /
    (Real.log p + η * (1 - p) ^ 2 / p)

end SampleDrivenOS.Limit


