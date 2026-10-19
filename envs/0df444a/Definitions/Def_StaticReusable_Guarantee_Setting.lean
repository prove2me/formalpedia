-- Prove2me | Definitions.Def_StaticReusable_Guarantee_Setting
-- name    : StaticReusable_Guarantee_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:16.637545+00:00
-- url     : https://prove2.me/theorems/3f2def5a-673c-4de0-86ab-d1f87e5b11dc
-- title:
--   §2, pp. 7–14 — reusable-resource pricing: instance class Ω, stationary policies, steady state, objectives (5)–(7), value (2), static rate (9), z-variables, R and R̃
-- statement:
--   A provider owns $C \ge 1$ identical units of a reusable resource. Customers arrive as a Poisson process of rate $\Lambda > 0$; at price $p$ a customer buys with effective rate $\lambda(p)$, and the provider works with the inverse demand $p(\lambda)$, so that the effective arrival rate $\lambda \in [0,\Lambda]$ is the decision. A served customer occupies one unit for an exponential time of mean $1/\mu$, pays $p(\lambda)$, and costs the provider $c > 0$; a customer who finds no free unit is lost.
--
--   **Instance class $\Omega$ (p. 9).** The standing assumptions are: $C \ge 1$; $\mu, \Lambda, c > 0$; weights $\alpha_1, \alpha_2, \alpha_3 \ge 0$ with $\alpha_1 + \alpha_2 + \alpha_3 = 1$; the profit rate $\lambda \mapsto \lambda(p(\lambda) - c)$ is concave on $[0,\Lambda]$; and $p$ is strictly decreasing on $(0,\Lambda]$ (the one-to-one correspondence between prices and rates, p. 8).
--
--   **Stationary policies (§2.3, p. 10).** A policy is a vector of rates $\lambda_1, \dots, \lambda_C \in [0,\Lambda]$, where $\lambda_i$ is used while $i$ units are free; the static policy with rate $l$ has $\lambda_1 = \dots = \lambda_C = l$. The number of free units is then a birth–death process whose steady-state probabilities are
--   $$\mathbb P_i(\pi) = \frac{\frac{C!}{(C-i)!}\prod_{j=i+1}^{C} \frac{\lambda_j}{\mu}}{\sum_{k=0}^{C} \frac{C!}{(C-k)!}\prod_{j=k+1}^{C}\frac{\lambda_j}{\mu}}, \qquad i = 0, \dots, C.$$
--
--   **Objectives (5)–(7) and value (2).**
--   $$\mathcal P^\pi = \sum_{i=1}^{C} \lambda_i (p(\lambda_i) - c)\,\mathbb P_i(\pi), \quad \mathcal{MS}^\pi = \sum_{i=1}^{C} \lambda_i\,\mathbb P_i(\pi), \quad \mathcal{SL}^\pi = \sum_{i=1}^{C} \mathbb P_i(\pi) = 1 - \mathbb P_0(\pi),$$
--   and the provider's value is $\alpha_1 \mathcal P^\pi + \alpha_2 \mathcal{MS}^\pi + \alpha_3 \mathcal{SL}^\pi$. The **myopic objective** of Lemma 1 is $\lambda(\alpha_1(p(\lambda) - c) + \alpha_2)$.
--
--   **Static rate (9).** For a policy with probabilities $\mathbb P_i$,
--   $$\tilde\lambda = \frac{\sum_{i=1}^{C} \lambda_i \mathbb P_i}{\sum_{i=1}^{C} \mathbb P_i},$$
--   the average rate over the states with a free unit.
--
--   **$z$-variables (§3.1, Step 2, p. 13).** $a_i := C!/(C-i)!$ for $i = 0, \dots, C$, and $z_i := \prod_{j=i}^{C} \lambda_j/\mu$ for $i = 1, \dots, C+1$, so $z_{C+1} = 1$. For a free vector $z_1, \dots, z_C$ (with $z_{C+1} := 1$) put $x := \sum_{k=1}^{C} a_k z_{k+1}$, $y := \sum_{k=2}^{C} a_k z_k$, $u := \sum_{k=1}^{C} a_k z_k = a_1 z_1 + y$, and
--   $$R(z_1,\dots,z_C) := \frac{\left(\sum_{k=0}^{C} a_k z_{k+1}\right)\sum_{i=1}^{C} a_i (u/x)^{C-i}}{x\sum_{i=0}^{C} a_i (u/x)^{C-i}}, \qquad \tilde R(z_1,\dots,z_C) := \frac{\left(\sum_{k=0}^{C} a_k z_{k+1}\right)\sum_{i=1}^{4} a_i u^{4-i} x^{i-1}}{\sum_{i=0}^{4} a_i u^{4-i} x^{i}}$$
--   (the second used for $C \ge 4$, Step 2b, p. 14).
--
--   These are the objects of every statement of the mission: the goal (Theorem 1) compares a static policy with an optimal stationary one through $\mathcal P$, $\mathcal{MS}$, $\mathcal{SL}$, and its proof runs through $\tilde\lambda$, $R$ and $\tilde R$.
--
--   **Formalization Note** The model is posed at the level of stationary state-dependent policies with the closed-form steady state above, as §2.3 does; the reduction from general non-anticipating policies and the long-run averages (1)–(2) are not formalized. A policy is a function `lam : ℕ → ℝ` read at $i = 1, \dots, C$ (other values are ignored), and `Policies C Λ` requires $\lambda_i \in [0,\Lambda]$ there. The normalizer of $\mathbb P_i$ is at least $C! > 0$ for every such policy, so no division is degenerate. A free $z$-vector is a function `z : ℕ → ℝ` read at $1, \dots, C$, and `zExt` supplies the convention $z_{C+1} = 1$; then $x \ge a_C = C! > 0$ whenever $z \ge 0$. `Standing` bundles the assumptions of $\Omega$. Lean identifiers: `profit`, `marketShare`, `serviceLevel`, `value`, `prob`, `weight`, `staticRate`, `myopic`, `a`, `zOf`, `zExt`, `uSum`, `xSum`, `ySum`, `R`, `Rt`.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, pp. 7–14, §2.1–§2.3, (2), (5)–(7), (9), Lemma 1 (myopic rate), §3.1 Step 2 (a_i, z_i, x, y, R, p. 13) and Step 2b (R̃, p. 14)

import Mathlib

namespace StaticReusable.Guarantee

open Finset

/-- The instance class `Ω` of §2.2, p. 9, together with the model assumptions of §2.1, pp. 7–8.
`C ≥ 1` units, service rate `μ > 0`, maximal (Poisson) arrival rate `Λ > 0`, cost `c > 0`,
inverse demand `p`, weights `α₁, α₂, α₃ ≥ 0` summing to one, the profit rate `λ (p λ - c)`
concave in `λ` on `[0, Λ]`, and the one-to-one price/rate correspondence (`p` strictly
decreasing on `(0, Λ]`). -/
structure Standing (C : ℕ) (μ Λ c : ℝ) (p : ℝ → ℝ) (α₁ α₂ α₃ : ℝ) : Prop where
  one_le_C : 1 ≤ C
  μ_pos : 0 < μ
  Λ_pos : 0 < Λ
  c_pos : 0 < c
  α₁_nonneg : 0 ≤ α₁
  α₂_nonneg : 0 ≤ α₂
  α₃_nonneg : 0 ≤ α₃
  α_sum : α₁ + α₂ + α₃ = 1
  concave : ConcaveOn ℝ (Set.Icc 0 Λ) (fun l => l * (p l - c))
  strictAnti : StrictAntiOn p (Set.Ioc 0 Λ)

/-- Stationary state-dependent pricing policies (§2.3, p. 10): an effective arrival rate
`lam i ∈ [0, Λ]` for each state `i = 1, …, C` (number of free units). Values of `lam`
outside `1, …, C` are ignored by every objective. -/
def Policies (C : ℕ) (Λ : ℝ) : Set (ℕ → ℝ) :=
  {lam | ∀ i ∈ Finset.Icc 1 C, lam i ∈ Set.Icc 0 Λ}

/-- Unnormalized steady-state weight of state `i` (§2.3, p. 10):
`C!/(C-i)! · ∏_{j=i+1}^{C} λ_j/μ`. -/
noncomputable def weight (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) (i : ℕ) : ℝ :=
  (C.descFactorial i : ℝ) * ∏ j ∈ Finset.Icc (i + 1) C, lam j / μ

/-- Steady-state probability `ℙ_i(π)` of having `i` free units (§2.3, p. 10). -/
noncomputable def prob (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) (i : ℕ) : ℝ :=
  weight C μ lam i / ∑ k ∈ Finset.range (C + 1), weight C μ lam k

/-- Long-run profit rate (5). -/
noncomputable def profit (C : ℕ) (μ : ℝ) (p : ℝ → ℝ) (c : ℝ) (lam : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 C, lam i * (p (lam i) - c) * prob C μ lam i

/-- Market share (6). -/
noncomputable def marketShare (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 C, lam i * prob C μ lam i

/-- Service level (7): `∑_{i=1}^{C} ℙ_i(π) = 1 - ℙ_0(π)`. -/
noncomputable def serviceLevel (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 C, prob C μ lam i

/-- The weighted objective (2): `α₁ P^π + α₂ MS^π + α₃ SL^π`. -/
noncomputable def value (C : ℕ) (μ : ℝ) (p : ℝ → ℝ) (c α₁ α₂ α₃ : ℝ) (lam : ℕ → ℝ) : ℝ :=
  α₁ * profit C μ p c lam + α₂ * marketShare C μ lam + α₃ * serviceLevel C μ lam

/-- The static rate `λ̃` of (9): `∑_{i=1}^C λ_i ℙ_i / ∑_{i=1}^C ℙ_i`. -/
noncomputable def staticRate (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 C, lam i * prob C μ lam i) / ∑ i ∈ Finset.Icc 1 C, prob C μ lam i

/-- The myopic objective of Lemma 1, p. 11: `λ (α₁ (p(λ) - c) + α₂)`. -/
noncomputable def myopic (p : ℝ → ℝ) (c α₁ α₂ : ℝ) (l : ℝ) : ℝ :=
  l * (α₁ * (p l - c) + α₂)

/-- `a_i := C!/(C-i)!` (§3.1, Step 2, p. 13). -/
def a (C i : ℕ) : ℝ := (C.descFactorial i : ℝ)

/-- `z_i := ∏_{j=i}^{C} λ_j/μ` (§3.1, Step 2, p. 13); `z_{C+1} = 1` (empty product). -/
noncomputable def zOf (C : ℕ) (μ : ℝ) (lam : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc i C, lam j / μ

/-- A free vector `z_1, …, z_C` extended by the convention `z_{C+1} = 1`. -/
def zExt (C : ℕ) (z : ℕ → ℝ) (k : ℕ) : ℝ := if k ≤ C then z k else 1

/-- `∑_{k=1}^{C} a_k z_k` (`= a_1 z_1 + y`). -/
noncomputable def uSum (C : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 C, a C k * zExt C z k

/-- `x := ∑_{k=1}^{C} a_k z_{k+1}` (p. 13). -/
noncomputable def xSum (C : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 C, a C k * zExt C z (k + 1)

/-- `y := ∑_{k=2}^{C} a_k z_k` (p. 13). -/
noncomputable def ySum (C : ℕ) (z : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 C, a C k * zExt C z k

/-- The service-level ratio function `R(z_1, …, z_C)` (§3.1, Step 2, p. 13). -/
noncomputable def R (C : ℕ) (z : ℕ → ℝ) : ℝ :=
  ((∑ k ∈ Finset.range (C + 1), a C k * zExt C z (k + 1)) *
      ∑ i ∈ Finset.Icc 1 C, a C i * (uSum C z / xSum C z) ^ (C - i)) /
    (xSum C z * ∑ i ∈ Finset.range (C + 1), a C i * (uSum C z / xSum C z) ^ (C - i))

/-- The truncated lower bound `R̃(z_1, …, z_C)` (§3.1, Step 2b, p. 14), used for `C ≥ 4`. -/
noncomputable def Rt (C : ℕ) (z : ℕ → ℝ) : ℝ :=
  ((∑ k ∈ Finset.range (C + 1), a C k * zExt C z (k + 1)) *
      ∑ i ∈ Finset.Icc 1 4, a C i * uSum C z ^ (4 - i) * xSum C z ^ (i - 1)) /
    ∑ i ∈ Finset.range 5, a C i * uSum C z ^ (4 - i) * xSum C z ^ i

end StaticReusable.Guarantee


