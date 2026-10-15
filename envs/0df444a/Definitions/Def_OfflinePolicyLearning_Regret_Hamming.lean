-- Prove2me | Definitions.Def_OfflinePolicyLearning_Regret_Hamming
-- name    : OfflinePolicyLearning_Regret_Hamming
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:10.169973+00:00
-- url     : https://prove2.me/theorems/86a117fc-af23-48dd-923c-7c03d18c9fbd
-- title:
--   Definition 4, p. 13 — Hamming distance, Hamming covering numbers N_H(ε, Π, {x_1,…,x_n}) and N_H(ε, Π), entropy integral κ(Π)
-- statement:
--   Let $\mathcal X$ be a feature set and let the $d$ actions be labelled $1,\dots,d$. A (deterministic) policy is a map $\pi:\mathcal X\to\{1,\dots,d\}$ and a policy class is a set $\Pi$ of such maps.
--
--   1. **Hamming distance.** For points $x_1,\dots,x_m\in\mathcal X$ (repetitions allowed) and policies $\pi_1,\pi_2$,
--   $$H(\pi_1,\pi_2)=\frac{1}{m}\sum_{j=1}^m \mathbf 1\{\pi_1(x_j)\neq\pi_2(x_j)\}.$$
--   2. **Covering number on a point set.** $N_H(\varepsilon,\Pi,\{x_1,\dots,x_m\})$ is the smallest number $K$ of policies $c_1,\dots,c_K\in\Pi$ such that every $\pi\in\Pi$ has $H(\pi,c_i)\le\varepsilon$ for some $i$.
--   3. **Covering number.** $N_H(\varepsilon,\Pi)=\sup_{m\ge1}\sup_{x_1,\dots,x_m}N_H(\varepsilon,\Pi,\{x_1,\dots,x_m\})$, a value in $\{0,1,2,\dots\}\cup\{\infty\}$.
--   4. **Entropy integral.**
--   $$\kappa(\Pi)=\int_0^1\sqrt{\log N_H(\varepsilon^2,\Pi)}\,d\varepsilon,$$
--   a value in $[0,\infty]$.
--
--   The entropy integral $\kappa(\Pi)$ is the complexity measure of the policy class in the paper's regret bound.
--
--   **Formalization Note** Point sets are sequences $x:\mathrm{Fin}\ m\to\mathcal X$, so repeated points are allowed, as in the paper's proofs. The cover is proper (centres in $\Pi$, as in Definition 4's "the minimum number of policies in $\Pi$"). The integrand is $+\infty$ where $N_H(\varepsilon^2,\Pi)=\infty$, and $\kappa(\Pi)$ is a Lebesgue integral in $[0,\infty]$; for the empty class every covering number is $0$ and the integrand is $0$.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 13, Definition 4

import Mathlib

open scoped ENNReal

namespace OfflinePolicyLearning.Regret

/-- Definition 4, item 1: the Hamming distance between two deterministic policies on the points
`x 0, …, x (m-1)` (repetitions allowed). -/
noncomputable def hammingDist {X : Type*} {d m : ℕ} (x : Fin m → X) (π₁ π₂ : X → Fin d) : ℝ :=
  ((Finset.univ.filter fun j => π₁ (x j) ≠ π₂ (x j)).card : ℝ) / m

/-- Definition 4, item 2: the `ε`-Hamming covering number of `Pol` on the points `x`
(a proper cover: the centres lie in `Pol`). -/
noncomputable def hammingCoverNumOn {X : Type*} {d m : ℕ} (ε : ℝ) (Pol : Set (X → Fin d))
    (x : Fin m → X) : ℕ :=
  sInf {K : ℕ | ∃ c : Fin K → (X → Fin d), (∀ i, c i ∈ Pol) ∧
    ∀ π ∈ Pol, ∃ i, hammingDist x π (c i) ≤ ε}

/-- Definition 4, item 3: the `ε`-Hamming covering number of `Pol`, a supremum over all finite
point sequences of length `m ≥ 1`. -/
noncomputable def hammingCoverNum {X : Type*} {d : ℕ} (ε : ℝ) (Pol : Set (X → Fin d)) : ℕ∞ :=
  ⨆ (m : ℕ) (_ : 1 ≤ m) (x : Fin m → X), (hammingCoverNumOn ε Pol x : ℕ∞)

/-- Definition 4, item 4: the entropy integral `κ(Π) = ∫₀¹ √(log N_H(ε², Π)) dε`, as an extended
nonnegative real (`⊤` when some covering number is infinite on a set of positive measure). -/
noncomputable def entropyIntegral {X : Type*} {d : ℕ} (Pol : Set (X → Fin d)) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc (0 : ℝ) 1,
    if hammingCoverNum (ε ^ 2) Pol = ⊤ then ⊤
    else ENNReal.ofReal (Real.sqrt (Real.log ((hammingCoverNum (ε ^ 2) Pol).toNat : ℝ)))

end OfflinePolicyLearning.Regret


