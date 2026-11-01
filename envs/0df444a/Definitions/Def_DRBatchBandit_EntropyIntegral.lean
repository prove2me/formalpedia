-- Prove2me | Definitions.Def_DRBatchBandit_EntropyIntegral
-- name    : DRBatchBandit_EntropyIntegral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:09.314079+00:00
-- url     : https://prove2.me/theorems/02cf4d81-b1a2-471f-bf18-762715e40312
-- title:
--   $n$-point Hamming covering number $N_H^{(n)}(\epsilon,\Pi)$ and entropy integral $\kappa^{(n)}(\Pi)$ (Definition 5)
-- statement:
--   Let $\Pi$ be a class of policies $\mathcal X\to\{a^1,\dots,a^d\}$ and $x_1,\dots,x_n\in\mathcal X$ (Definition 5, p.16).
--
--   1. The Hamming distance is $H(\pi_1,\pi_2)=\frac1n\sum_{j=1}^n\mathbf 1\{\pi_1(x_j)\ne\pi_2(x_j)\}$.
--   2. $N_H^{(n)}(\epsilon,\Pi,\{x_1,\dots,x_n\})$ is the smallest $K$ such that some $\pi_1,\dots,\pi_K\in\Pi$ satisfy: for every $\pi\in\Pi$ there is $i$ with $H(\pi,\pi_i)\le\epsilon$.
--   3. $N_H^{(n)}(\epsilon,\Pi)=\sup\{N_H^{(n)}(\epsilon,\Pi,\{x_1,\dots,x_n\}):x_1,\dots,x_n\in\mathcal X\}$.
--   4. The entropy integral is
--   $$\kappa^{(n)}(\Pi)=\int_0^1\sqrt{\log N_H^{(n)}(\epsilon^2,\Pi)}\,d\epsilon.$$
--
--   Items 1–2 are the published `OfflinePolicyLearning.Regret.hammingDist` and `hammingCoverNumOn`; this file adds items 3–4. $\kappa^{(n)}(\Pi)$ is the complexity term in Theorem 2.
--
--   **Formalization Note** The $n$ points are a sequence `Fin n → X` (repetitions allowed), as in the proof, which applies the definition to the sample. $N_H^{(n)}$ is valued in $\mathbb N\cup\{\infty\}$ and $\kappa^{(n)}$ in $[0,\infty]$; both are finite because $N_H^{(n)}\le d^n$, and theorems use the real value. This is not the published `entropyIntegral`, which takes a supremum over all sample sizes.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Definition 5 p.16 (items 3–4). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming

open scoped ENNReal

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

/-- Definition 5, item 3 (arXiv:2006.05630v7, p.16): the `ε`-Hamming covering number of `Π` at
sample size `n`, `N_H⁽ⁿ⁾(ε, Π) = sup {N_H⁽ⁿ⁾(ε, Π, {x₁, …, x_n}) | x₁, …, x_n ∈ 𝒳}`.

**Formalization Note.** The `n` points are a sequence `x : Fin n → X` (repetitions allowed);
`hammingCoverNumOn` is the proper covering number of Definition 5, items 1–2. -/
noncomputable def hammingCoverNumN {X : Type*} {d : ℕ} (n : ℕ) (ε : ℝ) (Pol : Set (X → Fin d)) :
    ℕ∞ :=
  ⨆ x : Fin n → X, (hammingCoverNumOn ε Pol x : ℕ∞)

/-- Definition 5, item 4 (arXiv:2006.05630v7, p.16): the entropy integral
`κ⁽ⁿ⁾(Π) = ∫₀¹ √(log N_H⁽ⁿ⁾(ε², Π)) dε`.

**Formalization Note.** An extended nonnegative real (it is finite, since
`N_H⁽ⁿ⁾ ≤ dⁿ`); statements use `.toReal`. This is the `n`-point quantity, not the supremum over
all sample sizes of `OfflinePolicyLearning.Regret.entropyIntegral`. -/
noncomputable def entropyIntegralN {X : Type*} {d : ℕ} (n : ℕ) (Pol : Set (X → Fin d)) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc (0 : ℝ) 1,
    if hammingCoverNumN n (ε ^ 2) Pol = ⊤ then ⊤
    else ENNReal.ofReal (Real.sqrt (Real.log ((hammingCoverNumN n (ε ^ 2) Pol).toNat : ℝ)))

end DRBatchBandit


