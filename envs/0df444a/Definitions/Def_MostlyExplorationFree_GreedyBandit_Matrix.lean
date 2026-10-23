-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
-- name    : MostlyExplorationFree_GreedyBandit_Matrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:50.758406+00:00
-- url     : https://prove2.me/theorems/509ecb01-ee09-4f1a-8b22-30584136a09f
-- title:
--   Matrix notation — ℓ₂ norm, λ_min and λ_max as Rayleigh extrema, entrywise conditional expectation of a matrix
-- statement:
--   Linear-algebra notation used throughout Bastani, Bayati and Khosravi's analysis of the Greedy Bandit. Vectors live in $\mathbb R^d$ and matrices in $\mathbb R^{d\times d}$.
--
--   1. The **Euclidean norm** of $x \in \mathbb R^d$ is $\|x\|_2 = \sqrt{x^\top x}$.
--   2. The **minimum and maximum eigenvalue** of a matrix $A$ are the extreme values of its Rayleigh quotient over the unit sphere:
--   $$
--   \lambda_{\min}(A) = \inf_{v^\top v = 1} v^\top A v, \qquad \lambda_{\max}(A) = \sup_{v^\top v = 1} v^\top A v .
--   $$
--   For a symmetric matrix these are its smallest and largest eigenvalues.
--   3. For a random matrix $M$ on a probability space and a sub-$\sigma$-algebra $\mathcal H$, the **conditional expectation** $\mathbb E[M \mid \mathcal H]$ is taken entry by entry.
--
--   These are the objects in which the paper's assumptions (covariate diversity bounds $\lambda_{\min}$ of a second-moment matrix) and its concentration lemmas (matrix Chernoff bounds $\lambda_{\min}$ of a sum of random matrices) are written.
--
--   **Formalization Note** Vectors are `Fin d → ℝ`. Lean's default norm on that type is the sup norm, so the ℓ₂ norm is defined separately. The Rayleigh infimum avoids attaching a symmetry proof to every matrix; on `d = 0` the unit sphere is empty and the infimum is the junk value `0`, so every statement using `λ_min` assumes `d ≥ 1`.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 8 (ℓ₂ ball notation), p. 9 Assumption 3 (λ_min), p. 15 (λ_max), p. 39 Lemma 9 (E[X_k | H_{k−1}])

import Mathlib

namespace MostlyExplorationFree.GreedyBandit

open Matrix MeasureTheory

/-- The Euclidean (ℓ₂) norm `‖x‖₂ = √(xᵀx)` of a vector `x ∈ ℝ^d`.
(Mathlib's `‖·‖` on `Fin d → ℝ` is the sup norm, so it is not used.) -/
noncomputable def l2norm {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (x ⬝ᵥ x)

/-- `λ_min(A)`: the infimum of the Rayleigh quotient `vᵀAv` over unit vectors `v`
(`vᵀv = 1`). For a symmetric matrix this is its smallest eigenvalue. -/
noncomputable def lambdaMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨅ v : {v : Fin d → ℝ // v ⬝ᵥ v = 1}, v.1 ⬝ᵥ (A *ᵥ v.1)

/-- `λ_max(A)`: the supremum of the Rayleigh quotient `vᵀAv` over unit vectors `v`.
For a symmetric matrix this is its largest eigenvalue. -/
noncomputable def lambdaMax {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ v : {v : Fin d → ℝ // v ⬝ᵥ v = 1}, v.1 ⬝ᵥ (A *ᵥ v.1)

/-- Entrywise conditional expectation `E[M | m]` of a matrix-valued random variable `M`
with respect to a sub-σ-algebra `m`. -/
noncomputable def condExpMatrix {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}
    (m : MeasurableSpace Ω) (P : @Measure Ω mΩ) (M : Ω → Matrix (Fin d) (Fin d) ℝ) :
    Ω → Matrix (Fin d) (Fin d) ℝ :=
  fun ω => Matrix.of fun a b => condExp m P (fun ω' => M ω' a b) ω

end MostlyExplorationFree.GreedyBandit


