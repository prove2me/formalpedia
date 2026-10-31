-- Prove2me | Definitions.Def_LinearZeroSumMG_QClass
-- name    : LinearZeroSumMG_QClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:13.750996+00:00
-- url     : https://prove2.me/theorems/ab8da460-6534-4aea-8c99-72a5d03a3237
-- title:
--   The function class $\mathcal Q$ of (5)
-- statement:
--   For an episode $k$, the class $\mathcal Q$ consists of all functions $Q:\mathcal S\times\mathcal A\times\mathcal A\to\mathbb R$ of the form
--   $$
--   Q(x,a,b)=\Pi_H\Big\{\langle w,\phi(x,a,b)\rangle+\rho\beta\sqrt{\phi(x,a,b)^\top A\,\phi(x,a,b)}\Big\},
--   $$
--   with parameters $(w,A,\rho)\in\mathbb R^d\times\mathbb R^{d\times d}\times\{\pm1\}$ satisfying $\|w\|\le2H\sqrt{dk}$ and $\|A\|_F\le\beta^2\sqrt d$.
--
--   The upper and lower estimates $\overline Q^k_h$ (with $\rho=1$) and $\underline Q^k_h$ (with $\rho=-1$) produced by Algorithm 1 have this form with $A=(\Lambda^k_h)^{-1}$; Algorithm 2 rounds them into a finite $\varepsilon$-net of $\mathcal Q$.
--
--   **Formalization Note** The class depends on $k$ through the bound on $\|w\|$. $A$ is not required to be positive semidefinite, as printed; the square root is `Real.sqrt` ($0$ on negative arguments), which adds only functions the algorithm never produces.
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, §3.2, (5), p.11

import Mathlib
import Definitions.Def_LinearZeroSumMG_clip

namespace LinearZeroSumMG

open Matrix

variable {S A : Type*} {d : ℕ}

/-- The function `Q(x, a, b) = Π_H{⟨w, φ(x, a, b)⟩ + ρβ√(φ(x, a, b)ᵀ M φ(x, a, b))}` with parameters
`(w, M, ρ)` (the parametric form (5), arXiv:2002.07066v3, p.11; also lines 8–9 of Algorithm 1,
p.10, with `M = (Λ^k_h)⁻¹` and `ρ = ±1`). -/
noncomputable def qFun (φ : S → A → A → Fin d → ℝ) (H : ℕ) (β ρ : ℝ) (w : Fin d → ℝ)
    (M : Fin d → Fin d → ℝ) : S → A → A → ℝ :=
  fun x a b => clip H (w ⬝ᵥ φ x a b + ρ * β * Real.sqrt (φ x a b ⬝ᵥ (Matrix.of M) *ᵥ φ x a b))

/-- **The function class `𝒬` of (5), for episode `k`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, §3.2, (5), p.11: "Let `𝒬` be the
class of functions `Q : 𝒮 × 𝒜 × 𝒜 → ℝ` with the parametric form
`Q(x, a, b) = Π_H{⟨w, φ(x, a, b)⟩ + ρβ√(φ(x, a, b)ᵀAφ(x, a, b))}`, (5)
where the parameters `(w, A, ρ) ∈ ℝ^d × ℝ^{d×d} × {±1}` satisfy `‖w‖ ≤ 2H√(dk)` and
`‖A‖_F ≤ β²√d`."

`QClass φ H β k` is the set of all `qFun φ H β ρ w M` with `ρ ∈ {1, −1}`, `‖w‖ ≤ 2H√(dk)` and
`‖M‖_F ≤ β²√d`.

**Formalization Note**
- The class depends on the episode `k` through the bound on `‖w‖`, so there is one class per `k`.
- `M` is not required to be positive semidefinite, as printed; `√` is `Real.sqrt`, which is `0` on
  negative arguments. This only adds functions that the algorithm never produces.
- `d` is the length of the feature vectors `φ(x, a, b) ∈ ℝ^d`. -/
def QClass (φ : S → A → A → Fin d → ℝ) (H : ℕ) (β : ℝ) (k : ℕ) : Set (S → A → A → ℝ) :=
  {Q | ∃ (w : Fin d → ℝ) (M : Fin d → Fin d → ℝ) (ρ : ℝ), (ρ = 1 ∨ ρ = -1) ∧
    ApproxVI.euclNorm w ≤ 2 * H * Real.sqrt (d * k) ∧ frobNorm M ≤ β ^ 2 * Real.sqrt d ∧
    Q = qFun φ H β ρ w M}

end LinearZeroSumMG


