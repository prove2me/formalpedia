-- Prove2me | Definitions.Def_SelfDualLP_Complexity_PCSequence
-- name    : SelfDualLP_Complexity_PCSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:56.305803+00:00
-- url     : https://prove2.me/theorems/aa56f732-4228-4183-8f55-1de2ea72fdf3
-- title:
--   The Mizuno–Todd–Ye predictor–corrector iteration on (HLP), as a relation on sequences
-- statement:
--   Work under the choice (7). Given $z^k=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)$, a direction $d=(d_y,d_x,d_\tau,d_\theta,d_s,d_\kappa)$ **solves (11)–(12) with parameter** $\gamma$ if $d\in Q$ and
--   $$
--   \begin{pmatrix}X^kd_s+S^kd_x\\ \tau^kd_\kappa+\kappa^kd_\tau\end{pmatrix}=\gamma\mu^ke-\begin{pmatrix}X^ks^k\\ \tau^k\kappa^k\end{pmatrix},\qquad \mu^k=\frac{(x^k)^Ts^k+\tau^k\kappa^k}{n+1}.
--   $$
--   A sequence $(z^j)_{0\le j\le k}$ is a **predictor–corrector run of $k$ steps** if
--   1. $z^0=(0,e,1,1,e,1)$;
--   2. for even $k$ (predictor step) there is a solution $d$ of (11)–(12) with $\gamma=0$ such that the step size $\bar\alpha=\max\{\alpha: z^k+\alpha d\in\mathcal N(1/2)\}$ of (13) (with $2\beta=1/2$) exists and $z^{k+1}=z^k+\bar\alpha d$;
--   3. for odd $k$ (corrector step) there is a solution $d$ of (11)–(12) with $\gamma=1$ and $z^{k+1}=z^k+d$.
--
--   This is the algorithm whose iteration count Theorem 6 and Corollary 7 bound.
--
--   **Formalization Note** The iteration is a relation, not a function: when $A$ lacks full row rank, (11)–(12) do not determine $d_y$, and the paper assumes no rank condition. The maximum in (13) is required for predictor steps taken before the final iterate. No step is required after termination, so an instance reaching an exact solution at a step with no attained maximum still has a finite run.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), pp. 60–61, Predictor-Corrector Algorithm, (11), (12), (13); initial point from Theorem 2 (ii) under (7)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_Neighborhood

open Matrix

namespace SelfDualLP.Complexity

/-- The initial point `(y⁰, x⁰, τ⁰, θ⁰, s⁰, κ⁰) = (0, e, 1, 1, e, 1)` (Theorem 2 (ii) under (7)). -/
def initialPoint (m n : ℕ) : HLPPoint m n :=
  ⟨0, ones n, 1, 1, ones n, 1⟩

/-- `d` solves the linear system (11)–(12) at `z` with parameter `γ`:
`d ∈ Q`, `X d_s + S d_x = γμe − Xs` componentwise, and `τ d_κ + κ d_τ = γμ − τκ`,
with `μ = (xᵀs + τκ)/(n + 1)` evaluated at `z`. -/
def IsPCDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z d : HLPPoint m n) (γ : ℝ) : Prop :=
  InQ7 A b c d ∧
  (∀ j, z.x j * d.s j + z.s j * d.x j = γ * mu z - z.x j * z.s j) ∧
  z.τ * d.κ + z.κ * d.τ = γ * mu z - z.τ * z.κ

/-- `z` is a run of `k` steps of the Mizuno–Todd–Ye predictor–corrector algorithm applied to
(HLP) under (7) (pp. 60–61), read as a relation. The values after `k` are irrelevant:
* `z 0 = (0, e, 1, 1, e, 1)`;
* for even `k` (predictor step) there are a solution `d` of (11)–(12) with `γ = 0` and the step
  `ᾱ = max {α : z k + α d ∈ 𝒩(2β)}` with `2β = 1/2` (13) — the maximum must exist — with
  `z (k+1) = z k + ᾱ d`;
* for odd `k` (corrector step) there is a solution `d` of (11)–(12) with `γ = 1` and
  `z (k+1) = z k + d`. -/
def IsPCSequence {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : ℕ → HLPPoint m n) (k : ℕ) : Prop :=
  z 0 = initialPoint m n ∧
  ∀ j : ℕ, j < k → ∃ d : HLPPoint m n,
    (Even j ∧ IsPCDirection A b c (z j) d 0 ∧
      ∃ α : ℝ, IsGreatest {a : ℝ | Nbhd A b c (1 / 2) ((z j).move d a)} α ∧
        z (j + 1) = (z j).move d α) ∨
    (¬ Even j ∧ IsPCDirection A b c (z j) d 1 ∧ z (j + 1) = (z j).move d 1)

end SelfDualLP.Complexity


