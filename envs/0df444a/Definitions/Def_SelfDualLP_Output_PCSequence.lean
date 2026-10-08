-- Prove2me | Definitions.Def_SelfDualLP_Output_PCSequence
-- name    : SelfDualLP_Output_PCSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:26:24.946011+00:00
-- url     : https://prove2.me/theorems/3b2b45b6-891c-4bbe-9420-67dfceefdaf8
-- title:
--   The Mizuno–Todd–Ye predictor–corrector sequence on (HLP), with β = 1/4
-- statement:
--   Work with (HLP) under the choice (7) and set $\beta=1/4$. Given an interior point $z^k=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)$ and $\gamma\in\{0,1\}$, a direction $d=(d_y,d_x,d_\tau,d_\theta,d_s,d_\kappa)$ **solves (11)–(12)** if
--
--   $$
--   d\in Q,\qquad
--   \begin{pmatrix} X^kd_s+S^kd_x\\ \tau^kd_\kappa+\kappa^kd_\tau\end{pmatrix}=\gamma\mu^ke-\begin{pmatrix}X^ks^k\\ \tau^k\kappa^k\end{pmatrix},
--   $$
--
--   with $\mu^k=((x^k)^Ts^k+\tau^k\kappa^k)/(n+1)$. A sequence $(z^k)_{k\ge0}$ is a **predictor–corrector sequence** if
--
--   1. $z^0=(0,e,1,1,e,1)$;
--   2. for even $k$ (predictor step) there is a direction $d$ solving (11)–(12) with $\gamma=0$ and
--   $$\bar\alpha=\max\{\alpha : z^k+\alpha d\in\mathcal N(2\beta)\}\qquad(13)$$
--   exists, and $z^{k+1}=z^k+\bar\alpha d$;
--   3. for odd $k$ (corrector step) there is a direction $d$ solving (11)–(12) with $\gamma=1$, and $z^{k+1}=z^k+d$.
--
--   Theorem 8 describes the behaviour of $\tau^k$, $\theta^k$ and $\kappa^k$ along every such sequence.
--
--   **Formalization Note** The iteration is a relation rather than a function: when $A$ does not have full row rank, (11)–(12) does not determine $d_y$, and the paper makes no rank assumption. The step size is required to be the greatest element of the set in (13), as printed; if that maximum is not attained, the sequence cannot be continued and is not a predictor–corrector sequence. The constant $\beta=1/4$ is a named definition so that $1-2\beta$ and $1+2\beta$ appear in the statements as printed.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), pp. 60–61, Predictor-Corrector Algorithm, (11)–(13); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Output_Neighborhood

open Matrix

namespace SelfDualLP.Output

/-- The algorithm's parameter `β = 1/4` (p. 60): predictor steps start in `𝒩(β)` and stay in
`𝒩(2β)`. -/
noncomputable def beta : ℝ := 1 / 4

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

/-- `z` is a sequence of iterates of the Mizuno–Todd–Ye predictor–corrector algorithm applied to
(HLP) under (7) (pp. 60–61), read as a relation:
* `z 0 = (0, e, 1, 1, e, 1)`;
* for even `k` (predictor step) there are a solution `d` of (11)–(12) with `γ = 0` and the step
  `ᾱ = max {α : z k + α d ∈ 𝒩(2β)}` (13) — the maximum must exist — with `z (k+1) = z k + ᾱ d`;
* for odd `k` (corrector step) there is a solution `d` of (11)–(12) with `γ = 1` and
  `z (k+1) = z k + d`. -/
def IsPCSequence {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : ℕ → HLPPoint m n) : Prop :=
  z 0 = initialPoint m n ∧
  ∀ k, ∃ d : HLPPoint m n,
    (Even k ∧ IsPCDirection A b c (z k) d 0 ∧
      ∃ α : ℝ, IsGreatest {a : ℝ | Nbhd A b c (2 * beta) ((z k).move d a)} α ∧
        z (k + 1) = (z k).move d α) ∨
    (¬ Even k ∧ IsPCDirection A b c (z k) d 1 ∧ z (k + 1) = (z k).move d 1)

end SelfDualLP.Output


