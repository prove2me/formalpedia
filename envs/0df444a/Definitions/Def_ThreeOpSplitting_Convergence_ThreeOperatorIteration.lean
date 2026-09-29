-- Prove2me | Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration
-- name    : ThreeOpSplitting_Convergence_ThreeOperatorIteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:47:01.523179+00:00
-- url     : https://prove2.me/theorems/aaaa6838-0cb3-4baf-b863-5ef0a77b8b2c
-- title:
--   The Davis–Yin operator $T$ of Eq. (1.2), Algorithm 1, and the coefficients $\alpha$, $\tau_k$
-- statement:
--   Let $H$ be a real vector space, $\gamma \in \mathbb{R}$ and $T_1, T_2, C : H \to H$.
--
--   1. The **three-operator map** of Eq. (1.2) is
--   $$T := T_1 \circ (2T_2 - I - \gamma C \circ T_2) + I - T_2 ,$$
--   that is $Tz = T_1\big(2T_2z - z - \gamma C(T_2 z)\big) + z - T_2 z$. With $T_1 = J_{\gamma A}$ and $T_2 = J_{\gamma B}$ this is the Davis–Yin operator; with general $T_1, T_2$ it is the operator of Proposition 2.1.
--   2. **Algorithm 1.** Given resolvent maps $J_A, J_B$, the operator $C$, a stepsize $\gamma$, relaxation parameters $(\lambda_k)_{k\ge 0}$ and a starting point $z^0$, the iterates are defined for $k = 0, 1, \dots$ by
--   $$x_B^k = J_B(z^k), \qquad x_A^k = J_A\big(2x_B^k - z^k - \gamma C x_B^k\big), \qquad z^{k+1} = z^k + \lambda_k (x_A^k - x_B^k).$$
--   3. For $\varepsilon \in (0,1)$, the averagedness coefficient is $\alpha = 1/(2 - \varepsilon)$, and for a relaxation parameter $\lambda$
--   $$\tau(\lambda) = \lambda(1 - \lambda) + \frac{\lambda(1 - \alpha)}{\alpha},$$
--   which is the simplification of $\tau_k$ used in the proof of Theorem 2.1 (p. 836).
--
--   Every convergence statement of the mission is about these sequences.
--
--   **Formalization Note** The resolvents $J_A, J_B$ are arguments of the definitions; the theorems require them to satisfy the resolvent inclusion. The formula for $\tau$ is the one the proof of Theorem 2.1 uses, $\tau(\lambda) = \lambda(1 - \alpha\lambda)/\alpha$, not the printed $(1 - \lambda/\alpha)\lambda/\alpha$ of Corollary 2.1 and Theorem 2.1; the two differ, and the printed one is negative for part of the admissible range $\lambda \in (0, 1/\alpha)$.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 830 Eq. (1.2), p. 831 Algorithm 1, p. 834 Corollary 2.1 (α), p. 836 (τ_k in the proof of Theorem 2.1)

import Mathlib

namespace ThreeOpSplitting.Convergence

/-- The three-operator map of Eq. (1.2), `T := T₁ ∘ (2T₂ - I - γ C ∘ T₂) + I - T₂`;
with `T₁ = J_{γA}` and `T₂ = J_{γB}` it is the operator `T` of Davis–Yin, and with general
`T₁, T₂` it is the operator of Proposition 2.1. -/
def threeOp {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (T₁ T₂ C : H → H) : H → H :=
  fun z => T₁ ((2 : ℝ) • T₂ z - z - γ • C (T₂ z)) + z - T₂ z

/-- The sequence `z^k` of Algorithm 1: `z^0` given and
`z^{k+1} = z^k + λ_k (x_A^k - x_B^k)` with `x_B^k = J_B z^k`,
`x_A^k = J_A (2 x_B^k - z^k - γ C x_B^k)`. -/
def zSeq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (JA JB C : H → H) (lam : ℕ → ℝ) (z0 : H) : ℕ → H
  | 0 => z0
  | k + 1 =>
    let z := zSeq γ JA JB C lam z0 k
    z + lam k • (JA ((2 : ℝ) • JB z - z - γ • C (JB z)) - JB z)

/-- The sequence `x_B^k = J_B(z^k)` of Algorithm 1 (step 1). -/
def xBSeq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (JA JB C : H → H) (lam : ℕ → ℝ) (z0 : H) (k : ℕ) : H :=
  JB (zSeq γ JA JB C lam z0 k)

/-- The sequence `x_A^k = J_A(2 x_B^k - z^k - γ C x_B^k)` of Algorithm 1 (step 2). -/
def xASeq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    (γ : ℝ) (JA JB C : H → H) (lam : ℕ → ℝ) (z0 : H) (k : ℕ) : H :=
  JA ((2 : ℝ) • xBSeq γ JA JB C lam z0 k - zSeq γ JA JB C lam z0 k
    - γ • C (xBSeq γ JA JB C lam z0 k))

/-- The averagedness coefficient `α = 1/(2 - ε)` of Corollary 2.1 and Theorem 2.1. -/
noncomputable def alpha (ε : ℝ) : ℝ := 1 / (2 - ε)

/-- The coefficient `τ_k = λ_k(1 - λ_k) + λ_k(1 - α)/α` (with `α = alpha ε`), as used in the
proof of Theorem 2.1 (p. 836); it equals `λ_k(1 - α λ_k)/α`. -/
noncomputable def tau (ε l : ℝ) : ℝ := l * (1 - l) + l * (1 - alpha ε) / alpha ε

end ThreeOpSplitting.Convergence


