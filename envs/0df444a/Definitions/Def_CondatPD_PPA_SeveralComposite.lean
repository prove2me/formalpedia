-- Prove2me | Definitions.Def_CondatPD_PPA_SeveralComposite
-- name    : CondatPD_PPA_SeveralComposite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:34:32.318418+00:00
-- url     : https://prove2.me/theorems/b0c970f5-331e-4102-84e1-0df455a0dfe3
-- title:
--   §5, pp. 13–15 — solutions of (48) and Algorithms 5.1–5.2 for m composite terms
-- statement:
--   Let $\mathcal X$ and $\mathcal Y_1,\dots,\mathcal Y_m$ be real Hilbert spaces, $L_i:\mathcal X\to\mathcal Y_i$ bounded linear operators, $F:\mathcal X\to\mathbb R$, $G:\mathcal X\to\mathbb R\cup\{+\infty\}$ and $H_i:\mathcal Y_i\to\mathbb R\cup\{+\infty\}$. This module fixes the objects of the extension of the method to problem (45), $\min_x F(x)+G(x)+\sum_{i=1}^m H_i(L_ix)$.
--
--   1. **Solutions of (48).** $(\hat x,\hat y_1,\dots,\hat y_m)$ solves
--   $$0\in\partial G(\hat x)+\sum_{i=1}^m L_i^*\hat y_i+\nabla F(\hat x),\qquad 0\in -L_i\hat x+\partial H_i^*(\hat y_i)\quad(i=1,\dots,m).$$
--   2. **Algorithm 5.1 (55).** With $P_G=\mathrm{prox}_{\tau G}$, $P_{H_i}=\mathrm{prox}_{\sigma H_i^*}$, relaxation $(\rho_n)$ and errors $e_{F,n},e_{G,n}\in\mathcal X$, $e_{H_i,n}\in\mathcal Y_i$, a run satisfies for every $n$
--   $$\tilde x_{n+1}=P_G\Big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau\sum_{i=1}^m L_i^*y_{i,n}\Big)+e_{G,n},\qquad x_{n+1}=\rho_n\tilde x_{n+1}+(1-\rho_n)x_n,$$
--   $$\tilde y_{i,n+1}=P_{H_i}\big(y_{i,n}+\sigma L_i(2\tilde x_{n+1}-x_n)\big)+e_{H_i,n},\qquad y_{i,n+1}=\rho_n\tilde y_{i,n+1}+(1-\rho_n)y_{i,n}.$$
--   3. **Algorithm 5.2 (56).** For every $n$: $\tilde y_{i,n+1}=P_{H_i}(y_{i,n}+\sigma L_ix_n)+e_{H_i,n}$ and $y_{i,n+1}=\rho_n\tilde y_{i,n+1}+(1-\rho_n)y_{i,n}$ for each $i$; then
--   $$\tilde x_{n+1}=P_G\Big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau\sum_{i=1}^m L_i^*(2\tilde y_{i,n+1}-y_{i,n})\Big)+e_{G,n},\qquad x_{n+1}=\rho_n\tilde x_{n+1}+(1-\rho_n)x_n.$$
--
--   These are the objects of Theorem 5.2, the several-composite-term version of Theorem 3.2.
--
--   **Formalization Note** The dual variable is a dependent function $y_n\in\prod_i\mathcal Y_i$ indexed by `Fin m`. Step 3 of Algorithm 5.2 is printed as $L_i^*(2\tilde y_{n+1}-y_n)$, without the index $i$ inside the parentheses; the indexed form above is the one meant (it is the substitution of (50) into Algorithm 3.2) and is the one formalized. The conjugate $H_i^*$ is the published `MoreauProx.Characterization.conj`.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), pp. 13–15, (45), (48), Algorithms 5.1–5.2 (55)–(56)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_CondatPD_PPA_Setting

open InnerProductSpace

namespace CondatPD.PPA

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {m : ℕ} {Y : Fin m → Type*} [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace ℝ (Y i)]
  [∀ i, CompleteSpace (Y i)]

/-- `(x̂, ŷ₁, …, ŷₘ)` solves the monotone inclusion (48) (Condat 2013, §5, p. 14):
`0 ∈ ∂G(x̂) + Σᵢ Lᵢ*ŷᵢ + ∇F(x̂)` and, for every `i`, `0 ∈ −Lᵢx̂ + ∂Hᵢ*(ŷᵢ)`; written as
`−Σᵢ Lᵢ*ŷᵢ − ∇F(x̂) ∈ ∂G(x̂)` and `Lᵢx̂ ∈ ∂Hᵢ*(ŷᵢ)`. -/
def IsSol48 (F : X → ℝ) (G : X → EReal) (H : ∀ i, Y i → EReal) (L : ∀ i, X →L[ℝ] Y i)
    (xh : X) (yh : ∀ i, Y i) : Prop :=
  InertialFB.IFB.IsSubgradient G xh
      (-(∑ i, ContinuousLinearMap.adjoint (L i) (yh i)) - gradient F xh) ∧
    ∀ i, InertialFB.IFB.IsSubgradient (MoreauProx.Characterization.conj (H i)) (yh i) (L i xh)

/-- A run `(xₙ, y_{1,n}, …, y_{m,n})` of Algorithm 5.1 (p. 15, (55)), with `PG = prox_{τG}` and
`PH i = prox_{σHᵢ*}`: for every `n`,
1. `x̃ₙ₊₁ = PG(xₙ − τ(∇F(xₙ) + e_{F,n}) − τ Σᵢ Lᵢ*y_{i,n}) + e_{G,n}`,
2. `xₙ₊₁ = ρₙx̃ₙ₊₁ + (1 − ρₙ)xₙ`,
3. for every `i`, `ỹ_{i,n+1} = PHᵢ(y_{i,n} + σLᵢ(2x̃ₙ₊₁ − xₙ)) + e_{Hᵢ,n}`,
4. for every `i`, `y_{i,n+1} = ρₙỹ_{i,n+1} + (1 − ρₙ)y_{i,n}`. -/
def IsAlg51Run (F : X → ℝ) (L : ∀ i, X →L[ℝ] Y i) (τ σ : ℝ) (PG : X → X)
    (PH : ∀ i, Y i → Y i) (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → ∀ i, Y i)
    (x : ℕ → X) (y : ℕ → ∀ i, Y i) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ∑ i, ContinuousLinearMap.adjoint (L i) (y n i)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧
      ∀ i, y (n + 1) i =
        ρ n • (PH i (y n i + σ • L i ((2 : ℝ) • xt - x n)) + eH n i) + (1 - ρ n) • y n i

/-- A run of Algorithm 5.2 (p. 15, (56)): for every `n`,
1. for every `i`, `ỹ_{i,n+1} = PHᵢ(y_{i,n} + σLᵢxₙ) + e_{Hᵢ,n}`,
2. for every `i`, `y_{i,n+1} = ρₙỹ_{i,n+1} + (1 − ρₙ)y_{i,n}`,
3. `x̃ₙ₊₁ = PG(xₙ − τ(∇F(xₙ) + e_{F,n}) − τ Σᵢ Lᵢ*(2ỹ_{i,n+1} − y_{i,n})) + e_{G,n}`,
4. `xₙ₊₁ = ρₙx̃ₙ₊₁ + (1 − ρₙ)xₙ`.
Step 3 is printed without the index `i` on `ỹₙ₊₁ − yₙ`; the indexed form is the one meant. -/
def IsAlg52Run (F : X → ℝ) (L : ∀ i, X →L[ℝ] Y i) (τ σ : ℝ) (PG : X → X)
    (PH : ∀ i, Y i → Y i) (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → ∀ i, Y i)
    (x : ℕ → X) (y : ℕ → ∀ i, Y i) : Prop :=
  ∀ n : ℕ,
    let yt : ∀ i, Y i := fun i => PH i (y n i + σ • L i (x n)) + eH n i
    (∀ i, y (n + 1) i = ρ n • yt i + (1 - ρ n) • y n i) ∧
      x (n + 1) = ρ n • (PG (x n - τ • (gradient F (x n) + eF n)
        - τ • ∑ i, ContinuousLinearMap.adjoint (L i) ((2 : ℝ) • yt i - y n i)) + eG n)
        + (1 - ρ n) • x n

end CondatPD.PPA


