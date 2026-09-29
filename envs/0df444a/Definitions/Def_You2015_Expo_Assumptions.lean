-- Prove2me | Definitions.Def_You2015_Expo_Assumptions
-- name    : You2015_Expo_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:09:05.20016+00:00
-- url     : https://prove2.me/theorems/f8a62ea1-d3d5-4130-b0ae-b2bf1c061a17
-- title:
--   Assumptions 2.1, 2.2, 3.1, 4.1, the class C^{2,1}, the operator 𝓛U of (3.2), and condition (3.5) on the observation interval τ
-- statement:
--   Let $S=\{1,\dots,N\}$, $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$, with $|x|$ the Euclidean norm and $|A|=\sqrt{\operatorname{trace}(A^TA)}$ the trace norm of a matrix.
--
--   1. **Assumption 2.1.** $K_1,K_2>0$; $f$ and $g$ are locally Lipschitz continuous in $x$: for every $R>0$ there is $L\ge0$ with
--   $$|f(x,i,t)-f(y,i,t)|\le L|x-y|,\qquad |g(x,i,t)-g(y,i,t)|\le L|x-y|$$
--   whenever $|x|,|y|\le R$, for all $i\in S$, $t\ge0$; and the linear growth condition
--   $$|f(x,i,t)|\le K_1|x|,\qquad |g(x,i,t)|\le K_2|x|\tag{2.4}$$
--   holds for all $(x,i,t)$.
--
--   2. **Assumption 2.2.** $K_3>0$ and for all $x,y,i,t$
--   $$|u(x,i,t)-u(y,i,t)|\le K_3|x-y|,\tag{2.6}$$
--   $$u(0,i,t)=0.\tag{2.7}$$
--
--   3. **The class $C^{2,1}(\mathbb R^n\times S\times\mathbb R_+;\mathbb R_+)$** of nonnegative functions $U(x,i,t)$ continuously twice differentiable in $x$ and once in $t$. Its derivatives $U_t$, $U_x$ (the gradient, as a row vector) and $U_{xx}$ (the Hessian) are carried along with $U$: $U\ge0$, $U_x(x,i,t)$ is the derivative of $U(\cdot,i,t)$ at $x$, $U_{xx}(x,i,t)$ is the derivative of $U_x(\cdot,i,t)$ at $x$, $U_t(x,i,t)$ is the derivative of $U(x,i,\cdot)$ at $t$ (one-sided at $t=0$), and $U,U_t,U_x,U_{xx}$ are continuous in $(x,t)$ for each $i$.
--
--   4. **The operator $\mathcal LU$** of (3.2):
--   $$\mathcal LU(x,i,t)=U_t(x,i,t)+U_x(x,i,t)\big[f(x,i,t)+u(x,i,t)\big]+\tfrac12\operatorname{trace}\big[g^T(x,i,t)U_{xx}(x,i,t)g(x,i,t)\big]+\sum_{j=1}^N\gamma_{ij}U(x,j,t).$$
--
--   5. **Assumption 3.1** (for a given $U\in C^{2,1}$ and numbers $\lambda_1,\lambda_2$): $\lambda_1,\lambda_2>0$ and
--   $$\mathcal LU(x,i,t)+\lambda_1|U_x(x,i,t)|^2\le-\lambda_2|x|^2\tag{3.3}$$
--   for all $(x,i,t)\in\mathbb R^n\times S\times\mathbb R_+$.
--
--   6. **Condition (3.5)** on the observation interval: $\tau>0$ and
--   $$\lambda_2>\frac{\tau K_3^2}{\lambda_1}\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\quad\text{and}\quad\tau\le\frac1{4K_3}.\tag{3.5}$$
--
--   7. **Assumption 4.1** (for a given $U$ and numbers $c_1,c_2$): $c_1,c_2>0$ and
--   $$c_1|x|^2\le U(x,i,t)\le c_2|x|^2\tag{4.1}$$
--   for all $(x,i,t)\in\mathbb R^n\times S\times\mathbb R_+$.
--
--   These are the standing hypotheses of the paper's main theorems. Note that $\mathcal LU$ uses the continuous-time feedback $u(x,i,t)$, not the sampled one.
--
--   **Formalization Note** $g$ is given by its columns $g_k$, so $|g|^2=\sum_k|g_k|^2$, (2.4) for $g$ is written as $\sum_k|g_k(x,i,t)|^2\le K_2^2|x|^2$ (equivalent, both sides being nonnegative), and $\operatorname{trace}[g^TU_{xx}g]=\sum_kU_{xx}(g_k,g_k)$. $U_x$ is a linear functional on Euclidean space; its operator norm is the Euclidean norm of the gradient, the paper's $|U_x|$. "Locally Lipschitz (see, e.g., [13, 14, 15, 23])" is read in the sense of those references: for each radius one Lipschitz constant, uniform in the mode $i$ and the time $t$. No measurability of $f,g$ in $t$ is assumed (the paper states none). The derivatives of $U$ are witnesses tied to $U$ by the derivative relations; since derivatives are unique, this adds nothing. Modes are `Fin N` (0-based). $\lambda_1,\lambda_2$ are written `lam₁`, `lam₂`.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 908, Assumptions 2.1 (Eq. (2.4)) and 2.2 (Eqs. (2.6)–(2.7)); p. 909, C^{2,1}, Eq. (3.2), Assumption 3.1 (Eq. (3.3)); p. 910, Eq. (3.5); p. 917, Assumption 4.1 (Eq. (4.1))

import Mathlib

open scoped NNReal

namespace You2015.Expo

variable {n m N : ℕ}

/-- **Assumption 2.1.** `K₁, K₂ > 0`; the coefficients `f` and `g` are locally Lipschitz
continuous in `x`, uniformly in `(i, t)` (for every `R` there is `L ≥ 0` with
`|f(x,i,t) − f(y,i,t)| ≤ L|x − y|` and `|g(x,i,t) − g(y,i,t)| ≤ L|x − y|` whenever
`|x|, |y| ≤ R`); and the linear growth condition (2.4) `|f(x,i,t)| ≤ K₁|x|`,
`|g(x,i,t)| ≤ K₂|x|` holds. `|g|` is the trace (Frobenius) norm of the `n × m` matrix whose
columns are `g x i t k`, so its square is `∑ₖ |g x i t k|²`. -/
def Assumption21
    (f : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ : ℝ) : Prop :=
  0 < K₁ ∧ 0 < K₂ ∧
    (∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y i t, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖f x i t - f y i t‖ ≤ L * ‖x - y‖ ∧
        ∑ k, ‖g x i t k - g y i t k‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2) ∧
    ∀ x i t, ‖f x i t‖ ≤ K₁ * ‖x‖ ∧ ∑ k, ‖g x i t k‖ ^ 2 ≤ K₂ ^ 2 * ‖x‖ ^ 2

/-- **Assumption 2.2.** `K₃ > 0`, the controller is globally Lipschitz,
`|u(x,i,t) − u(y,i,t)| ≤ K₃|x − y|` (2.6), and `u(0,i,t) = 0` (2.7). -/
def Assumption22
    (u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n)) (K₃ : ℝ) : Prop :=
  0 < K₃ ∧ (∀ x y i t, ‖u x i t - u y i t‖ ≤ K₃ * ‖x - y‖) ∧ ∀ i t, u 0 i t = 0

/-- The class `C^{2,1}(Rⁿ × S × R₊; R₊)`, with its derivatives given as witnesses tied to `U`:
`U ≥ 0`; `Ux x i t` is the Fréchet derivative of `U(·, i, t)` at `x` and `Uxx x i t` that of
`Ux(·, i, t)` at `x`; `Ut x i t` is the (one-sided at `t = 0`) derivative of `s ↦ U(x, i, s)`
on `[0, ∞)` at `t`; and `U, Ut, Ux, Uxx` are jointly continuous in `(x, t)` for each mode `i`. -/
structure C21
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) : Prop where
  nonneg : ∀ x i t, 0 ≤ U x i t
  hasFDerivAt_x : ∀ x i t, HasFDerivAt (fun y => U y i t) (Ux x i t) x
  hasFDerivAt_xx : ∀ x i t, HasFDerivAt (fun y => Ux y i t) (Uxx x i t) x
  hasDerivWithinAt_t : ∀ x i t,
    HasDerivWithinAt (fun s : ℝ => U x i s.toNNReal) (Ut x i t) (Set.Ici 0) (t : ℝ)
  cont_U : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => U p.1 i p.2)
  cont_Ut : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => Ut p.1 i p.2)
  cont_Ux : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => Ux p.1 i p.2)
  cont_Uxx : ∀ i, Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ≥0 => Uxx p.1 i p.2)

/-- The operator (3.2), with the continuous-time feedback `u(x, i, t)`:
`𝓛U(x,i,t) = U_t + U_x[f + u] + ½ trace[gᵀ U_xx g] + ∑ⱼ γ_ij U(x, j, t)`, where
`trace[gᵀ U_xx g] = ∑ₖ U_xx(g_k, g_k)` over the columns `g_k` of `g`. -/
noncomputable def LU (Γ : Matrix (Fin N) (Fin N) ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin N) (t : ℝ≥0) : ℝ :=
  Ut x i t + Ux x i t (f x i t + u x i t)
    + (1 / 2) * ∑ k, Uxx x i t (g x i t k) (g x i t k)
    + ∑ j, Γ i j * U x j t

/-- **Assumption 3.1** for the given `U` (with derivatives `Ut, Ux, Uxx`) and numbers
`lam₁ = λ₁`, `lam₂ = λ₂`: `λ₁, λ₂ > 0` and (3.3)
`𝓛U(x,i,t) + λ₁|U_x(x,i,t)|² ≤ −λ₂|x|²` for all `(x, i, t)`. The norm of `Ux x i t` is the
operator norm of a linear functional on Euclidean space, i.e. the Euclidean norm of the
gradient. -/
def Assumption31 (Γ : Matrix (Fin N) (Fin N) ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (lam₁ lam₂ : ℝ) : Prop :=
  0 < lam₁ ∧ 0 < lam₂ ∧
    ∀ x i t, LU Γ f u g U Ut Ux Uxx x i t + lam₁ * ‖Ux x i t‖ ^ 2 ≤ -lam₂ * ‖x‖ ^ 2

/-- **Condition (3.5)** on the observation interval `τ`: `τ > 0`,
`λ₂ > (τK₃²/λ₁)[2τ(K₁² + 2K₃²) + K₂²]` and `τ ≤ 1/(4K₃)`. -/
def Condition35 (K₁ K₂ K₃ lam₁ lam₂ : ℝ) (τ : ℝ≥0) : Prop :=
  0 < τ ∧
    (τ : ℝ) * K₃ ^ 2 / lam₁ * (2 * τ * (K₁ ^ 2 + 2 * K₃ ^ 2) + K₂ ^ 2) < lam₂ ∧
    (τ : ℝ) ≤ 1 / (4 * K₃)

/-- **Assumption 4.1** for the given `U`: there are positive numbers `c₁, c₂` with
`c₁|x|² ≤ U(x, i, t) ≤ c₂|x|²` (4.1) for all `(x, i, t) ∈ Rⁿ × S × R₊`. -/
def Assumption41 (U : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ) (c₁ c₂ : ℝ) : Prop :=
  0 < c₁ ∧ 0 < c₂ ∧ ∀ x i t, c₁ * ‖x‖ ^ 2 ≤ U x i t ∧ U x i t ≤ c₂ * ‖x‖ ^ 2

end You2015.Expo


