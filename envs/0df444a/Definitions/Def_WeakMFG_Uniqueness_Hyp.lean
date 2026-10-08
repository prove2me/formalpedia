-- Prove2me | Definitions.Def_WeakMFG_Uniqueness_Hyp
-- name    : WeakMFG_Uniqueness_Hyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:50.360326+00:00
-- url     : https://prove2.me/theorems/46c19d75-7528-484a-951b-fa04bbfd084e
-- title:
--   The standing assumptions (S.1)–(S.5) and joint measurability of the running reward
-- statement:
--   This file states the standing assumptions (S) of Carmona and Lacker, which "are implicitly assumed throughout the paper" (p. 8). The data are a control set $A$ in a normed space, a volatility $\sigma : [0,T]\times\mathcal C\to\mathbb R^{d\times d}$, a drift $b(t,x,\mu,a)\in\mathbb R^d$, a running reward $f(t,x,\mu,q,a)\in\mathbb R$ and a terminal reward $g(x,\mu)\in\mathbb R$, with $t\in[0,T]$, $x\in\mathcal C$, $\mu\in\mathcal P_\psi(\mathcal C)$, $q\in\mathcal P(A)$, $a\in A$, and a process $X$ on the base space with its path map.
--
--   1. $\psi : \mathcal C\to[1,\infty)$ is Borel measurable.
--   2. **(S.1)** $A$ is compact and convex; $\sigma$ is progressively measurable; $(t,x)\mapsto b(t,x,\mu,a)$ is progressively measurable for each $(\mu,a)$, and $a\mapsto b(t,x,\mu,a)$ is continuous on $A$ for each $(t,x,\mu)$.
--   3. **(S.2)** $X$ is the unique strong solution of the driftless state equation
--   $$dX_t = \sigma(t,X)\,dW_t,\qquad X_0=\xi, \tag{3.1}$$
--   with $E[\psi^2(X)]<\infty$; almost surely $\sigma(t,X)$ is nonsingular for all $t\in[0,T]$; and $\sigma^{-1}(t,X)\,b(t,X,\mu,a)$ is uniformly bounded.
--   4. **(S.3)** $(t,x)\mapsto f(t,x,\mu,q,a)$ is progressively measurable for each $(\mu,q,a)$, $a\mapsto f(t,x,\mu,q,a)$ is continuous on $A$, and $x\mapsto g(x,\mu)$ is Borel measurable.
--   5. **(S.4)** There are $c>0$ and an increasing $\rho:[0,\infty)\to[0,\infty)$ with
--   $$|g(x,\mu)| + |f(t,x,\mu,q,a)| \le c\Big(\psi(x) + \rho\Big(\int\psi\,d\mu\Big)\Big).$$
--   6. **(S.5)** $f(t,x,\mu,q,a) = f_1(t,x,\mu,a) + f_2(t,x,\mu,q)$ for some $f_1,f_2$.
--
--   The file also defines the joint measurability condition: for each $\mu$, $(t,x,q,a)\mapsto f(t,x,\mu,q,a)$ is measurable, with the Borel $\sigma$-field of the weak topology on $\mathcal P(A)$.
--
--   These assumptions make the control problem behind the mean field game well posed: the Girsanov change of measure is available, the reward is finite, and the Hamiltonian's maximizers do not depend on the $\mathcal P(A)$ argument.
--
--   **Formalization Note.** "Strong solution" of (3.1) is read in the $L^2$ Itô theory of the referenced definition `Peng1990.SMP.Stochastic`, which also asks $\sup_{t\le T}E|X_t-\xi|^2<\infty$ and $E\int_0^T|\sigma(t,X)|^2dt<\infty$; the solution has continuous paths (its path map is a point of $\mathcal C$), and uniqueness is up to modification among such solutions: any other one agrees with $X$ almost surely at each $t\le T$. "$\sigma(t,X)>0$" is encoded as invertibility of the matrix (Remark 3.2 calls it the nonsingularity assumption). "Increasing" $\rho$ is encoded as monotone, and $\rho$ is extended to $\mathbb R$. (S.5) is stated for all $a$; values of $f$ off $A$ never enter a statement. The joint measurability condition is not printed in (S.3); it is an added hypothesis, used where the reward $E^{\mu,\alpha}[\int_0^T f(t,X,\mu,q_t,\alpha_t)dt]$ must be defined: without measurability in $q$ the integrand $t\mapsto f(t,X,\mu,q_t,\alpha_t)$ need not be measurable, and Lean's integral of a non-measurable function is $0$. Time is $t\in[0,\infty)$ in Lean, and the conditions of (S.1), (S.3) and (S.4) are asked for every $t\ge 0$; every statement uses the coefficients on $[0,T]$ only, so this costs nothing (replace a coefficient by its value at $t\wedge T$). The path space $\mathcal C$ is that of the module `WeakMFG.Existence.Model`; the types $\mathcal P_\psi(\mathcal C)$, $\mathcal P(A)$, the base space and the canonical filtration are those of the module `WeakMFG.Uniqueness.Model`.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, Assumption (S), pp. 8–10

import Mathlib
import Definitions.Def_WeakMFG_Uniqueness_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Uniqueness

variable {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]

/-- `ψ : 𝒞 → [1, ∞)` is Borel measurable (p. 8: "fix a Borel measurable function
`ψ : 𝒞 → [1, ∞)` throughout"). -/
def PsiAdm (ψ : WeakMFG.Existence.Path d T → ℝ) : Prop :=
  Measurable ψ ∧ ∀ x, 1 ≤ ψ x

/-- Assumption (S.1), p. 9: the control space `A` is a compact convex subset of the normed space
`EA`; the volatility `σ : [0, T] × 𝒞 → ℝ^{d×d}` is progressively measurable; for each `(μ, a)`,
`(t, x) ↦ b(t, x, μ, a)` is progressively measurable; for each `(t, x, μ)`, `a ↦ b(t, x, μ, a)` is
continuous on `A`. (That the admissible controls are the progressive `A`-valued processes is
`Base.IsAdmissible`.) -/
def S1 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) : Prop :=
  IsCompact A ∧ Convex ℝ A ∧ IsStronglyProgressive (pathFilt d T) σ ∧
    (∀ μ a, IsStronglyProgressive (pathFilt d T) (fun t x => b t x μ a)) ∧
    ∀ t x μ, ContinuousOn (b t x μ) A

/-- Assumption (S.2), p. 9, for the process `X` with path map `Xp`: `X` is the unique strong
solution of the driftless state equation `dX_t = σ(t, X) dW_t`, `X_0 = ξ` (3.1); `E[ψ²(X)] < ∞`;
almost surely `σ(t, X)` is nonsingular for all `t ∈ [0, T]`; and `σ⁻¹(t, X) b(t, X, μ, a)` is
uniformly bounded.
**Formalization Note.** (D2) "strong solution" is read in the L² Itô theory of
`Peng1990.SMP.IsItoProcess`, which also asks `sup_{t ≤ T} E|X_t − ξ|² < ∞` and
`E ∫₀ᵀ |σ(t, X)|² dt < ∞`. (D3) "`σ(t, X) > 0`" is encoded as invertibility of the matrix
(Remark 3.2 calls (S.2) "the nonsingularity assumption"). Uniqueness is pathwise up to
modification: any other solution `X'` agrees with `X` almost surely at each `t ≤ T`. -/
def S2 {ψ : WeakMFG.Existence.Path d T → ℝ} (B : Base d Ω) (A : Set EA)
    (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T) : Prop :=
  (∀ ω (s : Set.Icc (0 : ℝ) T), Xp ω s = X (s : ℝ).toNNReal ω) ∧
  Peng1990.SMP.IsItoProcess B.filt B.P T B.W 0 0 (fun j s ω i => σ s (Xp ω) i j)
    (fun t ω => X t ω - B.ξ ω) ∧
  (∀ (X' : ℝ≥0 → Ω → Fin d → ℝ) (X'p : Ω → WeakMFG.Existence.Path d T),
    (∀ ω (s : Set.Icc (0 : ℝ) T), X'p ω s = X' (s : ℝ).toNNReal ω) →
    Peng1990.SMP.IsItoProcess B.filt B.P T B.W 0 0 (fun j s ω i => σ s (X'p ω) i j)
      (fun t ω => X' t ω - B.ξ ω) →
    ∀ t ≤ T, X' t =ᵐ[B.P] X t) ∧
  ∫⁻ ω, ENNReal.ofReal (ψ (Xp ω)) ^ 2 ∂B.P < ⊤ ∧
  (∀ᵐ ω ∂B.P, ∀ t ≤ T, IsUnit (σ t (Xp ω)).det) ∧
  ∃ c : ℝ, ∀ᵐ ω ∂B.P, ∀ t ≤ T, ∀ μ, ∀ a ∈ A, ‖(σ t (Xp ω))⁻¹ *ᵥ b t (Xp ω) μ a‖ ≤ c

/-- Assumption (S.3), p. 9: for each `(μ, q, a)`, `(t, x) ↦ f(t, x, μ, q, a)` is progressively
measurable; for each `(t, x, μ, q)`, `a ↦ f(t, x, μ, q, a)` is continuous on `A`; for each `μ`,
`x ↦ g(x, μ)` is Borel measurable. -/
def S3 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA) (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  (∀ μ q a, IsStronglyProgressive (pathFilt d T) (fun t x => f t x μ q a)) ∧
    (∀ t x μ q, ContinuousOn (f t x μ q) A) ∧ ∀ μ, Measurable (fun x => g x μ)

/-- Assumption (S.4), p. 10: there are `c > 0` and an increasing `ρ : [0, ∞) → [0, ∞)` with
`|g(x, μ)| + |f(t, x, μ, q, a)| ≤ c (ψ(x) + ρ(∫ ψ dμ))` for all `(t, x, μ, q, a)`.
**Formalization Note.** (D4) "increasing" is encoded as `Monotone`; `ρ` is a function on `ℝ`,
nonnegative everywhere, of which only its values on `[0, ∞)` are used. -/
def S4 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA) (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∃ ρ : ℝ → ℝ, (∀ r, 0 ≤ ρ r) ∧ Monotone ρ ∧
    ∀ t x μ q, ∀ a ∈ A, |g x μ| + |f t x μ q a| ≤ c * (ψ x + ρ (∫ y, ψ y ∂μ.toMeasure))

/-- Assumption (S.5), p. 10: `f(t, x, μ, q, a) = f₁(t, x, μ, a) + f₂(t, x, μ, q)`. -/
def S5 {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∃ (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → ℝ) (f₂ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → ℝ),
    ∀ t x μ q a, f t x μ q a = f₁ t x μ a + f₂ t x μ q

/-- The standing assumptions (S) (pp. 8–10), "implicitly assumed throughout the paper":
`ψ` is admissible and (S.1)–(S.5) hold, with `X` (path map `Xp`) the state process of (S.2). -/
def Standing (B : Base d Ω) (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    {ψ : WeakMFG.Existence.Path d T → ℝ} (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → WeakMFG.Existence.Path d T) : Prop :=
  PsiAdm ψ ∧ S1 A σ b ∧ S2 B A σ b X Xp ∧ S3 A f g ∧ S4 A f g ∧ S5 f

/-- (D5) Joint measurability of the running reward: for each `μ`, the map
`(t, x, q, a) ↦ f(t, x, μ, q, a)` is measurable on `ℝ≥0 × 𝒞 × P(A) × EA`, with the Borel σ-field
of the weak topology on `P(A)`.
**Formalization Note.** Not printed in (S.3), which gives measurability in `(t, x)` for each fixed
`(μ, q, a)` only. The paper's reward `J^{μ,q}(α) = E^{μ,α}[∫₀ᵀ f(t, X, μ, q_t, α_t) dt + g(X, μ)]`
presupposes that `t ↦ f(t, X, μ, q_t, α_t)` is measurable; without a measurability condition in
`q` it need not be, and Lean's Bochner integral of a non-measurable integrand is `0`. -/
def FJointMeas {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∀ μ, letI : MeasurableSpace (PA A) := borel (PA A)
    Measurable (fun p : ℝ≥0 × WeakMFG.Existence.Path d T × PA A × EA => f p.1 p.2.1 μ p.2.2.1 p.2.2.2)

end WeakMFG.Uniqueness


