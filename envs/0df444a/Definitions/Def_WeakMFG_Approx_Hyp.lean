-- Prove2me | Definitions.Def_WeakMFG_Approx_Hyp
-- name    : WeakMFG_Approx_Hyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:37.672752+00:00
-- url     : https://prove2.me/theorems/c290b465-cab6-4381-a53d-e4a9bc5bc8ba
-- title:
--   The standing assumptions (S), the driftless state $X$ of (3.1), the Hamiltonian (3.2) and assumption (C)
-- statement:
--   The data are a volatility $\sigma:[0,T]\times\mathcal C\to\mathbb R^{d\times d}$, a drift $b:[0,T]\times\mathcal C\times\mathcal P_\psi(\mathcal C)\times A\to\mathbb R^d$, a running reward $f:[0,T]\times\mathcal C\times\mathcal P_\psi(\mathcal C)\times\mathcal P(A)\times A\to\mathbb R$ and a terminal reward $g:\mathcal C\times\mathcal P_\psi(\mathcal C)\to\mathbb R$. The **standing assumptions (S)** are:
--
--   1. (S.1) $A$ is a compact convex subset of a normed space; $\sigma$ is progressively measurable; $(t,x)\mapsto b(t,x,\mu,a)$ is progressively measurable for each $(\mu,a)$ and $a\mapsto b(t,x,\mu,a)$ is continuous for each $(t,x,\mu)$.
--   2. (S.2) There is a unique strong solution $X$ of the driftless state equation $dX_t=\sigma(t,X)\,dW_t$, $X_0=\xi$, such that $\mathbb E[\psi^2(X)]<\infty$, $\sigma(t,X)$ is nonsingular for all $t\in[0,T]$ almost surely, and $\sigma^{-1}(t,X)b(t,X,\mu,a)$ is uniformly bounded.
--   3. (S.3) $(t,x)\mapsto f(t,x,\mu,q,a)$ is progressively measurable for each $(\mu,q,a)$, $a\mapsto f(t,x,\mu,q,a)$ is continuous for each $(t,x,\mu,q)$, and $x\mapsto g(x,\mu)$ is Borel measurable for each $\mu$.
--   4. (S.4) There are $c>0$ and an increasing $\rho:[0,\infty)\to[0,\infty)$ with $|g(x,\mu)|+|f(t,x,\mu,q,a)|\le c\big(\psi(x)+\rho(\int\psi\,d\mu)\big)$.
--   5. (S.5) $f(t,x,\mu,q,a)=f_1(t,x,\mu,a)+f_2(t,x,\mu,q)$.
--
--   The law of $X$ is $\mathcal X := P\circ X^{-1}$. The **Hamiltonian**, its maximized value and the maximizer set (3.2) are
--   $$h(t,x,\mu,q,z,a)=f(t,x,\mu,q,a)+z\cdot\sigma^{-1}b(t,x,\mu,a),\quad H=\sup_{a\in A}h,\quad A(t,x,\mu,q,z)=\{a\in A: h=H\}.$$
--   **Assumption (C)** requires every set $A(t,x,\mu,z)$ to be convex.
--
--   These assumptions stand throughout the paper; Theorem 4.2 assumes (C) in addition.
--
--   **Formalization Note** "Strong solution" is read in the $L^2$ Itô theory of the published `Peng1990.SMP.Stochastic`: $X-\xi$ is a progressive process with $\sup_{t\le T}\mathbb E|X_t-\xi|^2<\infty$ and $X_t-\xi=\int_0^t\sigma(s,X)\,dW_s$, which also requires $\mathbb E\int_0^T\|\sigma(t,X)\|^2dt<\infty$; $X$ has continuous paths, and uniqueness is among such solutions. Nonsingularity is $\det\sigma(t,X)$ a unit. "Increasing" $\rho$ is encoded as monotone (nondecreasing), a weaker requirement. (C) is also quantified over the $q$ argument, on which $A(\cdot)$ does not depend under (S.5).
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, pp. 9–10, (S.1)–(S.5), (3.1); §3.2, p. 10, (3.2) and Assumption (C)

import Mathlib
import Definitions.Def_WeakMFG_Approx_Model
import Definitions.Def_WeakMFG_Uniqueness_Hyp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Approx

variable {d : ℕ} {T : ℝ≥0} {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [MeasurableSpace EA] [BorelSpace EA]

/-- (S.1), p. 9: `A` is a compact convex subset of the normed space `EA`; `σ` is progressively
measurable; `(t, x) ↦ b(t, x, μ, a)` is progressively measurable for each `(μ, a)`; and
`a ↦ b(t, x, μ, a)` is continuous (on `A`) for each `(t, x, μ)`. -/
def S1 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) : Prop :=
  IsCompact A ∧ Convex ℝ A ∧ IsStronglyProgressive pathFilt σ ∧
    (∀ μ a, IsStronglyProgressive pathFilt (fun t x => b t x μ a)) ∧
    ∀ t x μ, ContinuousOn (b t x μ) A

/-- (S.3), p. 9: `(t, x) ↦ f(t, x, μ, q, a)` is progressively measurable for each `(μ, q, a)`,
`a ↦ f(t, x, μ, q, a)` is continuous (on `A`) for each `(t, x, μ, q)`, and `x ↦ g(x, μ)` is Borel
measurable for each `μ`. -/
def S3 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  (∀ μ q a, IsStronglyProgressive pathFilt (fun t x => f t x μ q a)) ∧
    (∀ t x μ q, ContinuousOn (f t x μ q) A) ∧ ∀ μ, Measurable (fun x => g x μ)

/-- (S.4), p. 10: there are `c > 0` and an increasing `ρ ≥ 0` with
`|g(x, μ)| + |f(t, x, μ, q, a)| ≤ c (ψ(x) + ρ(∫ ψ dμ))` (D4: `Monotone ρ`). -/
def S4 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∃ ρ : ℝ → ℝ, (∀ r, 0 ≤ ρ r) ∧ Monotone ρ ∧
    ∀ t x μ q, ∀ a ∈ A, |g x μ| + |f t x μ q a| ≤ c * (ψ x + ρ (∫ y, ψ y ∂μ.μ))

/-- (S.5), p. 10: `f(t, x, μ, q, a) = f₁(t, x, μ, a) + f₂(t, x, μ, q)`. -/
def S5 {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∃ (f₁ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → ℝ) (f₂ : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → ℝ),
    ∀ t x μ q a, f t x μ q a = f₁ t x μ a + f₂ t x μ q

/-- The parts (S.1), (S.3), (S.4), (S.5) of the standing assumptions (S) together with the
admissibility of `ψ`; the (S.2) part is the structure `Driftless`. -/
def Standing {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) (g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ) : Prop :=
  WeakMFG.Uniqueness.PsiAdm ψ ∧ S1 A σ b ∧ S3 A f g ∧ S4 A f g ∧ S5 A f

/-- (S.2), p. 9, on the base space `B`: `X` is the unique strong solution of the driftless state
equation `dX_t = σ(t, X) dW_t`, `X_0 = ξ` (3.1), with `E[ψ²(X)] < ∞`, `σ(t, X)` nonsingular for all
`t ∈ [0, T]` a.s. (D3), and `σ⁻¹(t, X) b(t, X, μ, a)` uniformly bounded.
Formalization Note (D2): "strong solution" is `Peng1990.SMP.IsItoProcess` for `X − ξ` (an L² Itô
process: `X − ξ` progressive with `sup_{t ≤ T} E|X_t − ξ|² < ∞` and `E ∫₀ᵀ ‖σ(t, X)‖² dt < ∞`), and
`Xp ω ∈ C` is the path of `X(ω)` on `[0, T]` (so `X` has continuous paths). -/
structure Driftless {Ω : Type*} [MeasurableSpace Ω] (B : Base d Ω) (ψ : WeakMFG.Existence.Path d T → ℝ)
    (A : Set EA) (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)) where
  X : ℝ≥0 → Ω → Fin d → ℝ
  Xp : Ω → WeakMFG.Existence.Path d T
  hXp : ∀ ω s, Xp ω s = X (s : ℝ).toNNReal ω
  ito : Peng1990.SMP.IsItoProcess B.filt B.P T B.W 0 0 (fun j s ω i => σ s (Xp ω) i j)
    (fun t ω => X t ω - B.ξ ω)
  uniq : ∀ (X' : ℝ≥0 → Ω → Fin d → ℝ) (X'p : Ω → WeakMFG.Existence.Path d T),
    (∀ ω s, X'p ω s = X' (s : ℝ).toNNReal ω) →
    Peng1990.SMP.IsItoProcess B.filt B.P T B.W 0 0 (fun j s ω i => σ s (X'p ω) i j)
      (fun t ω => X' t ω - B.ξ ω) →
    ∀ t ≤ T, X' t =ᵐ[B.P] X t
  psi2 : ∫⁻ ω, ENNReal.ofReal (ψ (Xp ω)) ^ 2 ∂B.P < ⊤
  nonsing : ∀ᵐ ω ∂B.P, ∀ t ≤ T, IsUnit (σ t (Xp ω)).det
  bdd : ∃ c : ℝ, ∀ᵐ ω ∂B.P, ∀ t ≤ T, ∀ μ, ∀ a ∈ A, ‖(σ t (Xp ω))⁻¹ *ᵥ b t (Xp ω) μ a‖ ≤ c

/-- The driftless law `𝒳 := P ∘ X⁻¹` (p. 10). -/
noncomputable def Driftless.law {Ω : Type*} [MeasurableSpace Ω] {B : Base d Ω}
    {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA} {σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ}
    {b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)} (X : Driftless B ψ A σ b) :
    Measure (WeakMFG.Existence.Path d T) :=
  B.P.map X.Xp

/-- The Hamiltonian `h(t, x, μ, q, z, a) := f(t, x, μ, q, a) + z · σ⁻¹ b(t, x, μ, a)` of (3.2), p. 10. -/
noncomputable def ham {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA}
    (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : PA A) (z : Fin d → ℝ) (a : EA) : ℝ :=
  f t x μ q a + z ⬝ᵥ ((σ t x)⁻¹ *ᵥ b t x μ a)

/-- The maximized Hamiltonian `H(t, x, μ, q, z) := sup_{a ∈ A} h(t, x, μ, q, z, a)` of (3.2).
Under (S.1), (S.3) the image is a compact set of reals and the sup is attained. -/
noncomputable def Ham {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : PA A) (z : Fin d → ℝ) : ℝ :=
  sSup ((ham σ b f t x μ q z) '' A)

/-- `A(t, x, μ, q, z) := {a ∈ A : h(t, x, μ, q, z, a) = H(t, x, μ, q, z)}` of (3.2). -/
def Amax {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ)
    (t : ℝ≥0) (x : WeakMFG.Existence.Path d T) (μ : Ppsi ψ) (q : PA A) (z : Fin d → ℝ) : Set EA :=
  {a ∈ A | ham σ b f t x μ q z a = Ham A σ b f t x μ q z}

/-- Assumption (C), p. 10: for each `(t, x, μ, z)` the set `A(t, x, μ, z)` is convex (quantified
also over the `q` argument, which `A(·)` does not depend on under (S.5)). -/
def CondC {ψ : WeakMFG.Existence.Path d T → ℝ} (A : Set EA)
    (σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∀ t x μ q z, Convex ℝ (Amax A σ b f t x μ q z)

end WeakMFG.Approx


