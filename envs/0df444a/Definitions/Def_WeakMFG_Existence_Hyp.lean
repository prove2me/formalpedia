-- Prove2me | Definitions.Def_WeakMFG_Existence_Hyp
-- name    : WeakMFG_Existence_Hyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:43.358333+00:00
-- url     : https://prove2.me/theorems/36b293ef-3685-42a7-a861-08032709a0ae
-- title:
--   Standing assumptions (S.1)–(S.5), the driftless state X of (3.1), the driftless law 𝒳 and assumption (E) (§3.1–§3.2)
-- statement:
--   Fix $d$, $T>0$, $\psi:\mathcal C\to[1,\infty)$ measurable, a control set $A$ in a normed space $E_A$, and coefficients
--   $$b:[0,T]\times\mathcal C\times\mathcal P_\psi(\mathcal C)\times A\to\mathbb R^d,\quad \sigma:[0,T]\times\mathcal C\to\mathbb R^{d\times d},\quad f:[0,T]\times\mathcal C\times\mathcal P_\psi(\mathcal C)\times\mathcal P(A)\times A\to\mathbb R,\quad g:\mathcal C\times\mathcal P_\psi(\mathcal C)\to\mathbb R.$$
--   The standing assumptions (S), assumed throughout the paper, are:
--
--   1. **(S.1)** $A$ is compact and convex; $\sigma$ is progressively measurable; $(t,x)\mapsto b(t,x,\mu,a)$ is progressively measurable for each $(\mu,a)$, and $a\mapsto b(t,x,\mu,a)$ is continuous for each $(t,x,\mu)$.
--   2. **(S.2)** There is a unique strong solution $X$ of the driftless state equation $dX_t=\sigma(t,X)\,dW_t$, $X_0=\xi$ (3.1), with $\mathbb E[\psi^2(X)]<\infty$, $\sigma(t,X)$ nonsingular for all $t\in[0,T]$ almost surely, and $\sigma^{-1}b(t,X,\mu,a)$ uniformly bounded.
--   3. **(S.3)** $(t,x)\mapsto f(t,x,\mu,q,a)$ is progressively measurable for each $(\mu,q,a)$, $a\mapsto f(t,x,\mu,q,a)$ is continuous, and $x\mapsto g(x,\mu)$ is Borel measurable.
--   4. **(S.4)** For some $c>0$ and a nonnegative increasing $\rho$, $|g(x,\mu)|+|f(t,x,\mu,q,a)|\le c\big(\psi(x)+\rho(\int\psi\,d\mu)\big)$.
--   5. **(S.5)** $f(t,x,\mu,q,a)=f_1(t,x,\mu,a)+f_2(t,x,\mu,q)$.
--
--   The *driftless law* is $\mathcal X:=P\circ X^{-1}$ and $\mathcal P_X:=\{\mu\in\mathcal P_\psi(\mathcal C):\mu\sim\mathcal X\}$. **Assumption (E)** asks that, for each $(t,x)$, the maps
--   $$(\mu,a)\mapsto b(t,x,\mu,a),\qquad(\mu,q,a)\mapsto f(t,x,\mu,q,a),\qquad \mu\mapsto g(x,\mu)$$
--   on $\mathcal P_X\times A$, $\mathcal P_X\times\mathcal P(A)\times A$ and $\mathcal P_X$ be sequentially continuous, with $\tau_\psi(\mathcal C)$ on $\mathcal P_X$ and the weak topology on $\mathcal P(A)$.
--
--   **Formalization Note** The SDE (3.1) is read through the published L² Itô layer (`Peng1990.SMP.IsItoProcess`), which also requires $\sup_{t\le T}\mathbb E|X_t-\xi|^2<\infty$; uniqueness is among processes with continuous paths. "$\sigma(t,X)>0$" is encoded as nonsingularity (the paper calls it "the nonsingularity assumption"), "increasing" as monotone, and $\rho$ is defined on all of $\mathbb R$ (only $[0,\infty)$ matters). The measurability of the path map of $X$ is recorded explicitly. (E) is stated with sequences, exactly as on the page; it is not continuity.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), §3.1, pp. 8–10 (S.1)–(S.5); §3.2, pp. 10–11, 𝒳, P_X and (E)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

variable {d : ℕ} {T : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]

/-- The standing requirement on `ψ` (§3.1, p. 8): `ψ : C → [1, ∞)` is Borel measurable. -/
def PsiHyp (ψ : Path d T → ℝ) : Prop :=
  Measurable ψ ∧ ∀ x, 1 ≤ ψ x

/-- Assumption (S.1) (p. 9): `A` is a compact convex subset of the normed space `EA`; `σ` is
progressively measurable; `(t, x) ↦ b(t, x, μ, a)` is progressively measurable for each
`(μ, a)`; `a ↦ b(t, x, μ, a)` is continuous on `A` for each `(t, x, μ)`. -/
def S1 (A : Set EA) (ψ : Path d T → ℝ)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ)) : Prop :=
  IsCompact A ∧ Convex ℝ A ∧ IsStronglyProgressive (pathFilt d T) σ ∧
    (∀ μ a, IsStronglyProgressive (pathFilt d T) (fun t x => b t x μ a)) ∧
    ∀ t x μ, ContinuousOn (b t x μ) A

/-- Assumption (S.2) (p. 9): `X` (with path map `Xp`) is the unique strong solution of the
driftless state equation `dX_t = σ(t, X) dW_t`, `X_0 = ξ` (3.1); `E[ψ²(X)] < ∞`;
`σ(t, X)` is nonsingular for all `t ∈ [0, T]` almost surely; `σ⁻¹b(t, X, μ, a)` is uniformly
bounded.
Formalization Notes: (D2) the SDE is read with the L² Itô layer `Peng1990.SMP.IsItoProcess`
(`X − ξ` is an Itô process with zero drift and diffusion `σ(s, X)`), which also requires
`sup_{t ≤ T} E|X_t − ξ|² < ∞`; uniqueness is among processes with continuous paths;
(D3) "σ(t, X) > 0" is nonsingularity `IsUnit det`; `Measurable Xp` is recorded explicitly (it
follows from progressive measurability of `X`, and keeps `P ∘ X⁻¹` from being the zero
measure). `(σ t x)⁻¹` is Mathlib's matrix inverse (`0` on singular matrices, never reached
along `X` almost surely). -/
def StateHyp (B : Base d T Ω) (A : Set EA) (ψ : Path d T → ℝ)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T) : Prop :=
  (∀ ω (s : Set.Icc (0 : ℝ) T), Xp ω s = X s.1.toNNReal ω) ∧
  Measurable Xp ∧
  Peng1990.SMP.IsItoProcess B.filt B.P T B.W 0 0
    (fun j s ω i => σ s (Xp ω) i j) (fun t ω => X t ω - B.ξ ω) ∧
  (∀ (X' : ℝ≥0 → Ω → Fin d → ℝ) (X'p : Ω → Path d T),
    (∀ ω (s : Set.Icc (0 : ℝ) T), X'p ω s = X' s.1.toNNReal ω) →
    Peng1990.SMP.IsItoProcess B.filt B.P T B.W 0 0
      (fun j s ω i => σ s (X'p ω) i j) (fun t ω => X' t ω - B.ξ ω) →
    ∀ t ≤ T, X' t =ᵐ[B.P] X t) ∧
  ∫⁻ ω, ENNReal.ofReal (ψ (Xp ω)) ^ 2 ∂B.P < ⊤ ∧
  (∀ᵐ ω ∂B.P, ∀ t ≤ T, IsUnit (σ t (Xp ω)).det) ∧
  ∃ c : ℝ, ∀ᵐ ω ∂B.P, ∀ t ≤ T, ∀ μ, ∀ a ∈ A, ‖(σ t (Xp ω))⁻¹ *ᵥ b t (Xp ω) μ a‖ ≤ c

/-- Assumption (S.3) (p. 9): `(t, x) ↦ f(t, x, μ, q, a)` is progressively measurable for each
`(μ, q, a)`; `a ↦ f(t, x, μ, q, a)` is continuous on `A` for each `(t, x, μ, q)`;
`x ↦ g(x, μ)` is Borel measurable for each `μ`. -/
def S3 (A : Set EA) (ψ : Path d T → ℝ)
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ) : Prop :=
  (∀ μ q a, IsStronglyProgressive (pathFilt d T) (fun t x => f t x μ q a)) ∧
    (∀ t x μ q, ContinuousOn (f t x μ q) A) ∧
    ∀ μ, Measurable (fun x => g x μ)

/-- Assumption (S.4) (p. 10): there are `c > 0` and a nonnegative increasing `ρ` with
`|g(x, μ)| + |f(t, x, μ, q, a)| ≤ c (ψ(x) + ρ(∫ ψ dμ))` for all `(t, x, μ, q, a)`.
Formalization Note (D4): "increasing" is read as `Monotone`; `ρ` is given on all of `ℝ` and only
its values on `[0, ∞)` matter. -/
def S4 (A : Set EA) (ψ : Path d T → ℝ)
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ) : Prop :=
  ∃ c > (0 : ℝ), ∃ ρ : ℝ → ℝ, (∀ r, 0 ≤ ρ r) ∧ Monotone ρ ∧
    ∀ t x μ q, ∀ a ∈ A,
      |g x μ| + |f t x μ q a| ≤ c * (ψ x + ρ (∫ y, ψ y ∂μ.toMeasure))

/-- Assumption (S.5) (p. 10): `f(t, x, μ, q, a) = f₁(t, x, μ, a) + f₂(t, x, μ, q)`. -/
def S5 (A : Set EA) (ψ : Path d T → ℝ)
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) : Prop :=
  ∃ (f₁ : ℝ≥0 → Path d T → Ppsi ψ → EA → ℝ) (f₂ : ℝ≥0 → Path d T → Ppsi ψ → PA A → ℝ),
    ∀ t x μ q a, f t x μ q a = f₁ t x μ a + f₂ t x μ q

/-- The standing assumptions (S) (pp. 8–10), "implicitly assumed throughout the paper":
`ψ ≥ 1` measurable, (S.1), (S.2), (S.3), (S.4), (S.5). -/
def Standing (B : Base d T Ω) (A : Set EA) (ψ : Path d T → ℝ)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T) : Prop :=
  PsiHyp ψ ∧ S1 A ψ σ b ∧ StateHyp B A ψ σ b X Xp ∧ S3 A ψ f g ∧ S4 A ψ f g ∧ S5 A ψ f

/-- The driftless law `𝒳 := P ∘ X⁻¹` (p. 10), as a measure on `C`. -/
noncomputable def lawX (B : Base d T Ω) (Xp : Ω → Path d T) : Measure (Path d T) :=
  B.P.map Xp

/-- Assumption (E) (p. 11): for each `(t, x)`, the maps `(μ, a) ↦ b(t, x, μ, a)` on
`P_X × A`, `(μ, q, a) ↦ f(t, x, μ, q, a)` on `P_X × P(A) × A` and `μ ↦ g(x, μ)` on `P_X` are
sequentially continuous, using `τ_ψ(C)` on `P_X = {μ ∈ P_ψ(C) : μ ∼ 𝒳}` and the weak topology
on `P(A)`. Formalization Note: stated with sequences, exactly as the page (it is not
continuity). -/
def CondE (B : Base d T Ω) (A : Set EA) (ψ : Path d T → ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (Xp : Ω → Path d T) : Prop :=
  ∀ t x,
    (∀ (μn : ℕ → Ppsi ψ) (μ : Ppsi ψ) (an : ℕ → EA) (a : EA),
      (∀ n, MEquiv (μn n).toMeasure (lawX B Xp)) → MEquiv μ.toMeasure (lawX B Xp) →
      (∀ n, an n ∈ A) → a ∈ A →
      Tendsto μn atTop (𝓝 μ) → Tendsto an atTop (𝓝 a) →
      Tendsto (fun n => b t x (μn n) (an n)) atTop (𝓝 (b t x μ a))) ∧
    (∀ (μn : ℕ → Ppsi ψ) (μ : Ppsi ψ) (qn : ℕ → PA A) (q : PA A) (an : ℕ → EA) (a : EA),
      (∀ n, MEquiv (μn n).toMeasure (lawX B Xp)) → MEquiv μ.toMeasure (lawX B Xp) →
      (∀ n, an n ∈ A) → a ∈ A →
      Tendsto μn atTop (𝓝 μ) → Tendsto qn atTop (𝓝 q) → Tendsto an atTop (𝓝 a) →
      Tendsto (fun n => f t x (μn n) (qn n) (an n)) atTop (𝓝 (f t x μ q a))) ∧
    (∀ (μn : ℕ → Ppsi ψ) (μ : Ppsi ψ),
      (∀ n, MEquiv (μn n).toMeasure (lawX B Xp)) → MEquiv μ.toMeasure (lawX B Xp) →
      Tendsto μn atTop (𝓝 μ) →
      Tendsto (fun n => g x (μn n)) atTop (𝓝 (g x μ)))

end WeakMFG.Existence


