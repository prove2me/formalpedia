-- Prove2me | Definitions.Def_MongeKantorovichYao_Defs
-- name    : MongeKantorovichYao_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T18:28:08.158798+00:00
-- url     : https://prove2.me/theorems/5950dd79-ba0d-412e-9d41-805c0a57764a
-- title:
--   Transference plans, $c$-cyclical monotonicity, $c$-conjugates, $c$-concavity, $c$-subdifferentials
-- statement:
--   Basic objects of Monge–Kantorovich optimal transport, following Sections 2.2 and 4 of the source. Throughout, $X$ and $Y$ are measurable spaces and $c : X\times Y\to\mathbb R$ is a cost function.
--
--   1. **Transference plans** (Section 2.2, Definition 4.13). For measures $\mu$ on $X$ and $\nu$ on $Y$, $\Pi(\mu,\nu)$ is the set of probability measures $\pi$ on $X\times Y$ whose marginals are $\mu$ and $\nu$:
--   $$(\mathrm{pr}_X)_\#\pi=\mu,\qquad (\mathrm{pr}_Y)_\#\pi=\nu,$$
--   equivalently $\pi(S\times Y)=\mu(S)$ and $\pi(X\times T)=\nu(T)$ for measurable $S,T$. For sets of measures $M$ on $X$ and $N$ on $Y$, $\Pi(M,N)$ is the set of probability measures on $X\times Y$ whose $X$-marginal lies in $M$ and whose $Y$-marginal lies in $N$ (Lemma 4.16).
--
--   2. **$c$-cyclical monotonicity** (Definition 4.2). A set $\Gamma\subseteq X\times Y$ is $c$-cyclically monotone if for every $N\ge 1$ and all $(x_1,y_1),\dots,(x_N,y_N)\in\Gamma$,
--   $$\sum_{i=1}^N c(x_i,y_i)\le\sum_{i=1}^N c(x_i,y_{i+1}),\qquad y_{N+1}=y_1 .$$
--   A plan $\pi$ is $c$-cyclically monotone if it is concentrated on such a set: $\pi(\Gamma^{c})=0$ for some $c$-cyclically monotone $\Gamma$ (Definition 4.15).
--
--   3. **$c$-conjugate** (Definition 4.19). For $\psi : X\to\overline{\mathbb R}$, $\psi^c(y)=\inf_{x\in X}\big(c(x,y)-\psi(x)\big)$; symmetrically, for $\varphi : Y\to\overline{\mathbb R}$, $\varphi^c(x)=\inf_{y\in Y}\big(c(x,y)-\varphi(y)\big)$.
--
--   4. **$c$-concavity** (Definition 4.18). $\psi : X\to\mathbb R$ is $c$-concave if there is $\varphi : Y\to\mathbb R$ with $\psi(x)=\inf_{y\in Y}\big(c(x,y)-\varphi(y)\big)$ for every $x$.
--
--   5. **$c$-subdifferential** (Definition 4.20). $\partial_c\psi=\{(x,y) : \psi^c(y)+\psi(x)=c(x,y)\}$.
--
--   These are the notions in which the Monge–Kantorovich duality theorem and its proof are phrased.
--
--   **Formalization Note** Infima defining $c$-conjugates are taken in the extended reals $\overline{\mathbb R}=[-\infty,+\infty]$, so they always exist and no default value is substituted. In the cyclic-monotonicity condition the $N$ points are indexed cyclically by $\mathbb Z/N\mathbb Z$. Marginals are pushforwards along the coordinate projections.
-- source:
--   Colin Yao, *Monge–Kantorovich and Transportation Theory* (paper dated September 10, 2023), Section 2.2 (p. 4), Definitions 4.2 (p. 7), 4.13, 4.15 (p. 10), 4.18 (p. 12), 4.19, 4.20 (p. 13); Lemma 4.16 (p. 10)

import Mathlib

open MeasureTheory

namespace MongeKantorovichYao

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Section 2.2: the set `Π(μ, ν)` of transference plans (couplings) between `μ` and `ν`:
probability measures `π` on `X × Y` with `π(S × Y) = μ(S)` and `π(X × T) = ν(T)`, i.e. whose
marginals (Definition 4.13, pushforwards along the projections) are `μ` and `ν`. -/
def transferencePlans (μ : Measure X) (ν : Measure Y) : Set (Measure (X × Y)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- Lemma 4.16: `Π(M, N)`, the transference plans whose marginals lie in `M` and `N`. -/
def transferencePlansOf (M : Set (Measure X)) (N : Set (Measure Y)) : Set (Measure (X × Y)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst ∈ M ∧ π.map Prod.snd ∈ N}

/-- Definition 4.2 (sets): `Γ ⊆ X × Y` is `c`-cyclically monotone if for every `N ≥ 1` and all
`(x₁, y₁), …, (x_N, y_N) ∈ Γ`, `∑ c(xᵢ, yᵢ) ≤ ∑ c(xᵢ, yᵢ₊₁)` with `y_{N+1} = y₁`.
The points are indexed by `Fin (N + 1)`, whose addition wraps around, so `i + 1` is the cyclic
successor. -/
def IsCCyclicallyMonotone (c : X × Y → ℝ) (Γ : Set (X × Y)) : Prop :=
  ∀ (N : ℕ) (p : Fin (N + 1) → X × Y), (∀ i, p i ∈ Γ) →
    ∑ i, c (p i) ≤ ∑ i, c ((p i).1, (p (i + 1)).2)

/-- Definition 4.2 (plans), with Definition 4.15: a transference plan is `c`-cyclically
monotone if it is concentrated on (gives zero mass to the complement of) a `c`-cyclically
monotone set. -/
def IsCCyclicallyMonotonePlan (c : X × Y → ℝ) (π : Measure (X × Y)) : Prop :=
  ∃ Γ : Set (X × Y), IsCCyclicallyMonotone c Γ ∧ π Γᶜ = 0

/-- Definition 4.19: the `c`-conjugate `ψᶜ(y) = inf_{x ∈ X} (c(x, y) - ψ(x))`, taken in the
extended reals so that the infimum always exists. -/
noncomputable def cConjugate (c : X × Y → ℝ) (ψ : X → EReal) (y : Y) : EReal :=
  ⨅ x, (c (x, y) : EReal) - ψ x

/-- The mirror-image transform of a function on `Y`:
`φᶜ(x) = inf_{y ∈ Y} (c(x, y) - φ(y))` (used to state `(ψᶜ)ᶜ = ψ`, Theorem 4.25). -/
noncomputable def cConjugate' (c : X × Y → ℝ) (φ : Y → EReal) (x : X) : EReal :=
  ⨅ y, (c (x, y) : EReal) - φ y

/-- Definition 4.18: `ψ : X → ℝ` is `c`-concave if `ψ(x) = inf_{y ∈ Y} (c(x, y) - φ(y))` for all
`x`, for some `φ : Y → ℝ` (infimum taken in the extended reals). -/
def IsCConcave (c : X × Y → ℝ) (ψ : X → ℝ) : Prop :=
  ∃ φ : Y → ℝ, ∀ x, (ψ x : EReal) = cConjugate' c (fun y => (φ y : EReal)) x

/-- Definition 4.20: the `c`-subdifferential `∂_c ψ = {(x, y) | ψᶜ(y) + ψ(x) = c(x, y)}`. -/
def cSubdifferential (c : X × Y → ℝ) (ψ : X → ℝ) : Set (X × Y) :=
  {p | cConjugate c (fun x => (ψ x : EReal)) p.2 + (ψ p.1 : EReal) = (c p : EReal)}

end MongeKantorovichYao


