-- Prove2me | Definitions.Def_ESAxioms_Characterization_Setting
-- name    : ESAxioms_Characterization_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:48.683756+00:00
-- url     : https://prove2.me/theorems/a103a32e-2efa-46cf-b300-3ec7a16d1649
-- title:
--   §1.2, §2.1–2.2, Definitions 1–2 and 4, p. 20 — L¹, VaRₚ, ESₚ, tail and p-tail events, p-concentration, Axioms M, LI, P, NRC, p-additivity
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,\mathbb P)$ (atomless wherever a theorem says so). Random variables are real functions $X:\Omega\to\mathbb R$; a positive value is a loss.
--
--   1. **Domains.** $L^1$ is the set of measurable, integrable $X$; $L^1_+$ is the set of $X\in L^1$ with $X(\omega)\ge 0$ for every $\omega$; for $q\in[0,\infty]$, $L^q$ is the set of measurable $X$ with finite $q$-th moment ($L^0$: all random variables, $L^\infty$: essentially bounded ones).
--   2. **Equality in law.** $X\overset{d}{=}Y$ means $\mathbb P(X\le x)=\mathbb P(Y\le x)$ for every $x\in\mathbb R$.
--   3. **Value-at-Risk and Expected Shortfall.** For $p\in(0,1)$,
--   $$\mathrm{VaR}_p(X)=\inf\{x\in\mathbb R:\mathbb P(X\le x)\ge p\},\qquad \mathrm{ES}_p(X)=\frac{1}{1-p}\int_p^1\mathrm{VaR}_q(X)\,\mathrm dq .$$
--   4. **Conditional expectation on an event.** $\mathbb E[X\mid A]=\mathbb E[X\mathbf 1_A]/\mathbb P(A)$.
--   5. **Tail events (Definition 1).** A tail event of $X$ is an event $A$ with $0<\mathbb P(A)<1$ such that $X(\omega)\ge X(\omega')$ for almost all pairs $(\omega,\omega')$ with $\omega\in A$, $\omega'\in A^c$, "almost all" with respect to $\mathbb P\times\mathbb P$. A $p$-tail event is a tail event of probability $1-p$, and $(X_1,\dots,X_n)$ is **$p$-concentrated** (Definition 2) if its components share a common $p$-tail event.
--   6. **ES aggregation (Definition 4).** $(X_1,\dots,X_n)$ maximizes the $\mathrm{ES}_p$ aggregation if $\mathrm{ES}_p(X_1'+\dots+X_n')\le \mathrm{ES}_p(X_1+\dots+X_n)$ whenever $X_i'\overset{d}{=}X_i$ for every $i$.
--   7. **Axioms** for a functional $\rho$ on a domain $\mathcal X$ (all random variables in $\mathcal X$): **M** $\rho(X)\le\rho(Y)$ whenever $X(\omega)\le Y(\omega)$ for every $\omega$; **LI** $\rho(X)=\rho(Y)$ whenever $X\overset{d}{=}Y$; **P** $\lim_k\rho(\xi_k)\ge\rho(X)$ whenever $\xi_k\to X$ pointwise and the limit exists; **NRC** there is a stress event $A$, i.e. an event with $0<\mathbb P(A)<1$ such that $\rho(X+Y)=\rho(X)+\rho(Y)$ for all $X,Y$ sharing the tail event $A$.
--   8. **Additivity.** $\rho$ is additive on $\mathcal X$ if $\rho(X+Y)=\rho(X)+\rho(Y)$ for all $X,Y\in\mathcal X$, and $p$-additive if this holds for all $X,Y$ sharing a tail event of probability $1-p$.
--
--   These objects are the vocabulary of the axiomatic characterization of ES: the four axioms single out the family $\{\mathrm{ES}_p\}$ on $L^1$.
--
--   **Formalization Note** A risk measure is any map $\rho:(\Omega\to\mathbb R)\to\mathbb R$; every axiom constrains it only on its domain argument. Axiom M uses the sure order and Axiom P pointwise convergence at every $\omega$, the weakest forms in the paper's Remark 1. $\mathrm{VaR}_p$ is the published `VaRL P (1 - p)` (small-$\alpha$ convention), and $\mathrm{ES}_p$ is the Lebesgue integral over the open interval $(p,1)$. The paper's Axiom NRC reads "there exists an event $A$"; since a tail event has $0<\mathbb P(A)<1$, the event $A=\emptyset$ would satisfy it vacuously for every $\rho$ (for instance $\mathrm{VaR}_p$), which would make Theorem 1 false. The paper's own $p=1-\mathbb P(A)\in(0,1)$ shows the intended reading, so the stress event is required to satisfy $0<\mathbb P(A)<1$; this is the one hypothesis added to the page.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), pp. 5–8 (§1.2, Axioms M, LI, P, Definition 1, Axiom NRC), p. 12 (Definition 2), p. 15 (Definition 4), pp. 18, 20 (additivity, p-additivity), p. 32 (𝔼[X|A])

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

variable {Ω : Type*} [MeasurableSpace Ω]

/-- §1.2, p. 5: `L¹`, the integrable random variables (as functions `Ω → ℝ`). -/
def L1 (P : Measure Ω) : Set (Ω → ℝ) := {X | Measurable X ∧ Integrable X P}

/-- p. 18: `L¹₊`, the non-negative integrable random variables (pointwise non-negative). -/
def L1Plus (P : Measure Ω) : Set (Ω → ℝ) := {X | X ∈ L1 P ∧ ∀ ω, 0 ≤ X ω}

/-- §1.2, p. 5: `L^q` for `q ∈ [0, ∞]`. `MemLp X 0 P` is a.e. strong measurability, so `q = 0`
gives `L⁰`, and `q = ∞` gives `L^∞`. -/
def Lq (P : Measure Ω) (q : ENNReal) : Set (Ω → ℝ) := {X | Measurable X ∧ MemLp X q P}

/-- §1.2, p. 5: `X =ᵈ Y`, the two random variables follow the same cdf. -/
def SameLaw (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ x, TailRiskSharing.VaRConv.distFn P X x = TailRiskSharing.VaRConv.distFn P Y x

/-- §1.2, p. 5: `VaRₚ(X) = inf {x ∈ ℝ : ℙ(X ≤ x) ≥ p}`, the left `p`-quantile (large-`p`
convention), expressed through the published small-`α` `VaRL` with `α = 1 - p`. -/
noncomputable def VaR (P : Measure Ω) (p : ℝ) (X : Ω → ℝ) : ℝ :=
  TailRiskSharing.VaRConv.VaRL P (1 - p) X

/-- §1.2, p. 5: `ESₚ(X) = (1 - p)⁻¹ ∫ₚ¹ VaR_q(X) dq`. -/
noncomputable def ES (P : Measure Ω) (p : ℝ) (X : Ω → ℝ) : ℝ :=
  (1 - p)⁻¹ * ∫ q in Set.Ioo p 1, VaR P q X

/-- Lemma A.7, p. 32: the elementary conditional expectation `𝔼[X | A] = 𝔼[X 1_A] / ℙ(A)`. -/
noncomputable def condExpOn (P : Measure Ω) (X : Ω → ℝ) (A : Set Ω) : ℝ :=
  (P.real A)⁻¹ * ∫ ω in A, X ω ∂P

/-- Definition 1, p. 8: `A` is a tail event of `X`: `A ∈ ℱ`, `0 < ℙ(A) < 1`, and
`X(ω) ≥ X(ω')` for `ℙ × ℙ`-almost all `(ω, ω')` with `ω ∈ A`, `ω' ∈ Aᶜ`. -/
def IsTailEvent (P : Measure Ω) [SFinite P] (X : Ω → ℝ) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ 0 < P.real A ∧ P.real A < 1 ∧
    ∀ᵐ z ∂(P.prod P), z.1 ∈ A → z.2 ∉ A → X z.2 ≤ X z.1

/-- Definition 2, p. 12: a `p`-tail event is a tail event of probability `1 - p`. -/
def IsPTailEvent (P : Measure Ω) [SFinite P] (p : ℝ) (X : Ω → ℝ) (A : Set Ω) : Prop :=
  IsTailEvent P X A ∧ P.real A = 1 - p

/-- Definition 2, p. 12: `(X₁, …, Xₙ)` is `p`-concentrated: its components share a common
tail event of probability `1 - p`. A pair `(X, Y)` is `IsPConcentrated P p ![X, Y]`. -/
def IsPConcentrated (P : Measure Ω) [SFinite P] (p : ℝ) {n : ℕ} (Xs : Fin n → Ω → ℝ) : Prop :=
  ∃ A : Set Ω, ∀ i, IsPTailEvent P p (Xs i) A

/-- Definition 4, p. 15: `(X₁, …, Xₙ)` maximizes the `ESₚ` aggregation:
`ESₚ(X₁ + ⋯ + Xₙ) ≥ ESₚ(X'₁ + ⋯ + X'ₙ)` for every `(X'₁, …, X'ₙ)` with `X'ᵢ =ᵈ Xᵢ`. Since
`(X₁, …, Xₙ)` is itself a candidate, this is "`= max`". -/
def MaximizesESAggregation (P : Measure Ω) (p : ℝ) {n : ℕ} (Xs : Fin n → Ω → ℝ) : Prop :=
  ∀ Xs' : Fin n → Ω → ℝ, (∀ i, Measurable (Xs' i)) → (∀ i, SameLaw P (Xs' i) (Xs i)) →
    ES P p (fun ω => ∑ i, Xs' i ω) ≤ ES P p (fun ω => ∑ i, Xs i ω)

/-- Axiom M, p. 6: `ρ(X) ≤ ρ(Y)` whenever `X ≤ Y` surely (at every scenario), on the domain `D`. -/
def AxiomM (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ D, ∀ Y ∈ D, (∀ ω, X ω ≤ Y ω) → ρ X ≤ ρ Y

/-- Axiom LI, p. 6: `ρ(X) = ρ(Y)` whenever `X =ᵈ Y`, on the domain `D`. -/
def AxiomLI (P : Measure Ω) (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ D, ∀ Y ∈ D, SameLaw P X Y → ρ X = ρ Y

/-- Axiom P, p. 6: `lim ρ(ξₖ) ≥ ρ(X)` whenever `ξₖ → X` pointwise and the limit exists, all
random variables in the domain `D`. -/
def AxiomP (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (ξ : ℕ → Ω → ℝ) (X : Ω → ℝ), (∀ k, ξ k ∈ D) → X ∈ D →
    (∀ ω, Tendsto (fun k => ξ k ω) atTop (𝓝 (X ω))) →
    ∀ L : ℝ, Tendsto (fun k => ρ (ξ k)) atTop (𝓝 L) → ρ X ≤ L

/-- Axiom NRC, p. 8: `A` is a stress event for `ρ` on `D`: `ρ(X + Y) = ρ(X) + ρ(Y)` for all
`X, Y ∈ D` sharing the tail event `A`. The clause `0 < ℙ(A) < 1` is an explicit addition: without
it `A = ∅` (which is a tail event of nothing) satisfies the axiom vacuously for every `ρ`. -/
def IsStressEvent (P : Measure Ω) [SFinite P] (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ)
    (A : Set Ω) : Prop :=
  MeasurableSet A ∧ 0 < P.real A ∧ P.real A < 1 ∧
    ∀ X ∈ D, ∀ Y ∈ D, IsTailEvent P X A → IsTailEvent P Y A → ρ (X + Y) = ρ X + ρ Y

/-- Axiom NRC, p. 8: there exists a stress event. -/
def AxiomNRC (P : Measure Ω) [SFinite P] (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∃ A : Set Ω, IsStressEvent P D ρ A

/-- p. 20 (and Proposition 4, p. 11): `ρ` is `p`-additive on `D`: `ρ(X + Y) = ρ(X) + ρ(Y)` for
all `X, Y ∈ D` sharing a tail event of probability `1 - p`. -/
def IsPAdditive (P : Measure Ω) [SFinite P] (p : ℝ) (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) :
    Prop :=
  ∀ X ∈ D, ∀ Y ∈ D, IsPConcentrated P p ![X, Y] → ρ (X + Y) = ρ X + ρ Y

/-- p. 18: `ρ` is additive on `D`: `ρ(X + Y) = ρ(X) + ρ(Y)` for all `X, Y ∈ D`. -/
def IsAdditiveOn (D : Set (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ D, ∀ Y ∈ D, ρ (X + Y) = ρ X + ρ Y

end ESAxioms.Characterization


