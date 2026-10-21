-- Prove2me | Definitions.Def_CompoundSMM_Conv_Setting
-- name    : CompoundSMM_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:46.919277+00:00
-- url     : https://prove2.me/theorems/8f611519-98fd-4a0b-9f38-0763581f5491
-- title:
--   (1), (A1)–(A4), (6)–(9), SMM, Lemma 3, (E∞), pp. 1–11 — compound SP, surrogate families, the SMM run
-- statement:
--   This file sets up the compound stochastic program of Liu, Cui and Pang and the stochastic majorization–minimization (SMM) algorithm that solves it.
--
--   **The problem (1).** Let $\tilde\xi$ be a random variable with law $\mu$ on a measurable space $\Xi$, let $X\subseteq\mathbb R^n$, and let $G:\mathbb R^n\times\Xi\to\mathbb R^{\ell_G}$, $F:\mathbb R^n\times\Xi\to\mathbb R^{\ell_F}$ (with $\ell_G+\ell_F>0$), $\varphi:\mathbb R^{\ell_G}\times\mathbb R^{\ell_F}\to\mathbb R^{\ell_\varphi}$ (with $\ell_\varphi>0$) and $\psi:\mathbb R^{\ell_\varphi}\to\mathbb R$. The maps $G,F$ are Carathéodory (continuous in $x$ on $X$ for every $\xi$, integrable in $\xi$ for every $x\in X$) and $\varphi,\psi$ are continuous. The objective is
--
--   $$\Theta(x)=\psi\Big(\mathbb E\big[\varphi\big(G(x,\tilde\xi),\ \mathbb E[F(x,\tilde\xi)]\big)\big]\Big).$$
--
--   Given samples $\xi^1,\dots,\xi^n$ and $\eta^1,\dots,\eta^m$, the sample average approximation (9) is $\overline\Theta_{n,m}(x)=\psi\big(\tfrac1n\sum_{t=1}^n\varphi(G(x,\xi^t),\tfrac1m\sum_{s=1}^mF(x,\eta^s))\big)$.
--
--   **Assumptions.** A map $\varphi:\mathbb R^k\to\mathbb R^\ell$ is *isotone* if $u\le v$ componentwise implies $\varphi(u)\le\varphi(v)$ componentwise.
--   1. (A1) $X$ is nonempty, convex and compact.
--   2. (A2) $\psi$ and $\varphi$ are isotone and Lipschitz with constants $\mathrm{Lip}_\psi$, $\mathrm{Lip}_\varphi$ (Euclidean norms; for $\varphi$ the norm of the pair $(a,b)$), and $\psi$ and every component $\varphi_j$ are convex.
--   3. (A3$_G$) For every $x'\in X$ and $\xi$ there is a nonempty family $\mathcal G(x',\xi)$ of maps $\widehat G(\bullet,\xi;x')$ that touch $G$ at $x'$, majorize $G(\bullet,\xi)$ componentwise on $X$, are componentwise convex on $X$, and satisfy the uniform outer semicontinuity condition (4) with an integrable modulus $L\ge0$: for every sequence $x^\nu\to x^\infty$ in $X$ and every selection $\widehat G(\bullet,\xi;x^\nu)\in\mathcal G(x^\nu,\xi)$ bounded on $X$ uniformly in $\nu$ (for each $\xi$), there are a selection $\widehat G(\bullet,\xi;x^\infty)\in\mathcal G(x^\infty,\xi)$ and an infinite set $\mathcal K$ of indices such that for every $x\in X$ and $\varepsilon>0$ some $\bar\nu(x,\varepsilon)$ gives $\|\widehat G(x,\xi;x^\nu)-\widehat G(x,\xi;x^\infty)\|\le\varepsilon L(\xi)$ for all $\nu\in\mathcal K$, $\nu\ge\bar\nu$, and all $\xi$. (A3$_F$) is the same for $F$ and a family $\mathcal F$.
--   4. (A4) For every $x\in X$, $F(x,\tilde\xi)$ and $G(x,\tilde\xi)$ are square integrable with $\mathbb E\|F(x,\tilde\xi)-\mathbb E F(x,\tilde\xi)\|^2\le\sigma_F^2$ and $\mathbb E\|G(x,\tilde\xi)-\mathbb E G(x,\tilde\xi)\|^2\le\sigma_G^2$, where $\sigma_F,\sigma_G\ge0$.
--
--   **Surrogates (6), (8).** For selections $\widehat G(\bullet,\xi;x')\in\mathcal G(x',\xi)$, $\widehat F(\bullet,\xi;x')\in\mathcal F(x',\xi)$ (one for every $\xi$),
--
--   $$\widehat V(x;x')=\psi\Big(\mathbb E\big[\varphi\big(\widehat G(x,\tilde\xi;x'),\ \mathbb E[\widehat F(x,\tilde\xi;x')]\big)\big]\Big),$$
--
--   and $\widehat V(\bullet;x')$ is a *well-defined member* of $\mathcal V(x')$ when $\widehat G(x,\tilde\xi;x')$, $\widehat F(x,\tilde\xi;x')$ and $\varphi(\widehat G(x,\tilde\xi;x'),\mathbb E[\widehat F(x,\tilde\xi;x')])$ are integrable for every $x\in X$. The sample surrogate is $\widehat V_N(x;x')=\psi\big(\tfrac1N\sum_{t=1}^N\varphi(\widehat G^t(x),\tfrac1N\sum_{s=1}^N\widehat F^s(x))\big)$ for selected surrogates $\widehat G^t$, $\widehat F^s$.
--
--   **Sample sizes (Lemma 3).** There are a positive integer $\bar\nu$ and scalars $c_1>0$, $c_2>0$, $c_3<\bar\nu$ with $\max\{N_{\nu-1}+1,\ c_2\nu^{1+2c_1}\}\le N_\nu\le N_{\nu-1}/(1-c_3/\nu)$ for all $\nu>\bar\nu$.
--
--   **Condition (E$_\infty$) at $x^\infty$.** For almost every $\xi$ the members of $\mathcal G(x^\infty,\xi)$ are continuous on $X$ and form a compact convex subset of $C(X)$ with the supremum norm, and $\sup\{\sup_{x\in X}\|\widehat G(x,\xi;x^\infty)\|\}$ over the family is bounded by an integrable function of $\xi$.
--
--   **An SMM run (pp. 8–9).** On a probability space $(\Omega,\mathbb P)$: two sequences $\xi^1,\xi^2,\dots$ and $\eta^1,\eta^2,\dots$ that are jointly independent with law $\mu$; sample sizes $N_0=0\le N_1\le N_2\le\cdots$ with $N_\nu>0$ for $\nu\ge1$; at iteration $\nu$ a surrogate is chosen at every sample from the family at the current iterate $x^\nu$; and starting from $x^0=x^1\in X$, for $\nu\ge1$
--
--   $$x^{\nu+1}\in\operatorname*{argmin}_{x\in X}\Big\{\widehat V_{N_\nu}(x;x^\nu)+\tfrac1{2\rho}\|x-x^\nu\|^2\Big\}.$$
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note.** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`; $\varphi$ is curried in $(G,F)$; isotonicity is componentwise, jointly in both arguments of $\varphi$; convexity of $\psi$ and $\varphi_j$ is on the whole space. The open set $\mathcal O\supseteq X$ of the paper is dropped (maps are total and only their values on $X$ are used). Sample indices are 0-based. Added relative to the page, each implicit in it: nonempty surrogate families; $c_1,c_2>0$ in Lemma 3 (without them $N_\nu=\nu$ qualifies and the lemma fails); $\sigma_F,\sigma_G\ge0$; measurability of the samples, of the iterates and (jointly in base point and sample) of the surrogate selectors; $x^1:=x^0$ (the page leaves $x^1$ undefined). In a run the surrogate chosen at a sample depends on the iteration, the current iterate and the sample value, not on the sample's index. (E$_\infty$)'s expectation of a supremum is encoded as an integrable envelope.
-- source:
--   Liu, Cui & Pang, Solving nonsmooth and nonconvex compound stochastic programs with applications to risk measure minimization, arXiv:2004.14342v3, pp. 1–11, problem (1), §1.2 (isotone), (A1)–(A3), (6)–(8), the SMM algorithm, (9), (A4), Lemma 3, (E∞)

import Mathlib

namespace CompoundSMM.Conv

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

/-- `ℝ^k` with the Euclidean norm. -/
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Isotone (§1.2, p. 4): `u ≤ v` componentwise implies `φ u ≤ φ v` componentwise. -/
def Isotone {k l : ℕ} (φ : E k → E l) : Prop :=
  ∀ u v : E k, (∀ i, u i ≤ v i) → ∀ j, φ u j ≤ φ v j

/-- Isotone for a real-valued map (`ℓ = 1` in §1.2, p. 4). -/
def IsotoneReal {k : ℕ} (ψ : E k → ℝ) : Prop :=
  ∀ u v : E k, (∀ i, u i ≤ v i) → ψ u ≤ ψ v

/-- Isotone for a map of the pair `(a, b) ∈ ℝ^{ℓG} × ℝ^{ℓF} = ℝ^ℓ`, jointly in both arguments. -/
def Isotone₂ {k₁ k₂ l : ℕ} (φ : E k₁ → E k₂ → E l) : Prop :=
  ∀ a a' : E k₁, ∀ b b' : E k₂, (∀ i, a i ≤ a' i) → (∀ i, b i ≤ b' i) →
    ∀ j, φ a b j ≤ φ a' b' j

/-- The data of the compound stochastic program (1), pp. 1–2: the law `μ` of `ξ̃` on `Ξ`, the
feasible set `X`, the Carathéodory maps `G`, `F`, the outer maps `φ` (curried in `(G, F)`) and `ψ`. -/
structure CompoundSP (n ℓG ℓF ℓφ : ℕ) (Ξ : Type*) [MeasurableSpace Ξ] where
  μ : Measure Ξ
  isProb : IsProbabilityMeasure μ
  X : Set (E n)
  G : E n → Ξ → E ℓG
  F : E n → Ξ → E ℓF
  φ : E ℓG → E ℓF → E ℓφ
  ψ : E ℓφ → ℝ
  dims : 0 < ℓG + ℓF ∧ 0 < ℓφ
  carathG : (∀ ξ, ContinuousOn (fun x => G x ξ) X) ∧ ∀ x ∈ X, Integrable (G x) μ
  carathF : (∀ ξ, ContinuousOn (fun x => F x ξ) X) ∧ ∀ x ∈ X, Integrable (F x) μ
  contφ : Continuous (fun p : E ℓG × E ℓF => φ p.1 p.2)
  contψ : Continuous ψ

variable {n ℓG ℓF ℓφ k : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- The objective `Θ(x) = ψ(E[φ(G(x, ξ̃), E[F(x, ξ̃)])])` of (1). -/
noncomputable def Θ (P : CompoundSP n ℓG ℓF ℓφ Ξ) (x : E n) : ℝ :=
  P.ψ (∫ ξ, P.φ (P.G x ξ) (∫ ζ, P.F x ζ ∂P.μ) ∂P.μ)

/-- The SAA function `Θ̄_{n,m}` of (9), p. 9, with 0-based sample indices: the page's `ξ^t` is
`ξs (t - 1)`. -/
noncomputable def Θbar (P : CompoundSP n ℓG ℓF ℓφ Ξ) (nn m : ℕ) (ξs ηs : ℕ → Ξ) (x : E n) : ℝ :=
  P.ψ ((1 / (nn : ℝ)) • ∑ t ∈ Finset.range nn,
        P.φ (P.G x (ξs t)) ((1 / (m : ℝ)) • ∑ s ∈ Finset.range m, P.F x (ηs s)))

/-- (A1), p. 6: `X` is nonempty, convex and compact. -/
def A1 (P : CompoundSP n ℓG ℓF ℓφ Ξ) : Prop :=
  P.X.Nonempty ∧ Convex ℝ P.X ∧ IsCompact P.X

/-- (A2), p. 6: `ψ` and `φ` are isotone and Lipschitz with constants `Lψ = Lip_ψ`,
`Lφ = Lip_φ` (Euclidean norms; for `φ` the norm of the pair in `ℝ^{ℓG} × ℝ^{ℓF} = ℝ^ℓ`), and `ψ`
and each component `φ_j` are convex. -/
def A2 (P : CompoundSP n ℓG ℓF ℓφ Ξ) (Lψ Lφ : ℝ) : Prop :=
  0 ≤ Lψ ∧ 0 ≤ Lφ ∧
  IsotoneReal P.ψ ∧ Isotone₂ P.φ ∧
  (∀ u v : E ℓφ, |P.ψ u - P.ψ v| ≤ Lψ * ‖u - v‖) ∧
  (∀ (a a' : E ℓG) (b b' : E ℓF),
    ‖P.φ a b - P.φ a' b'‖ ≤ Lφ * Real.sqrt (‖a - a'‖ ^ 2 + ‖b - b'‖ ^ 2)) ∧
  ConvexOn ℝ Set.univ P.ψ ∧
  ∀ j, ConvexOn ℝ Set.univ (fun p : E ℓG × E ℓF => P.φ p.1 p.2 j)

/-- (A4), p. 9: `sup_{x∈X} (E‖F(x, ξ̃) − E F(x, ξ̃)‖²)^{1/2} ≤ σF`, and the same for `G` with `σG`. -/
def A4 (P : CompoundSP n ℓG ℓF ℓφ Ξ) (σF σG : ℝ) : Prop :=
  0 ≤ σF ∧ 0 ≤ σG ∧
  ∀ x ∈ P.X, MemLp (P.F x) 2 P.μ ∧ MemLp (P.G x) 2 P.μ ∧
    ∫ ξ, ‖P.F x ξ - ∫ ζ, P.F x ζ ∂P.μ‖ ^ 2 ∂P.μ ≤ σF ^ 2 ∧
    ∫ ξ, ‖P.G x ξ - ∫ ζ, P.G x ζ ∂P.μ‖ ^ 2 ∂P.μ ≤ σG ^ 2

/-- (A3G)/(A3F), p. 6, for a map `H` (`G` or `F`) and a surrogate family `𝒢 x' ξ`:
nonempty (implicit on the page), (1) touching, (2) majorization on `X`, (3) componentwise
convexity on `X`, and (4) uniform outer semicontinuity with an integrable modulus `L ≥ 0`. -/
def SurrogateFamily (X : Set (E n)) (μ : Measure Ξ) (H : E n → Ξ → E k)
    (𝒢 : E n → Ξ → Set (E n → E k)) : Prop :=
  (∀ x' ∈ X, ∀ ξ, (𝒢 x' ξ).Nonempty) ∧
  (∀ x' ∈ X, ∀ ξ, ∀ g ∈ 𝒢 x' ξ, g x' = H x' ξ) ∧
  (∀ x' ∈ X, ∀ ξ, ∀ g ∈ 𝒢 x' ξ, ∀ x ∈ X, ∀ i, H x ξ i ≤ g x i) ∧
  (∀ x' ∈ X, ∀ ξ, ∀ g ∈ 𝒢 x' ξ, ∀ i, ConvexOn ℝ X (fun x => g x i)) ∧
  ∃ L : Ξ → ℝ, (∀ ξ, 0 ≤ L ξ) ∧ Integrable L μ ∧
    ∀ (xs : ℕ → E n) (xinf : E n), (∀ ν, xs ν ∈ X) → Tendsto xs atTop (𝓝 xinf) →
    ∀ gs : ℕ → Ξ → (E n → E k), (∀ ν ξ, gs ν ξ ∈ 𝒢 (xs ν) ξ) →
      (∀ ξ, ∃ M : ℝ, ∀ ν, ∀ x ∈ X, ‖gs ν ξ x‖ ≤ M) →
      ∃ ginf : Ξ → (E n → E k), (∀ ξ, ginf ξ ∈ 𝒢 xinf ξ) ∧ ∃ K : Set ℕ, K.Infinite ∧
        ∀ x ∈ X, ∀ ε > 0, ∃ νbar : ℕ, ∀ ν ∈ K, νbar ≤ ν → ∀ ξ,
          ‖gs ν ξ x - ginf ξ x‖ ≤ ε * L ξ

/-- `V̂(x; x′)` of (6), p. 8, for the selections `g ξ = Ĝ(•, ξ; x′)`, `f ξ = F̂(•, ξ; x′)`. -/
noncomputable def Vhat (P : CompoundSP n ℓG ℓF ℓφ Ξ) (g : Ξ → E n → E ℓG) (f : Ξ → E n → E ℓF)
    (x : E n) : ℝ :=
  P.ψ (∫ ξ, P.φ (g ξ x) (∫ ζ, f ζ x ∂P.μ) ∂P.μ)

/-- A well-defined member `V̂(•; x′)` of `V(x′)` (p. 8): selections from the families for every
`ξ`, with `Ĝ(x, ξ̃; x′)`, `F̂(x, ξ̃; x′)` and the inner composite integrable for every `x ∈ X`. -/
def WellDefinedMember (P : CompoundSP n ℓG ℓF ℓφ Ξ) (𝒢 : E n → Ξ → Set (E n → E ℓG))
    (ℱ : E n → Ξ → Set (E n → E ℓF)) (x' : E n) (g : Ξ → E n → E ℓG) (f : Ξ → E n → E ℓF) :
    Prop :=
  (∀ ξ, g ξ ∈ 𝒢 x' ξ) ∧ (∀ ξ, f ξ ∈ ℱ x' ξ) ∧
  ∀ x ∈ P.X, Integrable (fun ξ => g ξ x) P.μ ∧ Integrable (fun ξ => f ξ x) P.μ ∧
    Integrable (fun ξ => P.φ (g ξ x) (∫ ζ, f ζ x ∂P.μ)) P.μ

/-- The sample surrogate of (8)/(14): `ψ((1/N) Σ_{t<N} φ(g_t(x), (1/N) Σ_{s<N} f_s(x)))`, where
`g_t = Ĝ^t(•, ξ^t; x′)` and `f_s = F̂^s(•, η^s; x′)` are the selected surrogates (0-based). -/
noncomputable def VN (P : CompoundSP n ℓG ℓF ℓφ Ξ) (N : ℕ) (gs : ℕ → E n → E ℓG)
    (fs : ℕ → E n → E ℓF) (x : E n) : ℝ :=
  P.ψ ((1 / (N : ℝ)) • ∑ t ∈ Finset.range N,
        P.φ (gs t x) ((1 / (N : ℝ)) • ∑ s ∈ Finset.range N, fs s x))

/-- Lemma 3's sample-size conditions, p. 10, with `c₁ > 0` and `c₂ > 0` (added, necessary):
a positive integer `ν̄` and scalars `c₃ < ν̄` with
`max{N_{ν−1} + 1, c₂ ν^{1+2c₁}} ≤ N_ν ≤ N_{ν−1} / (1 − c₃/ν)` for all `ν > ν̄`. -/
def SampleSizeCond (N : ℕ → ℕ) : Prop :=
  ∃ νbar : ℕ, 0 < νbar ∧ ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ c3 < νbar ∧
    ∀ ν : ℕ, νbar < ν →
      max ((N (ν - 1) : ℝ) + 1) (c2 * (ν : ℝ) ^ (1 + 2 * c1)) ≤ N ν ∧
      (N ν : ℝ) ≤ N (ν - 1) / (1 - c3 / ν)

/-- Condition (E∞), p. 11, for one family at `xinf`: for almost every `ξ`, the members of
`𝒢(xinf, ξ)` are continuous on `X` and, as elements of `C(X)` with the supremum norm, form a
compact convex set; and `sup{sup_{x∈X} ‖Ĝ(x, ξ; xinf)‖ | Ĝ ∈ 𝒢(xinf, ξ)}` has an integrable
envelope. -/
def EinfFamily (X : Set (E n)) (μ : Measure Ξ) (𝒢 : E n → Ξ → Set (E n → E k)) (xinf : E n) :
    Prop :=
  (∀ᵐ ξ ∂μ, (∀ g ∈ 𝒢 xinf ξ, ContinuousOn g X) ∧
     IsCompact {h : X →ᵇ E k | ∃ g ∈ 𝒢 xinf ξ, ∀ y : X, h y = g y} ∧
     Convex ℝ {h : X →ᵇ E k | ∃ g ∈ 𝒢 xinf ξ, ∀ y : X, h y = g y}) ∧
  ∃ Hb : Ξ → ℝ, Integrable Hb μ ∧ ∀ᵐ ξ ∂μ, ∀ g ∈ 𝒢 xinf ξ, ∀ y ∈ X, ‖g y‖ ≤ Hb ξ

/-- Two independent i.i.d. sample sequences `ξs`, `ηs` on `(Ω, Pr)`, each with law `μ`: the whole
family `(ξs t)_t ∪ (ηs s)_s` is mutually independent. -/
def IIDSamples {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (μ : Measure Ξ)
    (ξs ηs : ℕ → Ω → Ξ) : Prop :=
  (∀ t, Measurable (ξs t)) ∧ (∀ s, Measurable (ηs s)) ∧
  iIndepFun (fun i : ℕ ⊕ ℕ => Sum.elim ξs ηs i) Pr ∧
  (∀ t, Measure.map (ξs t) Pr = μ) ∧ (∀ s, Measure.map (ηs s) Pr = μ)

/-- One run of the SMM algorithm, pp. 8–9, on a probability space `(Ω, Pr)`: i.i.d. samples, sample
sizes `N` with `N 0 = 0`, surrogate selectors depending on the iteration, the base point and the
sample value, the start `x⁰ ∈ X` (with `x¹ := x⁰`), and iterates `x (ν+1)` minimizing
`V̂_{N_ν}(•; x^ν) + ‖• − x^ν‖² / (2ρ)` over `X` for `ν ≥ 1`. -/
structure SMMRun (P : CompoundSP n ℓG ℓF ℓφ Ξ) (𝒢 : E n → Ξ → Set (E n → E ℓG))
    (ℱ : E n → Ξ → Set (E n → E ℓF)) (ρ : ℝ) (Ω : Type*) [MeasurableSpace Ω] where
  Pr : Measure Ω
  isProb : IsProbabilityMeasure Pr
  ξs : ℕ → Ω → Ξ
  ηs : ℕ → Ω → Ξ
  iid : IIDSamples Pr P.μ ξs ηs
  N : ℕ → ℕ
  hN : N 0 = 0 ∧ Monotone N ∧ ∀ ν, 1 ≤ ν → 0 < N ν
  gsel : ℕ → E n → Ξ → (E n → E ℓG)
  fsel : ℕ → E n → Ξ → (E n → E ℓF)
  hsel : ∀ ν, ∀ x' ∈ P.X, ∀ ξ, gsel ν x' ξ ∈ 𝒢 x' ξ ∧ fsel ν x' ξ ∈ ℱ x' ξ
  hselMeas : ∀ ν (y : E n), Measurable (fun p : E n × Ξ => gsel ν p.1 p.2 y) ∧
    Measurable (fun p : E n × Ξ => fsel ν p.1 p.2 y)
  x0 : E n
  hx0 : x0 ∈ P.X
  x : ℕ → Ω → E n
  hx01 : ∀ ω, x 0 ω = x0 ∧ x 1 ω = x0
  hmeas : ∀ ν, Measurable (x ν)
  hstep : ∀ ν, 1 ≤ ν → ∀ ω, x (ν + 1) ω ∈ P.X ∧
    ∀ y ∈ P.X,
      VN P (N ν) (fun t => gsel ν (x ν ω) (ξs t ω)) (fun s => fsel ν (x ν ω) (ηs s ω))
          (x (ν + 1) ω) + ‖x (ν + 1) ω - x ν ω‖ ^ 2 / (2 * ρ)
        ≤ VN P (N ν) (fun t => gsel ν (x ν ω) (ξs t ω)) (fun s => fsel ν (x ν ω) (ηs s ω)) y
          + ‖y - x ν ω‖ ^ 2 / (2 * ρ)

end CompoundSMM.Conv


