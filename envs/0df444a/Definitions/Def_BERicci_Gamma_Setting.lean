-- Prove2me | Definitions.Def_BERicci_Gamma_Setting
-- name    : BERicci_Gamma_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:57.067208+00:00
-- url     : https://prove2.me/theorems/5322159f-ef6f-4513-a272-b6062b902e6d
-- title:
--   §2–§3, pp. 10–40 — Dirichlet form, heat flow, Γ, BE(K,N) (Def. 2.4), d_E, slope, Cheeger energy, W₂, Ent_m, Energy and Riemannian Energy measure spaces, RCD(K,∞)
-- statement:
--   This module fixes the analytic setting of Ambrosio–Gigli–Savaré. Let $(X,\mathcal B)$ be a measurable space with a $\sigma$-additive measure $m$.
--
--   1. A **symmetric Dirichlet form** $\mathcal E:L^2(X,m)\to[0,\infty]$ is an $L^2$-lower semicontinuous quadratic form whose domain $\mathbb V=\{f:\mathcal E(f)<\infty\}$ is dense in $L^2(X,m)$, and which satisfies the Markov property $\mathcal E(\eta\circ f)\le\mathcal E(f)$ for every normal contraction $\eta$ (1-Lipschitz, $\eta(0)=0$). Its bilinear form is $\mathcal E(f,g)=\tfrac14(\mathcal E(f+g)-\mathcal E(f-g))$, and $\mathbb V_\infty=\mathbb V\cap L^\infty(X,m)$.
--   2. $\mathcal E$ is **strongly local** if $\mathcal E(f,g)=0$ for $f,g\in\mathbb V$ whenever $(f+a)g=0$ $m$-a.e. for some constant $a$.
--   3. The **generator** $\Delta_{\mathcal E}$ is defined by $\mathcal E(f,g)=-\int_X g\,\Delta_{\mathcal E}f\,dm$ for all $g\in\mathbb V$, and the **heat flow** $(\mathsf P_t)_{t\ge0}$ is characterized by: $t\mapsto\mathsf P_tf$ is $C^1$ on $(0,\infty)$ in $L^2$ with values in $D(\Delta_{\mathcal E})$, $\frac{d}{dt}\mathsf P_tf=\Delta_{\mathcal E}\mathsf P_tf$, and $\mathsf P_tf\to f$ in $L^2$ as $t\downarrow0$.
--   4. For $f,\varphi\in\mathbb V_\infty$, $\Gamma[f;\varphi]=\mathcal E(f,f\varphi)-\tfrac12\mathcal E(f^2,\varphi)$. A function $f\in\mathbb V$ belongs to $\mathbb G$, with **carré du champ** $\Gamma(f)\in L^1_+(X,m)$, if $\Gamma[f;\varphi]=\int_X\Gamma(f)\varphi\,dm$ for every $\varphi\in\mathbb V_\infty$ (for unbounded $f$ the left side is taken along the truncations $-n\vee f\wedge n$).
--   5. With $I_K(t)=\int_0^te^{Ks}\,ds$, $I_{K,2}(t)=\int_0^tI_K(s)\,ds$ and $\mathsf A_t[f;\varphi](s)=\tfrac12\int_X(\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$, the form satisfies **$BE(K,N)$**, $\nu=1/N\ge0$, if for every $f\in L^2$, nonnegative $\varphi\in L^2\cap L^\infty$ and $t>0$
--   $$\frac{\partial^2}{\partial s^2}\mathsf A_t[f;\varphi](s)\ge 2K\frac{\partial}{\partial s}\mathsf A_t[f;\varphi](s)+4\nu\,\mathsf A^\Delta_t[f;\varphi](s)\quad\text{in }\mathscr D'(0,t),$$
--   where $\mathsf A^\Delta_t[f;\varphi](s)=\tfrac12\int_X(\Delta_{\mathcal E}\mathsf P_{t-s}f)^2\mathsf P_s\varphi\,dm$.
--
--   The module also defines the intrinsic distance $d_{\mathcal E}$, the slope and asymptotic Lipschitz constant, the Cheeger energy, the quadratic Wasserstein cost, the relative entropy, the length property, (MD.b), (MD.exp), Energy and Riemannian Energy measure spaces (Definitions 3.6, 3.13, 3.16) and $RCD(K,\infty)$ (Definition 3.1), which the later missions of the series use.
--
--   **Formalization Note** An element of $L^2$ is represented by a function $f$ with `MemLp f 2 m`, and every predicate is invariant under $m$-a.e. equality; the $m$-completion of $\mathcal B$ is not modelled. $\mathcal E$ takes the value $\infty$ off $L^2$. The carré du champ is a predicate on a candidate density, so no density is chosen. $BE$ tests the distributional inequality against nonnegative smooth $\zeta$ with compact support in $(0,t)$, integrated by parts twice: $-2K\int\mathsf A\zeta'+4\nu\int\mathsf A^\Delta\zeta\le\int\mathsf A\zeta''$. The Bochner integrals in $\mathsf A_t$, $\mathsf A^\Delta_t$ are those of integrable functions, because $\mathsf P_s$ is sub-Markovian and maps $L^\infty$ to $L^\infty$. $I_K$, $I_{K,2}$ are defined by their integrals, so $K=0$ needs no separate case. The length of a curve is its variation on $[0,1]$; this gives the same infimum in (3.2) as $\int|\dot\gamma|$ over absolutely continuous curves. $W_2^2$, the slopes, the Cheeger energy and $d_{\mathcal E}$ are extended-valued, so no supremum or infimum is taken over an empty or unbounded real set. $\mathrm{Ent}_m(\rho)=\int(f\log f)^+\,dm-\int(f\log f)^-\,dm$ in $[-\infty,+\infty]$ for $\rho=f\,m$, and $+\infty$ unless $\rho\ll m$; statements that use it assume $m$ $\sigma$-finite. In $RCD(K,\infty)$ the inequality (3.14) is required together with $\mathrm{Ent}_m(\mathsf H_t\rho)<\infty$: this is what makes its left side a meaningful sum on the page, and it rules out the extended-real corner where an upper right derivative $-\infty$ plus an entropy $+\infty$ would satisfy (3.14) vacuously. The completeness and separability of $X$ in Definitions 3.1 and 3.6 are hypotheses of each statement that uses them.
-- source:
--   arXiv:1209.5786v4, (2.1)–(2.5), pp. 10–11; heat flow, p. 12; (2.23)–(2.24), p. 15; (2.29), p. 17; (2.33) and Definition 2.4, pp. 18–20; §3.1, (3.2), (3.12), Definition 3.1, pp. 21–25; Definitions 3.6, 3.13, 3.16, (MD.b), (MD.exp), pp. 21, 31–40

import Mathlib

namespace BERicci.Gamma

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

variable {X : Type*} [MeasurableSpace X]

/-- `fs n → f` strongly in `L²(X, m)`. -/
def L2Tendsto (m : Measure X) (fs : ℕ → X → ℝ) (f : X → ℝ) : Prop :=
  (∀ n, MemLp (fs n) 2 m) ∧ MemLp f 2 m ∧
    Tendsto (fun n => eLpNorm (fs n - f) 2 m) atTop (𝓝 0)

/-- (2.1)–(2.2), p. 10: `E : L²(X, m) → [0, ∞]` is a symmetric Dirichlet form with dense domain,
written on functions (`E f = ∞` off `L²`, `E` invariant under `m`-a.e. equality). -/
structure IsDirichletForm (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Prop where
  ae_congr : ∀ f g : X → ℝ, f =ᵐ[m] g → E f = E g
  top_of_not_memLp : ∀ f : X → ℝ, ¬ MemLp f 2 m → E f = ⊤
  smul : ∀ (c : ℝ) (f : X → ℝ), E (c • f) = ENNReal.ofReal (c ^ 2) * E f
  parallelogram : ∀ f g : X → ℝ, E (f + g) + E (f - g) = 2 * E f + 2 * E g
  lsc : ∀ (fs : ℕ → X → ℝ) (f : X → ℝ), L2Tendsto m fs f →
    E f ≤ liminf (fun n => E (fs n)) atTop
  markov : ∀ η : ℝ → ℝ, LipschitzWith 1 η → η 0 = 0 → ∀ f : X → ℝ, E (η ∘ f) ≤ E f
  dense : ∀ f : X → ℝ, MemLp f 2 m → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ g : X → ℝ, E g < ⊤ ∧ eLpNorm (f - g) 2 m < ε

/-- `𝕍 = D(E)` (p. 10). -/
def domain (E : (X → ℝ) → ℝ≥0∞) : Set (X → ℝ) := {f | E f < ⊤}

/-- `𝕍∞ = D(E) ∩ L∞(X, m)` (p. 10). -/
def domainInf (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Set (X → ℝ) :=
  {f | E f < ⊤ ∧ MemLp f ⊤ m}

/-- The bilinear form `E(f, g) = ¼(E(f + g) − E(f − g))` on `𝕍` (p. 10). -/
noncomputable def bilin (E : (X → ℝ) → ℝ≥0∞) (f g : X → ℝ) : ℝ :=
  ((E (f + g)).toReal - (E (f - g)).toReal) / 4

/-- Strong locality (p. 10). -/
def IsStronglyLocal (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Prop :=
  ∀ f g : X → ℝ, E f < ⊤ → E g < ⊤ → ∀ a : ℝ,
    (∀ᵐ x ∂m, (f x + a) * g x = 0) → bilin E f g = 0

/-- Truncation `−n ∨ f ∧ n` (proof of Lemma 2.1, p. 16). -/
def trunc (n : ℕ) (f : X → ℝ) : X → ℝ := fun x => max (-(n : ℝ)) (min (f x) n)

/-- `Γ[f; φ] = E(f, fφ) − ½ E(f², φ)` for `f, φ ∈ 𝕍∞` (2.3). -/
noncomputable def gammaForm (E : (X → ℝ) → ℝ≥0∞) (f φ : X → ℝ) : ℝ :=
  bilin E f (f * φ) - bilin E (f * f) φ / 2

/-- (2.5): `f ∈ 𝔾` with Carré du champ density `g = Γ(f) ∈ L¹₊`. For `f ∈ 𝕍` the form `Γ[f; φ]`
is the continuous extension (2.20), taken along the truncations of `f`. -/
def IsCarreDuChamp (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (f g : X → ℝ) : Prop :=
  E f < ⊤ ∧ Integrable g m ∧ 0 ≤ᵐ[m] g ∧
    ∀ φ ∈ domainInf m E,
      Tendsto (fun n => gammaForm E (trunc n f) φ) atTop (𝓝 (∫ x, g x * φ x ∂m))

/-- `𝔾` (2.5). -/
def carreDomain (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Set (X → ℝ) :=
  {f | ∃ g, IsCarreDuChamp m E f g}

/-- `f ∈ D(Δ_E)` and `Δ_E f = h`: `E(f, g) = −∫ g h dm` for all `g ∈ 𝕍` (p. 12). -/
def IsGenerator (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (f h : X → ℝ) : Prop :=
  E f < ⊤ ∧ MemLp h 2 m ∧ ∀ g : X → ℝ, E g < ⊤ → bilin E f g = - ∫ x, g x * h x ∂m

/-- The heat flow of `E` on `L²(X, m)` (p. 12): `t ↦ P t f` is differentiable on `(0, ∞)` in `L²`
with values in `D(Δ_E)`, derivative `Δ_E P t f`, and tends to `f` in `L²` as `t ↓ 0`. -/
structure IsHeatSemigroup (m : Measure X) (E : (X → ℝ) → ℝ≥0∞)
    (P : ℝ → (X → ℝ) → X → ℝ) : Prop where
  ae_congr : ∀ t : ℝ, ∀ f g : X → ℝ, f =ᵐ[m] g → P t f =ᵐ[m] P t g
  memLp : ∀ t : ℝ, 0 ≤ t → ∀ f : X → ℝ, MemLp f 2 m → MemLp (P t f) 2 m
  zero : ∀ f : X → ℝ, P 0 f =ᵐ[m] f
  tendsto_zero : ∀ f : X → ℝ, MemLp f 2 m →
    Tendsto (fun t => eLpNorm (P t f - f) 2 m) (𝓝[>] 0) (𝓝 0)
  hasDeriv : ∀ f : X → ℝ, MemLp f 2 m → ∀ t : ℝ, 0 < t → ∃ h : X → ℝ,
    IsGenerator m E (P t f) h ∧
      Tendsto (fun s => eLpNorm ((s - t)⁻¹ • (P s f - P t f) - h) 2 m) (𝓝[≠] t) (𝓝 0)

/-- `I_K(t) = ∫₀ᵗ e^{Ks} ds` and `I_{K,2}(t) = ∫₀ᵗ I_K(s) ds` (2.29); the integral form needs no
case `K = 0`. -/
noncomputable def IK (K t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.exp (K * s)

noncomputable def IK2 (K t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, IK K s

/-- `A_t[f; φ](s) = ½ ∫ (P_{t−s} f)² P_s φ dm` (2.23). -/
noncomputable def At (m : Measure X) (P : ℝ → (X → ℝ) → X → ℝ) (f φ : X → ℝ) (t s : ℝ) : ℝ :=
  (1 / 2) * ∫ x, (P (t - s) f x) ^ 2 * P s φ x ∂m

/-- **Definition 2.4** (p. 20) through Corollary 2.3 (iii), (2.33): `BE(K, N)` with `ν = 1/N ≥ 0`
(`ν = 0` is `N = ∞`). The distributional inequality `A'' ≥ 2K A' + 4ν A^Δ` on `(0, t)` is tested
against nonnegative smooth `ζ` with compact support in `(0, t)`; `lap s` is any version of
`Δ_E P_{t−s} f`, which is unique `m`-a.e. -/
def BE (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (P : ℝ → (X → ℝ) → X → ℝ) (K ν : ℝ) : Prop :=
  0 ≤ ν ∧
  ∀ f φ : X → ℝ, MemLp f 2 m → MemLp φ 2 m → MemLp φ ⊤ m → 0 ≤ᵐ[m] φ →
  ∀ t : ℝ, 0 < t → ∀ lap : ℝ → X → ℝ,
    (∀ s ∈ Set.Ioo 0 t, IsGenerator m E (P (t - s) f) (lap s)) →
  ∀ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ Set.Ioo 0 t → 0 ≤ ζ →
    -2 * K * ∫ s in (0 : ℝ)..t, At m P f φ t s * deriv ζ s
      + 4 * ν * ∫ s in (0 : ℝ)..t, ((1 / 2) * ∫ x, (lap s x) ^ 2 * P s φ x ∂m) * ζ s
      ≤ ∫ s in (0 : ℝ)..t, At m P f φ t s * deriv (deriv ζ) s

section Topological
variable [TopologicalSpace X]

/-- `L_C` (p. 31): continuous `ψ ∈ 𝔾` with `Γ(ψ) ≤ 1` m-a.e. -/
def IsLC (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (ψ : X → ℝ) : Prop :=
  Continuous ψ ∧ ∃ g, IsCarreDuChamp m E ψ g ∧ g ≤ᵐ[m] 1

/-- The intrinsic (extended) pseudo-distance `d_E` (p. 31; (1.9)). -/
noncomputable def intrinsicDist (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (x y : X) : ℝ≥0∞ :=
  ⨆ (ψ : X → ℝ) (_ : IsLC m E ψ), ENNReal.ofReal |ψ y - ψ x|

end Topological

section Metric
variable [MetricSpace X]

/-- Slope / local Lipschitz constant `|Df|(x)` (p. 22); `0` at isolated points. -/
noncomputable def slope (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  limsup (fun y => ENNReal.ofReal (|f y - f x| / dist y x)) (𝓝[≠] x)

/-- Asymptotic Lipschitz constant `|D*f|(x)` (p. 22). -/
noncomputable def slopeStar (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  limsup (fun p : X × X => ENNReal.ofReal (|f p.1 - f p.2| / dist p.1 p.2))
    (𝓝 (x, x) ⊓ 𝓟 {p | p.1 ≠ p.2})

/-- `Lip_b(X)`: bounded Lipschitz functions. -/
def IsLipB (f : X → ℝ) : Prop := (∃ K, LipschitzWith K f) ∧ ∃ C, ∀ x, |f x| ≤ C

/-- The Cheeger energy (p. 23; (1.6)). -/
noncomputable def cheeger (m : Measure X) (f : X → ℝ) : ℝ≥0∞ :=
  ⨅ (fs : ℕ → X → ℝ) (_ : (∀ n, IsLipB (fs n)) ∧ L2Tendsto m fs f),
    liminf (fun n => (1 / 2 : ℝ≥0∞) * ∫⁻ x, slope (fs n) x ^ 2 ∂m) atTop

/-- Length space (3.2), with the length of a continuous curve as its variation. -/
def IsLengthSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ x₀ x₁ : X, edist x₀ x₁ = ⨅ (γ : ℝ → X) (_ : ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x₀ ∧ γ 1 = x₁),
    eVariationOn γ (Set.Icc 0 1)

end Metric

section Wasserstein
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- `γ` is a coupling of `μ₁, μ₂` (3.12). -/
def IsCoupling (μ₁ μ₂ : Measure Y) (γ : Measure (Y × Y)) : Prop :=
  γ.map Prod.fst = μ₁ ∧ γ.map Prod.snd = μ₂

/-- `W₂²(μ₁, μ₂)` (3.12), an extended value. -/
noncomputable def W2sq (μ₁ μ₂ : Measure Y) : ℝ≥0∞ :=
  ⨅ (γ : Measure (Y × Y)) (_ : IsCoupling μ₁ μ₂ γ), ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ

/-- `P₂(Y)` (p. 24). -/
def InP2 (μ : Measure Y) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ y₀ : Y, ∫⁻ y, edist y y₀ ^ 2 ∂μ < ⊤

open Classical in
/-- `Ent_m(ρ) = ∫ f log f dm` for `ρ = f m`, `+∞` otherwise (p. 25), as `∫ (f log f)⁺ − ∫ (f log f)⁻`. -/
noncomputable def entropy (m ρ : Measure Y) : EReal :=
  if ρ ≪ m then
    ((∫⁻ y, ENNReal.ofReal ((ρ.rnDeriv m y).toReal * Real.log (ρ.rnDeriv m y).toReal) ∂m : ℝ≥0∞) : EReal)
      - ((∫⁻ y, ENNReal.ofReal (-((ρ.rnDeriv m y).toReal * Real.log (ρ.rnDeriv m y).toReal)) ∂m : ℝ≥0∞) : EReal)
  else ⊤

/-- Upper right Dini derivative `d⁺/dt` (Definition 3.1). -/
noncomputable def upperRightDeriv (g : ℝ → ℝ) (t : ℝ) : EReal :=
  limsup (fun h => (((g (t + h) - g t) / h : ℝ) : EReal)) (𝓝[>] 0)
end Wasserstein

section Structures
variable [MetricSpace X] [BorelSpace X]

/-- The truncation profile `S` of (3.27): `C¹`, `S = 1` on `[−1, 1]`, `S = 0` off `]−3, 3[`, `|S'| ≤ 1`. -/
def IsTruncProfile (S : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 S ∧ (∀ r, |r| ≤ 1 → S r = 1) ∧ (∀ r, 3 ≤ |r| → S r = 0) ∧ ∀ r, |deriv S r| ≤ 1

/-- `S_k(r) = k S(r/k)` (3.27). -/
noncomputable def Sk (S : ℝ → ℝ) (k r : ℝ) : ℝ := k * S (r / k)

/-- `ψ ∈ 𝕃` (p. 31): `ψ ∈ 𝔾` with `Γ(ψ) ≤ 1` m-a.e. -/
def IsL (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (ψ : X → ℝ) : Prop :=
  ∃ g, IsCarreDuChamp m E ψ g ∧ g ≤ᵐ[m] 1

/-- **Definition 3.6** (pp. 31–32), Energy measure space, with `τ` the topology of the metric of `X`
and that metric equal to `d_E` (condition (b)); `X` complete and separable is carried by the
binders `[CompleteSpace X] [SecondCountableTopology X]` of each statement. -/
structure IsEnergyMeasureSpace (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) : Prop where
  dirichlet : IsDirichletForm m E
  strongLocal : IsStronglyLocal m E
  fullSupport : m.IsOpenPosMeasure
  theta : ∃ θ : X → ℝ, Continuous θ ∧ (∀ x, 0 ≤ θ x) ∧ ∀ k : ℝ, 0 < k → IsL m E (fun x => Sk S k (θ x))
  dist_eq : ∀ x y : X, intrinsicDist m E x y = edist x y

/-- **Definition 3.13** (p. 38), upper regularity; "dense in `𝕍`" is density for the norm
`(‖f‖₂² + E(f))^{1/2}` of `𝕍`. -/
def IsUpperRegular (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) : Prop :=
  ∃ D : Set (X → ℝ), D ⊆ domain E ∧
    (∀ f ∈ domain E, ∀ ε : ℝ≥0∞, 0 < ε → ∃ h ∈ D, eLpNorm (f - h) 2 m < ε ∧ E (f - h) < ε) ∧
    ∀ f ∈ D, ∃ (fs gs : ℕ → X → ℝ),
      (∀ n, fs n ∈ carreDomain m E ∧ Continuous (fs n) ∧ ∃ C, ∀ x, |fs n x| ≤ C) ∧
      L2Tendsto m fs f ∧
      (∀ n, UpperSemicontinuous (gs n) ∧ ∃ C, ∀ x, |gs n x| ≤ C) ∧
      (∀ n, ∃ g, IsCarreDuChamp m E (fs n) g ∧ ∀ᵐ x ∂m, Real.sqrt (g x) ≤ gs n x) ∧
      limsup (fun n => ∫⁻ x, ENNReal.ofReal (gs n x ^ 2) ∂m) atTop ≤ E f

/-- **Definition 3.16** (p. 40), Riemannian Energy measure space. -/
def IsRiemannianEMS (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (S : ℝ → ℝ) : Prop :=
  IsEnergyMeasureSpace m E S ∧ IsUpperRegular m E ∧
    ∀ ψ : X → ℝ, IsL m E ψ → ∃ ψ' : X → ℝ, Continuous ψ' ∧ ψ' =ᵐ[m] ψ

/-- (MD.b), p. 21. -/
def MDb (m : Measure X) : Prop := ∀ (x : X) (r : ℝ), 0 < r → m (Metric.ball x r) < ⊤

/-- (MD.exp), p. 21. -/
def MDexp (m : Measure X) : Prop :=
  ∃ (x₀ : X) (M c : ℝ), 0 < M ∧ 0 ≤ c ∧
    ∀ r : ℝ, 0 ≤ r → m (Metric.ball x₀ r) ≤ ENNReal.ofReal (M * Real.exp (c * r ^ 2))

/-- **Definition 3.1** (p. 25), `RCD(K, ∞)`, for `(X, d, m)` with `X` complete and separable (binders):
(MD) (full support, (MD.b)), (MD.exp), the length property (3.2), and an `EVI_K` solution from
every `ρ ∈ P₂(X)`. (3.14) is read with `Ent_m(H_t ρ) < ∞`, so that its left side is a meaningful sum
(in `EReal`, `⊥ + ⊤ = ⊥` would otherwise satisfy it vacuously). -/
def IsRCDInfty (m : Measure X) (K : ℝ) : Prop :=
  m.IsOpenPosMeasure ∧ MDb m ∧ MDexp m ∧ IsLengthSpace X ∧
  ∀ ρ : Measure X, InP2 ρ → ∃ H : ℝ → Measure X,
    (∀ t, 0 < t → InP2 (H t)) ∧ Tendsto (fun t => W2sq (H t) ρ) (𝓝[>] 0) (𝓝 0) ∧
    ∀ t, 0 < t → ∀ ν : Measure X, InP2 ν → entropy m ν < ⊤ →
      entropy m (H t) < ⊤ ∧
      upperRightDeriv (fun s => (W2sq (H s) ν).toReal / 2) t
        + ((K / 2 * (W2sq (H t) ν).toReal : ℝ) : EReal) + entropy m (H t) ≤ entropy m ν

end Structures

end BERicci.Gamma


