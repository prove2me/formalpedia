-- Prove2me | Definitions.Def_BERicci_Gamma_Calculus
-- name    : BERicci_Gamma_Calculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:32.733394+00:00
-- url     : https://prove2.me/theorems/cbf07004-b2cf-49a5-8fde-30b657841e19
-- title:
--   §2.1–§2.2, pp. 13–19 — L¹ heat flow, Γ[f,g;φ] and its extension (2.20), Γ₂ (2.22), A^Δ_t, the conditions of Corollary 2.3 and of Lemma 2.2
-- statement:
--   This module collects the objects of §2.2 used to state Lemmas 2.1, 2.2 and Corollary 2.3. Throughout, $\mathcal E$ is a Dirichlet form on $L^2(X,m)$ with domain $\mathbb V$, generator $\Delta_{\mathcal E}$ and heat flow $(\mathsf P_t)$, and $\mathbb V_\infty=\mathbb V\cap L^\infty$.
--
--   1. **Heat flow on $L^1$** (p. 13). $\mathsf P^{(1)}_t$ is a linear $L^1$-contraction on $L^1(X,m)$ agreeing with $\mathsf P_t$ on $L^1\cap L^2$; by density of $L^1\cap L^2$ in $L^1$ it is the unique such extension. It gives meaning to $\mathsf P_t(f^2)$ and $\mathsf P_t\Gamma(f)$.
--   2. **The multilinear form** (p. 14). For $f,g,\varphi\in\mathbb V_\infty$,
--   $$\Gamma[f,g;\varphi]=\tfrac12\big(\mathcal E(f,g\varphi)+\mathcal E(g,f\varphi)-\mathcal E(fg,\varphi)\big).$$
--   By (2.20) it extends to $\mathbb V\times\mathbb V\times\mathbb V_\infty$: $\Gamma[f,g;\varphi]=c$ means that there are $f_n,g_n,\varphi_n\in\mathbb V_\infty$ converging in $\mathbb V$ to $f,g,\varphi$ with $\sup_n\|\varphi_n\|_\infty<\infty$, and that along every such sequence $\Gamma[f_n,g_n;\varphi_n]\to c$.
--   3. **$\Gamma_2$** (2.22). $\Gamma_2[f;\varphi]=\tfrac12\Gamma[f;\Delta_{\mathcal E}\varphi]-\Gamma[f,\Delta_{\mathcal E}f;\varphi]$, with $\Gamma[f;\psi]=\Gamma[f,f;\psi]$; $\Gamma_2[f;\varphi]=c$ means both terms are defined and combine to $c$.
--   4. $\mathsf A^\Delta_t[f;\varphi](s)=\tfrac12\int_X(\Delta_{\mathcal E}\mathsf P_{t-s}f)^2\,\mathsf P_s\varphi\,dm$ (2.24).
--   5. The conditions (i), (ii), (iv), (v), (vi) of **Corollary 2.3**, for $K\in\mathbb R$, $\nu\ge0$:
--      - (i) $\Gamma_2[f;\varphi]\ge K\Gamma[f;\varphi]+\nu\int_X(\Delta_{\mathcal E}f)^2\varphi\,dm$ for $(f,\varphi)\in D(\Gamma_2)$, $\varphi\ge0$, where $D(\Gamma_2)=\{(f,\varphi)\in D(\Delta_{\mathcal E})^2:\Delta_{\mathcal E}f\in\mathbb V,\ \varphi,\Delta_{\mathcal E}\varphi\in L^\infty\}$;
--      - (ii) $\mathsf C_t[f;\varphi](s)\ge K\mathsf B_t[f;\varphi](s)+2\nu\mathsf A^\Delta_t[f;\varphi](s)$ for $0\le s<t$, with $\mathsf B_t[f;\varphi](s)=\Gamma[\mathsf P_{t-s}f;\mathsf P_s\varphi]$, $\mathsf C_t[f;\varphi](s)=\Gamma_2[\mathsf P_{t-s}f;\mathsf P_s\varphi]$, for $f\in L^2$ and nonnegative $\varphi\in D(\Delta_{\mathcal E})\cap L^\infty$ with $\Delta_{\mathcal E}\varphi\in L^\infty$;
--      - (iv) $\mathsf P_tf\in\mathbb G$ and $I_{2K}(t)\Gamma(\mathsf P_tf)+2\nu I_{2K,2}(t)(\Delta_{\mathcal E}\mathsf P_tf)^2\le\tfrac12\mathsf P_t(f^2)-\tfrac12(\mathsf P_tf)^2$ a.e., for $f\in L^2$, $t>0$;
--      - (v) $\mathbb G=\mathbb V$ and, for $f\in\mathbb V$, $t>0$: $\tfrac12\mathsf P_t(f^2)-\tfrac12(\mathsf P_tf)^2+2\nu I_{-2K,2}(t)(\Delta_{\mathcal E}\mathsf P_tf)^2\le I_{-2K}(t)\,\mathsf P_t\Gamma(f)$ a.e. (coefficient on the right corrected, see the Formalization Note);
--      - (vi) $\mathbb G$ is dense in $L^2$ and, for $f\in\mathbb G$, $t>0$: $\mathsf P_tf\in\mathbb G$ and $\Gamma(\mathsf P_tf)+2\nu I_{-2K}(t)(\Delta_{\mathcal E}\mathsf P_tf)^2\le e^{-2Kt}\mathsf P_t\Gamma(f)$ a.e.
--   6. The four conditions of **Lemma 2.2** on $a\in C^1([0,t))$ with derivative $a'$ and $g\in C^0([0,t))$:
--      - (i) $a''\ge2Ka'+\nu g$ in $\mathscr D'(0,t)$, and pointwise on $[0,t)$ when $a\in C^2([0,t))$;
--      - (ii) $\frac{d}{ds}(e^{-2Ks}a'(s))\ge\nu e^{-2Ks}g(s)$ in $\mathscr D'(0,t)$;
--      - (iii) inequality (2.27) for $0\le s_1<s_2<t$ and nonnegative $\zeta\in C^2([s_1,s_2])$:
--   $$\int_{s_1}^{s_2}a(\zeta''+2K\zeta')\,ds+[a'\zeta]_{s_1}^{s_2}-[a(\zeta'+2K\zeta)]_{s_1}^{s_2}\ge\nu\int_{s_1}^{s_2}g\zeta\,ds;$$
--      - (iv) inequality (2.28) for $0\le s_1<s_2<t$: $e^{-2K(s_2-s_1)}a'(s_2)\ge a'(s_1)+\nu\int_{s_1}^{s_2}e^{-2K(s-s_1)}g(s)\,ds$.
--
--   These definitions turn every condition of Corollary 2.3 except (iii), which is the Setting's $BE$, into a predicate.
--
--   **Formalization Note** The paper defines $\Gamma$ only on $\mathbb V\times\mathbb V\times\mathbb V_\infty$, but (2.22) also writes $\Gamma[f;\Delta_{\mathcal E}\varphi]$, where $\Delta_{\mathcal E}\varphi$ is only assumed to be in $L^\infty$. The predicate form leaves $\Gamma_2[f;\varphi]$ undefined when no approximating sequence exists, and conditions (i)–(ii) quantify over the values of $\Gamma$ and $\Gamma_2$ that are defined. Distributional inequalities are tested against nonnegative smooth functions with compact support in $(0,t)$, integrated by parts. $\Gamma(\cdot)$ and $\Delta_{\mathcal E}$ are witnesses (`IsCarreDuChamp`, `IsGenerator`), which are unique a.e. Two changes are made to Lemma 2.2 as printed. In (iii) the test function is required to be nonnegative: the printed statement allows every $\zeta\in C^2$, and replacing $\zeta$ by $-\zeta$ reverses (2.27). In (iv), $s_2<t$ is added because $a'$ is only defined on $[0,t)$. In condition (v) of Corollary 2.3 the coefficient of $\mathsf P_t\Gamma(f)$ is $I_{-2K}(t)$, not the printed $I_{-2K,2}(t)$: as printed, (v) is false (see the goal's note), and the paper's derivation of (v) from (2.31) gives $I_{-2K}(t)$.
-- source:
--   arXiv:1209.5786v4, L¹ extension, p. 13; Γ[f,g;φ], p. 14; (2.20), (2.22), (2.24), p. 15; Lemma 2.2, (2.27)–(2.28), p. 17; Corollary 2.3 (i), (ii), (iv), (v), (vi), (2.32), (2.34), (2.35), pp. 18–19

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting

namespace BERicci.Gamma

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

variable {X : Type*} [MeasurableSpace X]

/-! ### The heat flow on `L¹` (p. 13) -/

/-- The extension of the heat flow `(P_t)` from `L¹ ∩ L²` to `L¹(X, m)` (p. 13): for `t ≥ 0`, `P1 t`
maps `L¹` to `L¹`, is linear, is an `L¹` contraction, and agrees `m`-a.e. with `P t` on `L¹ ∩ L²`.
Since `L¹ ∩ L²` is dense in `L¹`, these properties determine `P1 t g` up to `m`-a.e. equality. -/
structure IsL1Extension (m : Measure X) (P P1 : ℝ → (X → ℝ) → X → ℝ) : Prop where
  integrable : ∀ t : ℝ, 0 ≤ t → ∀ g : X → ℝ, Integrable g m → Integrable (P1 t g) m
  add : ∀ t : ℝ, 0 ≤ t → ∀ g h : X → ℝ, Integrable g m → Integrable h m →
    P1 t (g + h) =ᵐ[m] P1 t g + P1 t h
  smul : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℝ) (g : X → ℝ), Integrable g m →
    P1 t (c • g) =ᵐ[m] c • P1 t g
  contraction : ∀ t : ℝ, 0 ≤ t → ∀ g : X → ℝ, Integrable g m →
    eLpNorm (P1 t g) 1 m ≤ eLpNorm g 1 m
  agrees : ∀ t : ℝ, 0 ≤ t → ∀ g : X → ℝ, Integrable g m → MemLp g 2 m →
    P1 t g =ᵐ[m] P t g

/-! ### The multilinear form `Γ[f, g; φ]` (p. 14) and its extension (2.20) -/

/-- `fs n → f` strongly in `𝕍`, i.e. in `L²(X, m)` and in energy: `E(fs n − f) → 0`. -/
def VTendsto (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (fs : ℕ → X → ℝ) (f : X → ℝ) : Prop :=
  L2Tendsto m fs f ∧ Tendsto (fun n => E (fs n - f)) atTop (𝓝 0)

/-- `Γ[f, g; φ] = ½(E(f, gφ) + E(g, fφ) − E(fg, φ))` for `f, g, φ ∈ 𝕍∞` (p. 14). -/
noncomputable def gammaTri (E : (X → ℝ) → ℝ≥0∞) (f g φ : X → ℝ) : ℝ :=
  (bilin E f (g * φ) + bilin E g (f * φ) - bilin E (f * g) φ) / 2

/-- Approximating sequences for (2.20): `fs n, gs n, φs n ∈ 𝕍∞`, `fs n → f`, `gs n → g`, `φs n → φ`
strongly in `𝕍`, and `sup_n ‖φs n‖_∞ < ∞`. -/
def IsGammaApprox (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (f g φ : X → ℝ)
    (fs gs φs : ℕ → X → ℝ) : Prop :=
  (∀ n, fs n ∈ domainInf m E ∧ gs n ∈ domainInf m E ∧ φs n ∈ domainInf m E) ∧
    VTendsto m E fs f ∧ VTendsto m E gs g ∧ VTendsto m E φs φ ∧
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, eLpNorm (φs n) ⊤ m ≤ C

/-- `Γ[f, g; φ] = c` for the extension of `Γ` to `𝕍 × 𝕍 × 𝕍∞` by (2.20): approximating sequences
exist, and along every one of them `Γ[fs n, gs n; φs n] → c`. The predicate holds for at most one
`c`; it holds for some `c` exactly where the paper's extended `Γ` is defined. -/
def IsGammaVal (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (f g φ : X → ℝ) (c : ℝ) : Prop :=
  (∃ fs gs φs : ℕ → X → ℝ, IsGammaApprox m E f g φ fs gs φs) ∧
    ∀ fs gs φs : ℕ → X → ℝ, IsGammaApprox m E f g φ fs gs φs →
      Tendsto (fun n => gammaTri E (fs n) (gs n) (φs n)) atTop (𝓝 c)

/-- `Γ₂[f; φ] = c` (2.22): `Γ₂[f; φ] = ½ Γ[f; Δ_E φ] − Γ[f, Δ_E f; φ]`, with `Δ_E f`, `Δ_E φ` versions
of the generator (unique `m`-a.e.) and both `Γ` terms defined in the sense of `IsGammaVal`. -/
def IsGamma2Val (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (f φ : X → ℝ) (c : ℝ) : Prop :=
  ∃ (lf lφ : X → ℝ) (c₁ c₂ : ℝ), IsGenerator m E f lf ∧ IsGenerator m E φ lφ ∧
    IsGammaVal m E f f lφ c₁ ∧ IsGammaVal m E f lf φ c₂ ∧ c = c₁ / 2 - c₂

/-- `A^Δ_t[f; φ](s) = ½ ∫ (Δ_E P_{t−s} f)² P_s φ dm` (2.24), with `lap` a version of `Δ_E P_{t−s} f`. -/
noncomputable def AtLap (m : Measure X) (P : ℝ → (X → ℝ) → X → ℝ) (lap φ : X → ℝ) (s : ℝ) : ℝ :=
  (1 / 2) * ∫ x, (lap x) ^ 2 * P s φ x ∂m

/-! ### The six conditions of Corollary 2.3 (pp. 18–19); (iii) is the Setting's `BE` -/

/-- Corollary 2.3 (i): `Γ₂[f; φ] ≥ K Γ[f; φ] + ν ∫ (Δ_E f)² φ dm` for every `(f, φ) ∈ D(Γ₂)` with
`φ ≥ 0`, where `D(Γ₂) = {(f, φ) ∈ D(Δ_E) × D(Δ_E) : Δ_E f ∈ 𝕍, φ, Δ_E φ ∈ L∞}`. -/
def BECond1 (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (K ν : ℝ) : Prop :=
  ∀ f lf φ lφ : X → ℝ, IsGenerator m E f lf → E lf < ⊤ →
    IsGenerator m E φ lφ → MemLp φ ⊤ m → MemLp lφ ⊤ m → 0 ≤ᵐ[m] φ →
    ∀ c₂ c : ℝ, IsGamma2Val m E f φ c₂ → IsGammaVal m E f f φ c →
      K * c + ν * ∫ x, (lf x) ^ 2 * φ x ∂m ≤ c₂

/-- Corollary 2.3 (ii), (2.32): `C_t[f; φ](s) ≥ K B_t[f; φ](s) + 2ν A^Δ_t[f; φ](s)` for every
`f ∈ L²`, every nonnegative `φ ∈ D(Δ_E) ∩ L∞` with `Δ_E φ ∈ L∞`, and every `0 ≤ s < t`; here
`C_t[f; φ](s) = Γ₂[P_{t−s} f; P_s φ]` and `B_t[f; φ](s) = Γ[P_{t−s} f; P_s φ]`. -/
def BECond2 (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (P : ℝ → (X → ℝ) → X → ℝ) (K ν : ℝ) : Prop :=
  ∀ f : X → ℝ, MemLp f 2 m → ∀ φ lφ : X → ℝ,
    IsGenerator m E φ lφ → MemLp φ ⊤ m → MemLp lφ ⊤ m → 0 ≤ᵐ[m] φ →
    ∀ t : ℝ, 0 < t → ∀ s ∈ Set.Ico 0 t, ∀ lap : X → ℝ, IsGenerator m E (P (t - s) f) lap →
    ∀ c₂ c : ℝ, IsGamma2Val m E (P (t - s) f) (P s φ) c₂ →
      IsGammaVal m E (P (t - s) f) (P (t - s) f) (P s φ) c →
      K * c + 2 * ν * AtLap m P lap φ s ≤ c₂

/-- Corollary 2.3 (iv), (2.34): for every `f ∈ L²` and `t > 0`, `P_t f ∈ 𝔾` and
`I_{2K}(t) Γ(P_t f) + 2ν I_{2K,2}(t) (Δ_E P_t f)² ≤ ½ P_t(f²) − ½ (P_t f)²` `m`-a.e.;
`P_t(f²)` is the `L¹` heat flow `P1`. -/
def BECond4 (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (P P1 : ℝ → (X → ℝ) → X → ℝ) (K ν : ℝ) :
    Prop :=
  ∀ f : X → ℝ, MemLp f 2 m → ∀ t : ℝ, 0 < t →
    ∃ g lap : X → ℝ, IsCarreDuChamp m E (P t f) g ∧ IsGenerator m E (P t f) lap ∧
      ∀ᵐ x ∂m, IK (2 * K) t * g x + 2 * ν * IK2 (2 * K) t * (lap x) ^ 2 ≤
        (1 / 2) * P1 t (f * f) x - (1 / 2) * (P t f x) ^ 2

/-- Corollary 2.3 (v), with the coefficient of `P_t Γ(f)` corrected from the printed `I_{−2K,2}(t)` to
`I_{−2K}(t)` (the value the proof's route through (2.31) gives; the printed form fails for the heat flow
on `ℝ` with `K = ν = 0` and small `t`): `𝔾 = 𝕍`, and for every `f ∈ 𝕍` and `t > 0`,
`½ P_t(f²) − ½ (P_t f)² + 2ν I_{−2K,2}(t) (Δ_E P_t f)² ≤ I_{−2K}(t) P_t Γ(f)` `m`-a.e. (at `t = 0` both
sides vanish); `P_t(f²)` and `P_t Γ(f)` are the `L¹` heat flow `P1`. -/
def BECond5 (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (P P1 : ℝ → (X → ℝ) → X → ℝ) (K ν : ℝ) :
    Prop :=
  carreDomain m E = domain E ∧
  ∀ f g : X → ℝ, IsCarreDuChamp m E f g → ∀ t : ℝ, 0 < t →
    ∃ lap : X → ℝ, IsGenerator m E (P t f) lap ∧
      ∀ᵐ x ∂m, (1 / 2) * P1 t (f * f) x - (1 / 2) * (P t f x) ^ 2
          + 2 * ν * IK2 (-2 * K) t * (lap x) ^ 2 ≤ IK (-2 * K) t * P1 t g x

/-- Corollary 2.3 (vi), (2.35): `𝔾` is dense in `L²`, and for every `f ∈ 𝔾` and `t > 0`, `P_t f ∈ 𝔾`
with `Γ(P_t f) + 2ν I_{−2K}(t) (Δ_E P_t f)² ≤ e^{−2Kt} P_t Γ(f)` `m`-a.e.; `P_t Γ(f)` is the `L¹`
heat flow `P1` of the density `Γ(f)`. -/
def BECond6 (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (P P1 : ℝ → (X → ℝ) → X → ℝ) (K ν : ℝ) :
    Prop :=
  (∀ f : X → ℝ, MemLp f 2 m → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ h ∈ carreDomain m E, eLpNorm (f - h) 2 m < ε) ∧
  ∀ f g : X → ℝ, IsCarreDuChamp m E f g → ∀ t : ℝ, 0 < t →
    ∃ g' lap : X → ℝ, IsCarreDuChamp m E (P t f) g' ∧ IsGenerator m E (P t f) lap ∧
      ∀ᵐ x ∂m, g' x + 2 * ν * IK (-2 * K) t * (lap x) ^ 2 ≤
        Real.exp (-2 * K * t) * P1 t g x

/-! ### Lemma 2.2 (p. 17): conditions on real functions `a ∈ C¹([0,t))`, `g ∈ C⁰([0,t))` -/

/-- `a ∈ C¹([0, t))` with derivative `ap` (one-sided at `0`). -/
def IsC1Ico (t : ℝ) (a ap : ℝ → ℝ) : Prop :=
  ContinuousOn a (Set.Ico 0 t) ∧ ContinuousOn ap (Set.Ico 0 t) ∧
    ∀ s ∈ Set.Ico 0 t, HasDerivWithinAt a (ap s) (Set.Ico 0 t) s

/-- `ζ ∈ C²([s₁, s₂])` with first and second derivatives `ζ1`, `ζ2` (one-sided at the ends). -/
def IsC2Icc (s₁ s₂ : ℝ) (ζ ζ1 ζ2 : ℝ → ℝ) : Prop :=
  ContinuousOn ζ2 (Set.Icc s₁ s₂) ∧
    (∀ s ∈ Set.Icc s₁ s₂, HasDerivWithinAt ζ (ζ1 s) (Set.Icc s₁ s₂) s) ∧
    ∀ s ∈ Set.Icc s₁ s₂, HasDerivWithinAt ζ1 (ζ2 s) (Set.Icc s₁ s₂) s

/-- Lemma 2.2 (i): `a'' ≥ 2K a' + ν g` in `D'(0, t)` (tested against nonnegative smooth `ζ` with
compact support in `(0, t)`), and pointwise in `[0, t)` whenever `a ∈ C²([0, t))`. -/
def L22Cond1 (K ν t : ℝ) (a ap g : ℝ → ℝ) : Prop :=
  (∀ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ Set.Ioo 0 t → 0 ≤ ζ →
    ν * ∫ s in (0 : ℝ)..t, g s * ζ s ≤
      ∫ s in (0 : ℝ)..t, a s * (deriv (deriv ζ) s + 2 * K * deriv ζ s)) ∧
  ∀ app : ℝ → ℝ, IsC1Ico t ap app → ∀ s ∈ Set.Ico 0 t, 2 * K * ap s + ν * g s ≤ app s

/-- Lemma 2.2 (ii): `d/ds (e^{−2Ks} a'(s)) ≥ ν e^{−2Ks} g(s)` in `D'(0, t)`. -/
def L22Cond2 (K ν t : ℝ) (ap g : ℝ → ℝ) : Prop :=
  ∀ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ Set.Ioo 0 t → 0 ≤ ζ →
    ν * ∫ s in (0 : ℝ)..t, Real.exp (-2 * K * s) * g s * ζ s ≤
      - ∫ s in (0 : ℝ)..t, Real.exp (-2 * K * s) * ap s * deriv ζ s

/-- Lemma 2.2 (iii), (2.27), for every `0 ≤ s₁ < s₂ < t` and every **nonnegative**
`ζ ∈ C²([s₁, s₂])` (the sign condition is necessary: replacing `ζ` by `−ζ` reverses (2.27)). -/
def L22Cond3 (K ν t : ℝ) (a ap g : ℝ → ℝ) : Prop :=
  ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ < s₂ → s₂ < t →
  ∀ ζ ζ1 ζ2 : ℝ → ℝ, IsC2Icc s₁ s₂ ζ ζ1 ζ2 → (∀ s ∈ Set.Icc s₁ s₂, 0 ≤ ζ s) →
    ν * ∫ s in s₁..s₂, g s * ζ s ≤
      (∫ s in s₁..s₂, a s * (ζ2 s + 2 * K * ζ1 s)) + (ap s₂ * ζ s₂ - ap s₁ * ζ s₁)
        - (a s₂ * (ζ1 s₂ + 2 * K * ζ s₂) - a s₁ * (ζ1 s₁ + 2 * K * ζ s₁))

/-- Lemma 2.2 (iv), (2.28), for every `0 ≤ s₁ < s₂ < t`. -/
def L22Cond4 (K ν t : ℝ) (ap g : ℝ → ℝ) : Prop :=
  ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ < s₂ → s₂ < t →
    ap s₁ + ν * ∫ s in s₁..s₂, Real.exp (-2 * K * (s - s₁)) * g s
      ≤ Real.exp (-2 * K * (s₂ - s₁)) * ap s₂

end BERicci.Gamma


