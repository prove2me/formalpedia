-- Prove2me | Definitions.Def_ManyServerFluid_Uniqueness_Model
-- name    : ManyServerFluid_Uniqueness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:20.90798+00:00
-- url     : https://prove2.me/theorems/1a031be6-41e7-4366-8d12-b93964ff7c84
-- title:
--   The fluid model of §2.1 and §3.1: service law with density g and mean 1, M, hazard rate h, S_0, test functions C_c^{1,1}, the fluid equations (3.4)–(3.8), Assumption 2, ν̄*
-- statement:
--   This file sets up the fluid model of a many-server queue of Kaspi and Ramanan (§1.2, §2.1, §3.1).
--
--   **Service law.** Service requirements have a distribution function $G$ with a density $g$: $g \ge 0$, $g = 0$ on $(-\infty, 0)$, $\int g = 1$, and $G(x) = \int_{(-\infty, x]} g$. The mean service requirement is normalized to one,
--   $$\int_{[0,\infty)} x\, g(x)\, dx = 1 \qquad (2.2).$$
--   The right end of the support is $M = \sup\{x \ge 0 : G(x) < 1\} \in [0, \infty]$ (2.4), the age space is $[0, M)$, and the **hazard rate** is $h(x) = g(x)/(1 - G(x))$ on $[0, M)$ (2.3). The measure $\bar\nu^*$ has density $1 - G$ on $[0, \infty)$ (3.13).
--
--   **Data and paths.** $\mathcal M_{\le 1}[0, M)$ is the set of finite nonnegative measures carried by $[0, M)$ of total mass at most one. A path on $[0,\infty)$ is **càdlàg** if it is right-continuous at every $t \ge 0$ and has a left limit at every $t > 0$; for measure-valued paths the topology is weak convergence. $\mathcal I_0[0,\infty)$ is the set of nondecreasing càdlàg $f$ with $f(0) = 0$, and
--   $$\mathcal S_0 = \{(f, x, \mu) \in \mathcal I_0[0,\infty) \times \mathbb R_+ \times \mathcal M_{\le1}[0,M) : 1 - \langle \mathbf 1, \mu\rangle = [1 - x]^+\} \qquad (3.3).$$
--
--   **Test functions.** $\mathcal C_c^{1,1}([0,M) \times \mathbb R_+)$ is the set of functions $\varphi$ continuous on $[0,M) \times [0,\infty)$, vanishing there outside some $[0,m] \times [0,T]$ with $m < M$, whose directional derivative $\varphi_x + \varphi_s = \lim_{\varepsilon \downarrow 0} [\varphi(x+\varepsilon, s+\varepsilon) - \varphi(x,s)]/\varepsilon$ exists at every point and is again such a function.
--
--   **Fluid equations (Definition 3.3).** A càdlàg pair $(\bar X, \bar\nu)$ with $\bar X(t) \ge 0$ and $\bar\nu_t \in \mathcal M_{\le1}[0,M)$ solves the fluid equations associated with $(\bar E, \bar X(0), \bar\nu_0) \in \mathcal S_0$ if $\bar\nu$ starts at $\bar\nu_0$, $\bar X$ at $\bar X(0)$, and for every $t \ge 0$: $\int_0^t \langle h, \bar\nu_s\rangle\, ds < \infty$ (3.4); for every $\varphi \in \mathcal C_c^{1,1}$
--   $$\langle\varphi(\cdot,t),\bar\nu_t\rangle = \langle\varphi(\cdot,0),\bar\nu_0\rangle + \int_0^t\langle\varphi_x(\cdot,s)+\varphi_s(\cdot,s),\bar\nu_s\rangle ds - \int_0^t\langle h\varphi(\cdot,s),\bar\nu_s\rangle ds + \int_{[0,t]}\varphi(0,s)\,d\bar K(s) \quad (3.5);$$
--   $\bar X(t) = \bar X(0) + \bar E(t) - \bar D(t)$ (3.6); and $1 - \langle\mathbf 1,\bar\nu_t\rangle = [1 - \bar X(t)]^+$ (3.7), where $\bar D(t) = \int_0^t\langle h,\bar\nu_s\rangle ds$ (3.9) and $\bar K(t) = \langle\mathbf 1,\bar\nu_t\rangle - \langle\mathbf 1,\bar\nu_0\rangle + \bar D(t)$ (3.8).
--
--   **Assumption 2** (p. 46): there is $m_0 < M$ such that $h$ is bounded or lower semicontinuous on $(m_0, M)$.
--
--   These objects are shared by every statement of the mission; $\bar X$ is the fluid number in system, $\bar\nu_t$ the fluid age distribution of customers in service, $\bar K$ the cumulative entry into service and $\bar D$ the cumulative departures.
--
--   **Formalization Note.** Time is $\mathbb R$, read on $[0,\infty)$: every condition is stated for $t \ge 0$. Measures are `FiniteMeasure ℝ` carried by $[0,M)$, whose topology is weak convergence. $M$ lives in $[0,\infty]$ (`ℝ≥0∞`). Off $[0,M)$ the formula for $h$ returns $0$ (Lean's division by zero); measures are carried by $[0,M)$, so these values are never read. Compact support of test functions is relative to $[0,M) \times \mathbb R_+$, so $\varphi(0,s)$ need not vanish; the directional derivative is passed as a second function `Dφ` that the predicate `IsTestFn` ties to $\varphi$. The integral in (3.4) is a lower integral in $[0,\infty]$ and $\bar D$, $\bar K$ are its real value. $d\bar K$ is the Lebesgue–Stieltjes measure of $t \mapsto \bar K(\max(t,0))$, defined as $0$ when that function is not monotone and right-continuous; for a fluid solution $\bar K$ is nondecreasing and right-continuous, so the measure is the genuine one. The paper writes $\bar\nu_0$ for both the datum and the value at time 0; here $\bar\nu(0) = \bar\nu_0$ and $\bar X(0)$ equal to the datum are explicit clauses. The paper states that $G$ has a density; we state also that $g$ vanishes below $0$ and integrates to one, i.e. that $G$ is the distribution function of a nonnegative service requirement. The weak topology of `FiniteMeasure ℝ` is tested against bounded continuous functions on $\mathbb R$, while the paper's $\mathcal M_F[0,M)$ is tested against $\mathcal C_b[0,M)$. For measures carried by $[0,M)$ converging to a limit carried by $[0,M)$ the two notions agree, so right-continuity is the paper's; the left-limit clause asks only for a limit among finite measures on $\mathbb R$, which could in principle charge the point $M$. This can only enlarge the class of fluid solutions, and every fluid solution has its left limits in $\mathcal M_F[0,M)$ by the representation (3.11).
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), pp. 36–46, §1.2, §2.1 ((2.2)–(2.4)), §3.1 ((3.3), Definition 3.3, (3.8)–(3.9)), Assumption 2, Remark 3.8 (3.13)

import Mathlib

namespace ManyServerFluid.Uniqueness

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The service law (§2.1, p. 39): G has a density g; service requirements are nonnegative
(g = 0 on (−∞, 0)); the mean service requirement is 1 (2.2). -/
structure ServiceLaw where
  g : ℝ → ℝ
  measurable_g : Measurable g
  g_nonneg : ∀ x, 0 ≤ g x
  g_eq_zero_of_neg : ∀ x, x < 0 → g x = 0
  integrable_g : Integrable g
  integral_g : ∫ x, g x = 1
  integrable_mean : Integrable (fun x => x * g x)
  mean_one : ∫ x, x * g x = 1          -- (2.2)

namespace ServiceLaw
variable (S : ServiceLaw)

/-- G(x) = ∫_{(−∞, x]} g. -/
noncomputable def G (x : ℝ) : ℝ := ∫ y in Iic x, S.g y

/-- (2.4) M = sup{x ∈ [0, ∞) : G(x) < 1} ∈ [0, ∞]. -/
noncomputable def M : ℝ≥0∞ := ⨆ (x : ℝ) (_ : 0 ≤ x ∧ S.G x < 1), ENNReal.ofReal x

/-- The age space [0, M) ⊆ ℝ. -/
def Ages : Set ℝ := {x | 0 ≤ x ∧ ENNReal.ofReal x < S.M}

/-- (2.3) h = g / (1 − G). Off [0, M) the value is 0 (g = 0 below 0; 1 − G = 0 from M on, and
Lean's division by 0 is 0); measures below are carried by [0, M), so those values are never read. -/
noncomputable def h (x : ℝ) : ℝ := S.g x / (1 - S.G x)

/-- ν̄* (3.13): density 1 − G on [0, M) (and 1 − G = 0 beyond M). -/
noncomputable def nuStar : Measure ℝ :=
  (volume.restrict (Ici 0)).withDensity fun x => ENNReal.ofReal (1 - S.G x)

/-- M_{≤1}[0, M): a finite measure carried by [0, M) with total mass ≤ 1. -/
def IsSubProb (μ : FiniteMeasure ℝ) : Prop :=
  (μ : Measure ℝ) S.Agesᶜ = 0 ∧ μ.mass ≤ 1

/-- Càdlàg on [0, ∞): right-continuous at every t ≥ 0, a left limit at every t > 0. For
`α = FiniteMeasure ℝ` the topology is weak convergence, so this is D_{M_F[0,M)}[0, ∞). -/
def IsCadlag {α : Type*} [TopologicalSpace α] (p : ℝ → α) : Prop :=
  (∀ t, 0 ≤ t → ContinuousWithinAt p (Ici t) t) ∧
  (∀ t, 0 < t → ∃ a, Tendsto p (𝓝[<] t) (𝓝 a))

/-- I_0[0, ∞): nondecreasing càdlàg with f(0) = 0. -/
def IsI0 (f : ℝ → ℝ) : Prop := MonotoneOn f (Ici 0) ∧ f 0 = 0 ∧ IsCadlag f

/-- (3.3) (f, x, μ) ∈ S_0. -/
def InS0 (E : ℝ → ℝ) (x : ℝ) (μ : FiniteMeasure ℝ) : Prop :=
  IsI0 E ∧ 0 ≤ x ∧ S.IsSubProb μ ∧ 1 - (μ.mass : ℝ) = max (1 - x) 0

/-- C_c^{1,1}([0, M) × R₊) (p. 36), with `Dφ` its directional derivative φ_x + φ_s: φ and Dφ are
continuous on [0, M) × [0, ∞) and vanish there outside some [0, m] × [0, T] with m < M (compact
support *relative to* [0, M) × R₊), and the one-sided limit defining φ_x + φ_s exists and equals Dφ
at every point of [0, M) × [0, ∞). -/
def IsTestFn (φ Dφ : ℝ × ℝ → ℝ) : Prop :=
  ContinuousOn φ (S.Ages ×ˢ Ici 0) ∧ ContinuousOn Dφ (S.Ages ×ˢ Ici 0) ∧
  (∃ m T : ℝ, ENNReal.ofReal m < S.M ∧ ∀ p ∈ S.Ages ×ˢ Ici (0 : ℝ),
      (m < p.1 ∨ T < p.2) → φ p = 0 ∧ Dφ p = 0) ∧
  ∀ p ∈ S.Ages ×ˢ Ici (0 : ℝ),
    Tendsto (fun ε => (φ (p.1 + ε, p.2 + ε) - φ p) / ε) (𝓝[>] 0) (𝓝 (Dφ p))

/-- ∫_0^t ⟨h, ν̄_s⟩ ds as an extended number; (3.4) says it is finite. -/
noncomputable def hInt (ν : ℝ → FiniteMeasure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Icc 0 t, ∫⁻ x, ENNReal.ofReal (S.h x) ∂(ν s : Measure ℝ)

/-- (3.9) D̄(t) = ∫_0^t ⟨h, ν̄_s⟩ ds (real; finite under (3.4)). -/
noncomputable def Dbar (ν : ℝ → FiniteMeasure ℝ) (t : ℝ) : ℝ := (S.hInt ν t).toReal

/-- (3.8) K̄(t) = ⟨1, ν̄_t⟩ − ⟨1, ν̄_0⟩ + D̄(t). -/
noncomputable def Kbar (ν : ℝ → FiniteMeasure ℝ) (t : ℝ) : ℝ :=
  ((ν t).mass : ℝ) - ((ν 0).mass : ℝ) + S.Dbar ν t

end ServiceLaw

/-- dF for a path F on [0, ∞): the Lebesgue–Stieltjes measure of t ↦ F(max t 0) when that is
monotone and right-continuous, 0 otherwise. `∫ s in Icc 0 t, φ s ∂(stieltjes F)` is ∫_[0,t] φ dF;
there is no atom at 0 when F(0) = 0. The `else` branch is never reached by K̄ of a fluid solution
(K̄ is nondecreasing: proof of Corollary 4.4, p. 52). -/
noncomputable def stieltjes (F : ℝ → ℝ) : Measure ℝ := by
  classical
  exact if hF : Monotone (fun t => F (max t 0)) ∧
      ∀ t, ContinuousWithinAt (fun t => F (max t 0)) (Ici t) t
    then (StieltjesFunction.mk (fun t => F (max t 0)) hF.1 hF.2).measure else 0

namespace ServiceLaw
variable (S : ServiceLaw)

/-- Definition 3.3 (pp. 43–44): (X̄, ν̄) solves the fluid equations associated with
(Ē, X̄(0), ν̄_0). -/
structure IsFluidSolution (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ)
    (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ) : Prop where
  cadlag_X : IsCadlag X
  cadlag_ν : IsCadlag ν
  X_nonneg : ∀ t, 0 ≤ t → 0 ≤ X t
  subProb : ∀ t, 0 ≤ t → S.IsSubProb (ν t)
  X_zero : X 0 = X0
  ν_zero : ν 0 = ν0
  hInt_lt_top : ∀ t, 0 ≤ t → S.hInt ν t < ⊤                                   -- (3.4)
  age : ∀ φ Dφ, S.IsTestFn φ Dφ → ∀ t, 0 ≤ t →                                 -- (3.5)
    ∫ x, φ (x, t) ∂(ν t : Measure ℝ) =
      ∫ x, φ (x, 0) ∂(ν0 : Measure ℝ)
      + ∫ s in Icc 0 t, ∫ x, Dφ (x, s) ∂(ν s : Measure ℝ)
      - ∫ s in Icc 0 t, ∫ x, S.h x * φ (x, s) ∂(ν s : Measure ℝ)
      + ∫ s in Icc 0 t, φ (0, s) ∂(stieltjes (S.Kbar ν))
  balance : ∀ t, 0 ≤ t → X t = X0 + E t - S.Dbar ν t                           -- (3.6)
  nonidling : ∀ t, 0 ≤ t → 1 - ((ν t).mass : ℝ) = max (1 - X t) 0               -- (3.7)

/-- Assumption 2 (p. 46). -/
def Assumption2 : Prop :=
  ∃ m0 : ℝ, 0 ≤ m0 ∧ ENNReal.ofReal m0 < S.M ∧
    (BddAbove (S.h '' {x | m0 < x ∧ ENNReal.ofReal x < S.M}) ∨
     LowerSemicontinuousOn S.h {x | m0 < x ∧ ENNReal.ofReal x < S.M})

end ServiceLaw
end ManyServerFluid.Uniqueness


