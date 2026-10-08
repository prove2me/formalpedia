-- Prove2me | Definitions.Def_ManyServerFluid_Equilibrium_Model
-- name    : ManyServerFluid_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:26.208777+00:00
-- url     : https://prove2.me/theorems/d9683288-7d92-41ba-bfc7-2f62d322b064
-- title:
--   The fluid model of §2.1 and §3.1: service law G with density g and mean 1, M, hazard rate h, S_0, test functions C_c^{1,1}, the fluid equations (3.4)–(3.8), Assumption 2, ν̄*
-- statement:
--   This file fixes the fluid model of a many-server queue in which $N\to\infty$ servers each serve one customer at a time, customers are served in order of arrival, and service requirements are i.i.d. with distribution $G$.
--
--   1. **Service law.** $G$ is the distribution function of a nonnegative service requirement with a density $g$: $g\ge0$, $g=0$ on $(-\infty,0)$, $\int g=1$, and $G(x)=\int_{(-\infty,x]}g$. The mean service requirement is normalized to one,
--   $$\int_{[0,\infty)}x\,g(x)\,dx=\int_{[0,\infty)}(1-G(x))\,dx=1 .\qquad(2.2)$$
--   2. **Support and hazard rate.** $M=\sup\{x\in[0,\infty):G(x)<1\}\in[0,\infty]$ (2.4), the age space is $[0,M)$, and the hazard rate is $h(x)=g(x)/(1-G(x))$ for $x\in[0,M)$ (2.3).
--   3. **Equilibrium measure.** $\bar\nu_*$ is the measure on $[0,M)$ with density $1-G$ (3.13): $\bar\nu_*(A)=\int_A(1-G(x))\,dx$. By (2.2) it is a probability measure.
--   4. **Measures and paths.** $\mathcal M_{\le1}[0,M)$ is the set of finite nonnegative measures carried by $[0,M)$ with total mass at most $1$. A path on $[0,\infty)$ is càdlàg if it is right-continuous at every $t\ge0$ and has a left limit at every $t>0$; for measure-valued paths the topology is weak convergence. $\mathcal I_0[0,\infty)$ is the set of nondecreasing càdlàg real functions $f$ with $f(0)=0$.
--   5. **Initial conditions.** $\mathcal S_0$ is the set of triples $(\bar E,x,\mu)\in\mathcal I_0[0,\infty)\times\mathbb R_+\times\mathcal M_{\le1}[0,M)$ with $1-\langle\mathbf 1,\mu\rangle=[1-x]^+$ (3.3).
--   6. **Test functions.** $\mathcal C_c^{1,1}([0,M)\times\mathbb R_+)$: functions $\varphi$ continuous on $[0,M)\times[0,\infty)$, vanishing there outside $[0,m]\times[0,T]$ for some $m<M$ and $T<\infty$, whose directional derivative $\varphi_x+\varphi_s=\lim_{\varepsilon\downarrow0}[\varphi(x+\varepsilon,s+\varepsilon)-\varphi(x,s)]/\varepsilon$ exists everywhere on $[0,M)\times[0,\infty)$ and is continuous with the same kind of support.
--   7. **Fluid equations (Definition 3.3).** A càdlàg pair $(\bar X,\bar\nu)$ with $\bar X\ge0$ and $\bar\nu_t\in\mathcal M_{\le1}[0,M)$ solves the fluid equations associated with $(\bar E,\bar X(0),\bar\nu_0)\in\mathcal S_0$ if, for every $t\ge0$, $\bar D(t)=\int_0^t\langle h,\bar\nu_s\rangle\,ds<\infty$ (3.4), and, with $\bar K(t)=\langle\mathbf 1,\bar\nu_t\rangle-\langle\mathbf 1,\bar\nu_0\rangle+\bar D(t)$ (3.8),
--   $$\langle\varphi(\cdot,t),\bar\nu_t\rangle=\langle\varphi(\cdot,0),\bar\nu_0\rangle+\int_0^t\langle\varphi_x(\cdot,s)+\varphi_s(\cdot,s),\bar\nu_s\rangle ds-\int_0^t\langle h\varphi(\cdot,s),\bar\nu_s\rangle ds+\int_{[0,t]}\varphi(0,s)\,d\bar K(s)\quad(3.5)$$
--   for every test function $\varphi$, together with the mass balance $\bar X(t)=\bar X(0)+\bar E(t)-\bar D(t)$ (3.6) and the non-idling condition $1-\langle\mathbf 1,\bar\nu_t\rangle=[1-\bar X(t)]^+$ (3.7).
--   8. **Assumption 2.** There is $m_0<M$ such that $h$ is bounded, or lower semicontinuous, on $(m_0,M)$.
--
--   $\bar X(t)$ is the scaled number of customers in system, $\bar\nu_t$ the scaled age measure of the customers in service, $\bar E$ the cumulative arrivals, $\bar K$ the cumulative entries into service and $\bar D$ the cumulative departures. Every statement of the mission is about solutions of these equations.
--
--   **Formalization Note** Time is $\mathbb R$, read on $[0,\infty)$: every condition is stated for $t\ge0$ and values at negative times are never used. Measures are Mathlib `FiniteMeasure ℝ` carried by $[0,M)$; its topology is weak convergence against bounded continuous functions, the paper's topology on $\mathcal M_F[0,M)$. The paper takes "$\bar\nu_0$" to be $\bar\nu(0)$; the structure states $\bar\nu(0)=\bar\nu_0$ and $\bar X(0)=X_0$ explicitly. Compact support of a test function is relative to $[0,M)\times\mathbb R_+$, as the paper intends (otherwise the entry term $\varphi(0,s)$ would vanish identically). The directional derivative $\varphi_x+\varphi_s$ is supplied as a second function `Dφ`, determined by $\varphi$ on $[0,M)\times[0,\infty)$. $\int_0^t\langle h,\bar\nu_s\rangle ds$ is a lower Lebesgue integral in $[0,\infty]$ (so (3.4) is meaningful even when $h$ is unbounded), and $\bar D$, $\bar K$ are its real values. $d\bar K$ is the Lebesgue–Stieltjes measure of $t\mapsto\bar K(\max(t,0))$, defined to be $0$ if that function is not nondecreasing and right-continuous; for a fluid solution $\bar K$ is nondecreasing (proof of Corollary 4.4, p. 52), so that branch is a totality device only. $h=g/(1-G)$ is evaluated off $[0,M)$ with Lean's convention $a/0=0$; measures are carried by $[0,M)$, so those values are never read. Assumption 2 takes $m_0\ge0$, which loses nothing ($h$ bounded or lower semicontinuous on $(m_0,M)$ is inherited by $(\max(m_0,0),M)$).
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), pp. 36–46, §1.2, §2.1 (2.2)–(2.4), §3.1 (3.3), Definition 3.3 (3.4)–(3.9), Assumption 2, Remark 3.8 (3.13)

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model

namespace ManyServerFluid.Equilibrium

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
  mean_one : ∫ x, x * g x = 1

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

end ServiceLaw

/-- Càdlàg on [0, ∞): right-continuous at every t ≥ 0, a left limit at every t > 0. For
`α = FiniteMeasure ℝ` the topology is weak convergence, so this is D_{M_F[0,M)}[0, ∞). -/
def IsCadlag {α : Type*} [TopologicalSpace α] (p : ℝ → α) : Prop :=
  (∀ t, 0 ≤ t → ContinuousWithinAt p (Ici t) t) ∧
  (∀ t, 0 < t → ∃ a, Tendsto p (𝓝[<] t) (𝓝 a))

/-- I_0[0, ∞): nondecreasing càdlàg with f(0) = 0. -/
def IsI0 (f : ℝ → ℝ) : Prop := MonotoneOn f (Ici 0) ∧ f 0 = 0 ∧ IsCadlag f

namespace ServiceLaw
variable (S : ServiceLaw)

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
  hInt_lt_top : ∀ t, 0 ≤ t → S.hInt ν t < ⊤
  age : ∀ φ Dφ, S.IsTestFn φ Dφ → ∀ t, 0 ≤ t →
    ∫ x, φ (x, t) ∂(ν t : Measure ℝ) =
      ∫ x, φ (x, 0) ∂(ν0 : Measure ℝ)
      + ∫ s in Icc 0 t, ∫ x, Dφ (x, s) ∂(ν s : Measure ℝ)
      - ∫ s in Icc 0 t, ∫ x, S.h x * φ (x, s) ∂(ν s : Measure ℝ)
      + ∫ s in Icc 0 t, φ (0, s) ∂(ManyServerFluid.Uniqueness.stieltjes (S.Kbar ν))
  balance : ∀ t, 0 ≤ t → X t = X0 + E t - S.Dbar ν t
  nonidling : ∀ t, 0 ≤ t → 1 - ((ν t).mass : ℝ) = max (1 - X t) 0

/-- Assumption 2 (p. 46). -/
def Assumption2 : Prop :=
  ∃ m0 : ℝ, 0 ≤ m0 ∧ ENNReal.ofReal m0 < S.M ∧
    (BddAbove (S.h '' {x | m0 < x ∧ ENNReal.ofReal x < S.M}) ∨
     LowerSemicontinuousOn S.h {x | m0 < x ∧ ENNReal.ofReal x < S.M})

end ServiceLaw
end ManyServerFluid.Equilibrium


