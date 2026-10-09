-- Prove2me | Definitions.Def_NearlyUnstableHawkes_CIR_Setting
-- name    : NearlyUnstableHawkes_CIR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:24.839987+00:00
-- url     : https://prove2.me/theorems/6801319a-753e-44b9-b1a3-7c290888fd7e
-- title:
--   Hawkes and resolvent setting for the CIR limit
-- statement:
--   The paper considers simple counting processes $N^T$ with baseline rate $\mu>0$ and excitation kernel $\phi^T=a_T\phi$. For $t\ge0$, the intensity is
--
--   $$\lambda^T_t=\mu+\int_0^t\phi^T(t-s)\,dN^T_s.$$
--
--   The setting defines the natural filtration, compensated process $M^T$, convolution resolvent $\psi^T=\sum_{k\ge1}(\phi^T)^{*k}$, rescaled density $\rho^T(x)=T\psi^T(Tx)/\|\psi^T\|_1$, and the rescaled intensity $C^T_t=(1-a_T)\lambda^T_{tT}$ and count $V^T_t=(1-a_T)N^T_{tT}/T$. It also records Assumptions 1–2, the error process $Y^T$, Skorohod convergence in law on $D[0,1]$, and the exact drift and diffusion coefficients of the CIR limit.
--
--   These shared definitions fix the meaning of the goal and its supporting results.
--
--   **Formalization Note** Observation scales form a positive sequence tending to infinity. The intensity includes the jump at its current time, while stochastic integrands may use its predictable left limit. The Hawkes intensity identity is expressed with extended nonnegative integrals. Skorohod convergence is stated in its coupling form with increasing time changes. Differentiability of $\phi$ at zero is one-sided.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 5, §2.1; pp. 7–10, §2.3 (1)–(3); pp. 18–21, §4.3

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace NearlyUnstableHawkes.CIR

noncomputable section

/-- Rescaled resolvent density (2). -/
def rho (f : ℝ → ℝ) (T x : ℝ) : ℝ :=
  T * NearlyUnstableHawkes.Deterministic.psi f (T * x) / NearlyUnstableHawkes.Deterministic.psiNorm f

/-- The natural filtration of the counting process. -/
def natFiltration {Ω : Type*} (N : ℝ → Ω → ℕ) (t : ℝ) : MeasurableSpace Ω :=
  ⨆ s ∈ Icc (0 : ℝ) t, MeasurableSpace.comap (N s) inferInstance

/-- The right-continuous intensity, with excitation by jumps at `s ≤ t`. -/
def intensity {Ω : Type*} (μ : ℝ) (f : ℝ → ℝ)
    (N : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  μ + ∑ᶠ (s : ℝ) (_ : 0 < s ∧ s ≤ t ∧ NearlyUnstableHawkes.Deterministic.jump N s ω ≠ 0),
    NearlyUnstableHawkes.Deterministic.jump N s ω * f (t - s)

/-- The predictable, left-limit version used at NearlyUnstableHawkes.Deterministic.jump times in stochastic integrands. -/
def intensityPred {Ω : Type*} (μ : ℝ) (f : ℝ → ℝ)
    (N : ℝ → Ω → ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  μ + ∑ᶠ (s : ℝ) (_ : 0 < s ∧ s < t ∧ NearlyUnstableHawkes.Deterministic.jump N s ω ≠ 0),
    NearlyUnstableHawkes.Deterministic.jump N s ω * f (t - s)

/-- A simple Hawkes counting process with its natural-filtration intensity on `[0,T]`. -/
structure IsHawkes {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ℝ) (f : ℝ → ℝ) (T : ℝ)
    (N : ℝ → Ω → ℕ) : Prop where
  meas : ∀ t, 0 ≤ t → Measurable (N t)
  zero : ∀ ω, N 0 ω = 0
  mono : ∀ ω, MonotoneOn (fun t => N t ω) (Ici (0 : ℝ))
  rcont : ∀ ω t, 0 ≤ t → ContinuousWithinAt (fun s => (N s ω : ℝ)) (Ici t) t
  unit_jumps : ∀ ω t, 0 < t → NearlyUnstableHawkes.Deterministic.jump N t ω ≤ 1
  intensity_id : ∀ a b, 0 ≤ a → a < b → b ≤ T →
    ∀ A, MeasurableSet[natFiltration N a] A →
      (∫⁻ ω in A, ((N b ω - N a ω : ℕ) : ℝ≥0∞) ∂P) =
        ∫⁻ ω in A, (∫⁻ s in Ioc a b,
          ENNReal.ofReal (intensity μ f N s ω)) ∂P

/-- Assumption 1, including the half-line interpretation of differentiability at zero. -/
structure Assumption1 (φ φ' : ℝ → ℝ) (m : ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ s → 0 ≤ φ s
  measurable : Measurable (fun s : Ici (0 : ℝ) => φ s)
  integrable : IntegrableOn φ (Ici (0 : ℝ))
  mass : (∫ s in Ici (0 : ℝ), φ s) = 1
  moment_integrable : IntegrableOn (fun s => s * φ s) (Ici (0 : ℝ))
  moment : (∫ s in Ici (0 : ℝ), s * φ s) = m
  deriv : ∀ s, 0 ≤ s → HasDerivWithinAt φ (φ' s) (Ici (0 : ℝ)) s
  deriv_bounded : ∃ C : ℝ, ∀ s, 0 ≤ s → |φ' s| ≤ C
  deriv_integrable : IntegrableOn φ' (Ici (0 : ℝ))

/-- Assumption 2 along the observation-scale sequence. -/
def Assumption2 (T a : ℕ → ℝ) (φ : ℝ → ℝ) : Prop :=
  ∃ Kρ : ℝ, 0 < Kρ ∧ ∀ n x, 0 ≤ x →
    |rho (fun s => a n * φ s) (T n) x| ≤ Kρ

/-- The rescaled intensity `Cᵀ` from (1). -/
def C {Ω : ℕ → Type*} (T a : ℕ → ℝ) (μ : ℝ) (φ : ℝ → ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ) (n : ℕ) (t : ℝ) (ω : Ω n) : ℝ :=
  (1 - a n) * intensity μ (fun s => a n * φ s) (N n) (t * T n) ω

/-- The rescaled count `Vᵀ` from Theorem 2.2. -/
def V {Ω : ℕ → Type*} (T a : ℕ → ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ) (n : ℕ) (t : ℝ) (ω : Ω n) : ℝ :=
  (1 - a n) / T n * N n (t * T n) ω

/-- The plus-sign Fourier convention `ĝ(z)=∫₀∞ e^{izx}g(x) dx`. -/
def fourierPlus (g : ℝ → ℝ) (z : ℝ) : ℂ :=
  ∫ x in Ici (0 : ℝ), Complex.exp (Complex.I * (z : ℂ) * (x : ℂ)) * (g x : ℂ)

/-- `u_T=T(1-a_T)/λ` from p. 9. -/
def uT (T a : ℕ → ℝ) (lam : ℝ) (n : ℕ) : ℝ :=
  T n * (1 - a n) / lam

/-- The p. 18 error kernel, extended by zero for negative inputs as on p. 21. -/
def errorKernel (T a : ℕ → ℝ) (φ : ℝ → ℝ) (m lam : ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else
    (m / lam) * (a n / uT T a lam n) *
      rho (fun s => a n * φ s) (T n) x - Real.exp (-x / (m / lam))

/-- `Yᵀ_t`, using the corrected dummy variable in the p. 20 integral. -/
def Y {Ω : ℕ → Type*} (T a : ℕ → ℝ) (φ : ℝ → ℝ)
    (m lam μ : ℝ) (N : ∀ n, ℝ → Ω n → ℕ)
    (n : ℕ) (t : ℝ) (ω : Ω n) : ℝ :=
  (1 / T n) * NearlyUnstableHawkes.Deterministic.stieltjesM
    (fun s => errorKernel T a φ m lam n (t - s / T n))
    μ (fun s => a n * φ s) (N n) (t * T n) ω

/-- Cadlag paths restricted to `[0,1]`. -/
def IsCadlag01 (x : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ico (0 : ℝ) 1, ContinuousWithinAt x (Ici t) t) ∧
  ∀ t ∈ Ioc (0 : ℝ) 1, ∃ l : ℝ, Tendsto x (𝓝[<] t) (𝓝 l)

/-- Increasing continuous time changes of `[0,1]` onto itself. -/
def IsTimeChange01 (l : ℝ → ℝ) : Prop :=
  ContinuousOn l (Icc (0 : ℝ) 1) ∧
  StrictMonoOn l (Icc (0 : ℝ) 1) ∧
  l '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1

/-- Skorohod `J₁` path convergence on `[0,1]`. -/
def SkorohodTendsto01 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  (∀ n, IsCadlag01 (xs n)) ∧ IsCadlag01 x ∧
  ∃ l : ℕ → ℝ → ℝ, (∀ n, IsTimeChange01 (l n)) ∧
    TendstoUniformlyOn (fun n => xs n ∘ l n) x atTop (Icc (0 : ℝ) 1) ∧
    TendstoUniformlyOn l id atTop (Icc (0 : ℝ) 1)

/-- Convergence in law on `D[0,1]`, expressed by a Skorohod coupling. -/
def ConvInLawSkorohod01 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (xs : ∀ n, ℝ → Ω n → ℝ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (x : ℝ → Ω' → ℝ) : Prop :=
  ∃ (Ω'' : Type) (m'' : MeasurableSpace Ω''),
    letI := m''
    ∃ P'' : Measure Ω'', ∃ W : ℕ → Ω'' → ℝ → ℝ, ∃ W' : Ω'' → ℝ → ℝ,
      IsProbabilityMeasure P'' ∧
      (∀ n, IdentDistrib
        (fun ω (t : Icc (0 : ℝ) 1) => W n ω t.val)
        (fun ω (t : Icc (0 : ℝ) 1) => xs n t.val ω) P'' (P n)) ∧
      IdentDistrib
        (fun ω (t : Icc (0 : ℝ) 1) => W' ω t.val)
        (fun ω (t : Icc (0 : ℝ) 1) => x t.val ω) P'' P' ∧
      ∀ᵐ ω ∂P'', SkorohodTendsto01 (fun n => W n ω) (W' ω)

/-- Drift `(μ-x) λ/m` in the CIR equation. -/
def cirDrift (μ lam m : ℝ) : ℝ≥0 × EthierKurtz.SDEState 1 →
    EthierKurtz.SDEState 1 :=
  fun p => EuclideanSpace.single 0 ((μ - p.2 0) * lam / m)

/-- Diffusion coefficient `(√λ/m)√x` in the CIR equation. -/
def cirDiff (lam m : ℝ) : ℝ≥0 × EthierKurtz.SDEState 1 →
    EthierKurtz.SDEDiffusion 1 :=
  fun p => EuclideanSpace.single (0, 0)
    (Real.sqrt lam / m * Real.sqrt (p.2 0))

end
end NearlyUnstableHawkes.CIR


