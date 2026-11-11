-- Prove2me | Definitions.Def_MemSampleNGCA_Main_Framework
-- name    : MemSampleNGCA_Main_Framework
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:40:48.616843+00:00
-- url     : https://prove2.me/theorems/023dbf2d-eb93-4b35-b68a-4d2e076feef8
-- title:
--   The testing framework of Appendix B: state laws µ_i, ν_i, mixtures P_f, T_KL, T_q, likelihoods λ, Λ, Λ^(h), Π, Ψ
-- statement:
--   Let $\Theta$ carry a probability measure $\pi$, let $P_0$ be a probability measure on $\mathcal X$, and let $P_\theta=p(\theta,\cdot)\,P_0$ for a density $p$. For a streaming algorithm run on $N$ samples:
--
--   - **State laws** (14): $\mu_i(v)=\int_\Theta P_\theta(V_i=v)\,\pi(d\theta)$ and $\nu_i(v)=P_0(V_i=v)$ for $v\in\{0,1\}^B$.
--   - **Admissible densities** (15): $F_h=\{f:\Theta\to\mathbb R_{\ge0}:\int f\,d\pi=1,\ f\le e^h\}$.
--   - **Mixtures** (16): $P_f=\int_\Theta P_\theta f(\theta)\,\pi(d\theta)$.
--   - **Functionals** (17a)–(17b):
--   $$T_{KL}(h)=\sup_{f\in F_h}\mathrm{KL}(P_f,P_0),\qquad T_q(h)=\sup_{f\in F_h}\mathbb E_{X\sim P_0}\Big[\Big\{\int_\Theta\tfrac{dP_\theta}{dP_0}(X)f(\theta)\,\pi(d\theta)\Big\}^q\Big].$$
--   - **Posterior mixtures** (18): $\rho_{i,v}(\theta)=P_\theta(V_i=v)/\mu_i(v)$ and $P_{\rho_{i,v}}=\int P_\theta\rho_{i,v}(\theta)\,\pi(d\theta)$.
--   - **Likelihoods** (Step 1): $\lambda_{i,v}(\theta)=P_\theta(V_i=v)/\nu_i(v)$, $\Lambda_{0,v}=\lambda_{0,v}$, $\Lambda^{(h)}_{i,v}=\Lambda_{i,v}\mathbf 1\{\Lambda_{i,v}\le e^h\}$ and $\Lambda_{i+1,v'}(\theta)=\mathbb E_0\big[\Lambda^{(h)}_{i,V_i}(\theta)\,\tfrac{dP_\theta}{dP_0}(X_{i+1})\,\big|\,V_{i+1}=v'\big]$, where $\mathbb E_0$ is the law of the run under the null.
--   - **Step 5 objects**: $\Pi_{\ell,v}(\theta)=\mathbf 1\{\Lambda_{\ell,v}(\theta)>e^h\}/\int_\Theta\mathbf 1\{\Lambda_{\ell,v}>e^h\}\,d\pi$ and $\Psi_{\ell,v}=\sum_{v'}\nu_\ell(v')\{\int_\Theta\Lambda_{\ell,v'}\Pi_{\ell,v}\,d\pi\}^q$.
--   - **Setting of Theorem B.1** (`IsBoundedDensityFamily`): $\pi,P_0$ are probability measures, $p\ge0$ is jointly measurable with $\int p(\theta,\cdot)\,dP_0=1$, and $p(\theta,\cdot)\le M$ $P_0$-a.e. for every $\theta$.
--
--   These objects carry the paper's general memory–sample bound (Theorem B.1).
--
--   **Formalization Note.** All probabilities, densities, likelihoods, $\mathrm{KL}$ (Mathlib's `klDiv`), $T_{KL}$ and $T_q$ are `ℝ≥0∞`-valued. Suprema are `⨆` in `ℝ≥0∞`, and $q$-th powers are `ℝ≥0∞` real powers. Members of $F_h$ are measurable. $P_f$ and $P_{\rho_{i,v}}$ are written as $P_0$ with density $x\mapsto\int p(\theta,x)f(\theta)\,\pi(d\theta)$, which is the same measure by Tonelli. A conditional expectation given $\{V_{i+1}=v'\}$ is $\mathbb E_0[Y\mathbf 1\{V_{i+1}=v'\}]/\nu_{i+1}(v')$. A ratio with zero denominator follows `ℝ≥0∞` division; its numerator then vanishes, so the value is $0$, matching the paper's convention that such terms carry weight $0$. $\Lambda_{i,v}$ is defined for $i\le N$ (it needs $X_i$) and set to $0$ beyond. The paper's $\pi$ is the uniform measure on $\Theta\subseteq S^{d-1}$; here it is any probability measure.
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), pp. 16–21 (PDF 18–23), Eqs. (14)–(18), Step 1 and Step 5 of §B.1

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-! # The general testing framework of Appendix B

Pensia, Gupta, Verchand, Sharan, Vedantam, *Memory-Sample Tradeoffs in High-Dimensional
Statistics*, STOC 2027 submission (manuscript sha256 ac94994a…), Appendix B: Equations (14)–(18)
(pp. 16–17, PDF 18–19), the likelihoods of Step 1 (p. 17, PDF 19), and the objects of Step 5
(pp. 20–21, PDF 22–23).

Data: a parameter space `Θ` with a probability measure `π` (the paper's uniform measure on `Θ`),
an observation space `X` with the null `P₀`, and the family `P_θ = p(θ, ·) · P₀` given by a
density `p(θ, x) = dP_θ/dP₀ (x)`. All probabilities and densities are `ℝ≥0∞`-valued; a
conditional expectation given an event of positive probability is the ratio
`E[Y · 1_S] / P(S)`. -/

variable {Θ : Type*} [MeasurableSpace Θ] {X : Type*} [MeasurableSpace X]
variable {B : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The setting of Theorem B.1: `π` and `P₀` are probability measures, `p` is a jointly
measurable nonnegative density with `∫ p(θ, ·) dP₀ = 1` for every `θ` (so each `P_θ` is a
probability measure with `dP_θ/dP₀ = p(θ, ·)`), and `0 ≤ dP_θ/dP₀ ≤ M` for every `θ`. -/
structure IsBoundedDensityFamily (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (M : ℝ) :
    Prop where
  prob_π : IsProbabilityMeasure π
  prob_P₀ : IsProbabilityMeasure P₀
  meas : Measurable (Function.uncurry p)
  nonneg : ∀ θ x, 0 ≤ p θ x
  total : ∀ θ, ∫⁻ x, ENNReal.ofReal (p θ x) ∂P₀ = 1
  bound : ∀ θ, ∀ᵐ x ∂P₀, p θ x ≤ M

/-- `P_θ`, the law with density `p(θ, ·)` against `P₀`. -/
noncomputable def Ptheta (P₀ : Measure X) (p : Θ → X → ℝ) (θ : Θ) : Measure X :=
  P₀.withDensity (fun x => ENNReal.ofReal (p θ x))

/-- The admissible (diffuse) densities `F_h = {f : Θ → ℝ≥0 : ∫ f dπ = 1, f ≤ e^h}` (15);
densities are measurable, and written `ℝ≥0∞`-valued (the bound `f ≤ e^h` makes them finite). -/
def Fh (π : Measure Θ) (h : ℝ) : Set (Θ → ℝ≥0∞) :=
  {f | Measurable f ∧ ∫⁻ θ, f θ ∂π = 1 ∧ ∀ θ, f θ ≤ ENNReal.ofReal (Real.exp h)}

/-- The density of `P_f` against `P₀`: `x ↦ ∫_Θ (dP_θ/dP₀)(x) f(θ) π(dθ)`. -/
noncomputable def mixDensity (π : Measure Θ) (p : Θ → X → ℝ) (f : Θ → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (p θ x) * f θ ∂π

/-- The mixture `P_f = ∫_Θ P_θ f(θ) π(dθ)` (16), written through its density against `P₀`. -/
noncomputable def mixture (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (f : Θ → ℝ≥0∞) :
    Measure X :=
  P₀.withDensity (mixDensity π p f)

/-- `T_KL(h) = sup_{f ∈ F_h} KL(P_f, P₀)` (17a). -/
noncomputable def TKL (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (h : ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ Fh π h, InformationTheory.klDiv (mixture π P₀ p f) P₀

/-- `T_q(h) = sup_{f ∈ F_h} E_{X∼P₀}[{∫_Θ (dP_θ/dP₀)(X) f(θ) π(dθ)}^q]` (17b). -/
noncomputable def Tq (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (q h : ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ Fh π h, ∫⁻ x, (mixDensity π p f x) ^ q ∂P₀

/-- `ν_i(v) = P₀(V_i = v)` (14): the law of the state after `i` samples under the null. -/
noncomputable def nu (A : StreamingAlg B X Ω) (N : ℕ) (P₀ : Measure X) (i : ℕ)
    (v : Fin B → Bool) : ℝ≥0∞ :=
  A.stateProb N P₀ i v

/-- `µ_i(v) = ∫_Θ P_θ(V_i = v) π(dθ)` (14): the law of the state after `i` samples under the
mixture prior. -/
noncomputable def mu (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (i : ℕ) (v : Fin B → Bool) : ℝ≥0∞ :=
  ∫⁻ θ, A.stateProb N (Ptheta P₀ p θ) i v ∂π

/-- `ν_i` as a measure on the state space `{0,1}^B`. -/
noncomputable def nuMeas (A : StreamingAlg B X Ω) (N : ℕ) (P₀ : Measure X) (i : ℕ) :
    Measure (Fin B → Bool) :=
  ∑ v, nu A N P₀ i v • Measure.dirac v

/-- `µ_i` as a measure on the state space `{0,1}^B`. -/
noncomputable def muMeas (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (i : ℕ) : Measure (Fin B → Bool) :=
  ∑ v, mu A N π P₀ p i v • Measure.dirac v

/-- The posterior density `ρ_{i,v}(θ) = P_θ(V_i = v)/µ_i(v)` (before (18)). -/
noncomputable def rho (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (i : ℕ) (v : Fin B → Bool) (θ : Θ) : ℝ≥0∞ :=
  A.stateProb N (Ptheta P₀ p θ) i v / mu A N π P₀ p i v

/-- `P_{ρ_{i,v}} = ∫_Θ P_θ · P_θ(V_i = v)/µ_i(v) π(dθ)` (18). -/
noncomputable def Prho (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (i : ℕ) (v : Fin B → Bool) : Measure X :=
  mixture π P₀ p (rho A N π P₀ p i v)

/-- The likelihood `λ_{i,v}(θ) = P_θ(V_i = v)/ν_i(v)` (Step 1, p. 17). -/
noncomputable def lam (A : StreamingAlg B X Ω) (N : ℕ) (P₀ : Measure X) (p : Θ → X → ℝ)
    (i : ℕ) (v : Fin B → Bool) (θ : Θ) : ℝ≥0∞ :=
  A.stateProb N (Ptheta P₀ p θ) i v / nu A N P₀ i v

/-- Elementary conditional expectation given an event: `E_μ[Y | S] = E_μ[Y · 1_S] / μ(S)`. -/
noncomputable def condOnEvent {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (Y : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ ω in S, Y ω ∂μ) / μ S

/-- Truncation at level `e^h`: `a · 1{a ≤ e^h}`. -/
noncomputable def truncAt (h : ℝ) (a : ℝ≥0∞) : ℝ≥0∞ :=
  if a ≤ ENNReal.ofReal (Real.exp h) then a else 0

/-- The propagated truncated likelihood `Λ_{i,v}` (Step 1, p. 17): `Λ_{0,v} = λ_{0,v}` and
`Λ_{i+1,v'}(θ) = E₀[Λ^{(h)}_{i,V_i}(θ) · (dP_θ/dP₀)(X_{i+1}) | V_{i+1} = v']`, the conditional
expectation under the null law of the run (samples i.i.d. `P₀`, seeds i.i.d. `R`). It is defined
for `i ≤ N` (it needs `X_{i+1}`); beyond `N` it is set to `0`. -/
noncomputable def Lam (A : StreamingAlg B X Ω) (N : ℕ) (P₀ : Measure X) (p : Θ → X → ℝ)
    (h : ℝ) : ℕ → (Fin B → Bool) → Θ → ℝ≥0∞
  | 0 => fun v θ => lam A N P₀ p 0 v θ
  | i + 1 => fun v' θ =>
    if hi : i < N then
      condOnEvent (A.sampleLaw N P₀) {ω | A.state ω.1 ω.2 (i + 1) = v'}
        (fun ω => truncAt h (Lam A N P₀ p h i (A.state ω.1 ω.2 i) θ) *
          ENNReal.ofReal (p θ (ω.1 ⟨i, hi⟩)))
    else 0

/-- The truncated likelihood `Λ^{(h)}_{i,v} = Λ_{i,v} · 1{Λ_{i,v} ≤ e^h}`. -/
noncomputable def LamTrunc (A : StreamingAlg B X Ω) (N : ℕ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (h : ℝ) (i : ℕ) (v : Fin B → Bool) (θ : Θ) : ℝ≥0∞ :=
  truncAt h (Lam A N P₀ p h i v θ)

/-- `∫_Θ 1{Λ_{ℓ,v}(θ) > e^h} π(dθ)`, the `π`-mass of the parameters truncated at `(ℓ, v)`. -/
noncomputable def truncMass (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (h : ℝ) (ℓ : ℕ) (v : Fin B → Bool) : ℝ≥0∞ :=
  ∫⁻ θ, (if ENNReal.ofReal (Real.exp h) < Lam A N P₀ p h ℓ v θ then 1 else 0) ∂π

/-- `Π_{ℓ,v}(θ) = 1{Λ_{ℓ,v}(θ) > e^h} / ∫_Θ 1{Λ_{ℓ,v} > e^h} dπ` (Step 5, Case 2, p. 20). -/
noncomputable def PiDist (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (h : ℝ) (ℓ : ℕ) (v : Fin B → Bool) (θ : Θ) : ℝ≥0∞ :=
  (if ENNReal.ofReal (Real.exp h) < Lam A N P₀ p h ℓ v θ then 1 else 0) /
    truncMass A N π P₀ p h ℓ v

/-- The potential `Ψ_{ℓ,v} = Σ_{v'} ν_ℓ(v') {∫_Θ Λ_{ℓ,v'}(θ) Π_{ℓ,v}(θ) π(dθ)}^q` (p. 21). -/
noncomputable def Psi (A : StreamingAlg B X Ω) (N : ℕ) (π : Measure Θ) (P₀ : Measure X)
    (p : Θ → X → ℝ) (h q : ℝ) (ℓ : ℕ) (v : Fin B → Bool) : ℝ≥0∞ :=
  ∑ v', nu A N P₀ ℓ v' *
    (∫⁻ θ, Lam A N P₀ p h ℓ v' θ * PiDist A N π P₀ p h ℓ v θ ∂π) ^ q

end MemSampleNGCA.Main


