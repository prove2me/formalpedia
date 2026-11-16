-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_pathSpace
-- name    : TFIMPhaseDiagram_Classical_Supplement_pathSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:49.205373+00:00
-- url     : https://prove2.me/theorems/d8f206a1-b800-47e2-8f75-e6e0115083bb
-- title:
--   Continuous spin paths, Curie–Weiss laws and variational functionals
-- statement:
--   The circle $S=\mathbb R/\mathbb Z$ is represented by $[0,1)$ with Lebesgue measure of total mass one. Its real Hilbert space is $L^2(S)$. A finite jump record $(d,u,(t_k))$ from the published Poisson spin-path model is sent to the equivalence class of
--   $$
--   \sigma(t)=u\prod_{k<d}(1-2\mathbf1_{[t_k,\infty)}(t)).
--   $$
--   The finite subset expansion realizes this class using actual $L^2$ indicators. The law $\nu_\eta$ is the push-forward of the published even-parity path law; this is a continuous path-space construction.
--
--   For $n\ge1$, let $\bar\sigma=n^{-1}\sum_i\sigma_i$, let $\mu_n$ be the tilt of $\nu_\eta^{\otimes n}$ by $bn\|\bar\sigma\|^2/2$, and let $\tilde\rho_n$ and $\rho_n$ be the independent and tilted average laws. The bundle defines the log moment-generating functional $\Lambda_\eta(f)$, $\Phi_{b,\eta}(f)=\Lambda_\eta(f)-\|f\|^2/(2b)$, and the extended-real Legendre rates $\tilde I$, $I=\tilde I-b\|x\|^2/2$, and $J=I-\inf I$.
--
--   It also defines the positive magnetization by its stationary equation, the scalar and functional gap constants from the source proofs, and the conditioned gadget integrals $Q_s$ and $A_0$ with the strict comparison and negative-sign tie rule of (18). Every measurable spin-valued function is admitted as a boundary condition through its $L^2$ class. These definitions supply the common objects for the concentration and gadget results.
--
--   **Formalization Note** The magnetization choice has a zero fallback outside its existence domain; the accompanying theorems establish existence and uniqueness throughout the supercritical domain. Extended rate values, including $+\infty$, remain extended values. No new condition is imposed on a reused base definition.
--
--   The bundle also defines the least enlarged concentration threshold from p.18 and the positive integer ceiling of the explicit gadget threshold on p.19. Their existence and validity are conclusions of Corollary 23, not hypotheses or structure fields.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 5–6, 14–19; Definitions 5 and 24, equations (16)–(27), proof of Lemma 27

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Lebesgue measure on the unit circle, represented on [0,1). -/
def circleVolume : Measure ℝ := volume.restrict (Set.Ico 0 1)
instance : IsFiniteMeasure circleVolume := by unfold circleVolume; infer_instance
abbrev CircleL2 := Lp ℝ 2 circleVolume
instance : MeasurableSpace CircleL2 := borel CircleL2
instance : BorelSpace CircleL2 := ⟨rfl⟩

def constL2 (c : ℝ) : CircleL2 := (memLp_const c).toLp (fun _ => c)
def jumpUpper (σ : PathData) (A : Finset ℕ) : Set ℝ := ⋂ k ∈ A, Set.Ici (σ.2.2 k)

/-- Finite expansion of spin(u) Π_k (1-2·1_[t_k,∞)); hence exactly pathValue a.e.
This uses actual L² indicators, with no default value on bad representatives. -/
def pathL2 (σ : PathData) : CircleL2 :=
  ∑ A ∈ (Finset.range σ.1).powerset,
    (spin σ.2.1 * (-2 : ℝ)^A.card) •
      indicatorConstLp 2
        (Finset.measurableSet_biInter A (fun _ _ => measurableSet_Ici))
        (measure_ne_top circleVolume (jumpUpper σ A)) (1 : ℝ)

def nuL2 (η : ℝ) : Measure CircleL2 := Measure.map pathL2 (pathLaw η false)
def l1Norm (f : CircleL2) : ℝ := ∫ t, |f t| ∂circleVolume
def circleMean (f : CircleL2) : ℝ := inner ℝ (constL2 1) f

def averageL2 {n : ℕ} (σ : Fin n → CircleL2) : CircleL2 := (n : ℝ)⁻¹ • ∑ i, σ i
def productL2 (η : ℝ) (n : ℕ) : Measure (Fin n → CircleL2) :=
  Measure.pi (fun _ => nuL2 η)
def cwEnergy (b : ℝ) {n : ℕ} (σ : Fin n → CircleL2) : ℝ :=
  b * n / 2 * ‖averageL2 σ‖^2
def cwLaw (b η : ℝ) (n : ℕ) : Measure (Fin n → CircleL2) :=
  tilt (productL2 η n) (cwEnergy b)
def averageLaw (η : ℝ) (n : ℕ) : Measure CircleL2 :=
  Measure.map averageL2 (productL2 η n)
def tiltedAverageLaw (b η : ℝ) (n : ℕ) : Measure CircleL2 :=
  tilt (averageLaw η n) (fun x => (n : ℝ) * (b / 2 * ‖x‖^2))

def supercritical (b η : ℝ) : Prop := 0 < b ∧ 0 < η ∧ 1 < b / η * Real.tanh η

def cumulant (η : ℝ) (f : CircleL2) : ℝ :=
  Real.log (∫ σ, Real.exp (inner ℝ f σ) ∂nuL2 η)
def phi (b η : ℝ) (f : CircleL2) : ℝ := cumulant η f - ‖f‖^2 / (2*b)
def scalarPhi (b η r : ℝ) : ℝ := phi b η (constL2 r)
def radius (η r : ℝ) : ℝ := Real.sqrt (η^2 + r^2)
def IsMagnetization (b η m : ℝ) : Prop :=
  0 < m ∧ m < 1 ∧ Real.tanh (radius η (b*m)) / radius η (b*m) = 1/b
/-- Choice of the unique positive solution; all uses establish existence and uniqueness.
Outside the supercritical regime the fallback is zero, never used by a theorem. -/
def magnetization (b η : ℝ) : ℝ :=
  if h : ∃ m, IsMagnetization b η m then Classical.choose h else 0

def scalarGap (b η : ℝ) : ℝ := η * (b / η * Real.tanh η - 1) / 8
def functionalGap (b η : ℝ) : ℝ :=
  let m := magnetization b η
  min (scalarGap b η / 13)
    (b / Real.cosh η * Real.exp (-3*b*m/2) * (1-Real.exp (-b*m/2)) / (4*m))
def phaseDistanceSq (m : ℝ) (q : CircleL2) : ℝ :=
  min (‖q - constL2 m‖^2) (‖q - constL2 (-m)‖^2)

/-- Full extended-real Legendre transform; not a real supremum with default 0. -/
def cramerRate (η : ℝ) (x : CircleL2) : EReal :=
  ⨆ f : CircleL2, ((inner ℝ f x - cumulant η f : ℝ) : EReal)
def unnormalizedRate (b η : ℝ) (x : CircleL2) : EReal :=
  cramerRate η x - ((b/2 * ‖x‖^2 : ℝ) : EReal)
def rateMinimum (b η : ℝ) : EReal := ⨅ x : CircleL2, unnormalizedRate b η x
def cwRate (b η : ℝ) (x : CircleL2) : EReal :=
  unnormalizedRate b η x - rateMinimum b η

/-- Spin-valued L² classes, including every measurable ±1 function, not only Poisson paths. -/
def IsSpinClass (f : CircleL2) : Prop := ∀ᵐ t ∂circleVolume, f t = 1 ∨ f t = -1

def gadgetPhase (m : ℝ) {r : ℕ} (σ : Fin r → CircleL2) : Bool :=
  decide (‖averageL2 σ - constL2 m‖ < ‖averageL2 σ - constL2 (-m)‖)
def phaseSign (s : Bool) : ℝ := if s then 1 else -1

def gadgetEnergy (b : ℝ) {t r : ℕ} (τ : Fin t → CircleL2) (σ : Fin r → CircleL2) : ℝ :=
  b / (2*r) * ‖(∑ j, τ j) + ∑ i, σ i‖^2
def gadgetQ (b η m : ℝ) {t : ℕ} (r : ℕ) (τ : Fin t → CircleL2) (s : Bool) : ℝ :=
  ∫ σ : Fin r → CircleL2, (if gadgetPhase m σ = s then Real.exp (gadgetEnergy b τ σ) else 0) ∂productL2 η r
def gadgetA (b η m δ : ℝ) (r : ℕ) : ℝ :=
  ∫ σ : Fin r → CircleL2, (if ‖averageL2 σ - constL2 m‖ < δ then
    Real.exp (b*r/2 * ‖averageL2 σ‖^2) else 0) ∂productL2 η r

/-- Least enlarged concentration threshold used on pp.18–19. Its existence is
asserted by the theorems, not assumed in the definition. -/
def IsConcentrationThreshold (b η δ : ℝ) (N : ℕ) : Prop :=
  0 < N ∧ ∀ n : ℕ, N ≤ n →
    (cwLaw b η n).real {σ | δ ≤ ‖averageL2 σ - constL2 (magnetization b η)‖ ∧
      δ ≤ ‖averageL2 σ - constL2 (-magnetization b η)‖} ≤
      Real.exp (-(n:ℝ)*(functionalGap b η/2)*δ^2) ∧
    Real.exp (-(n:ℝ)*(functionalGap b η/4)*δ^2) ≤ 1/2

def concentrationThreshold (b η δ : ℝ) : ℕ :=
  if h : ∃ N, IsConcentrationThreshold b η δ N then Nat.find h else 0

/-- Integer ceiling of the explicit threshold on p.19; +1 ensures positivity. -/
def gadgetThreshold (b η δ : ℝ) (t : ℕ) : ℕ :=
  let c := functionalGap b η/4
  let R' := 2*b*t*(1-δ) + Real.log (2/(Real.exp (b*t*δ)-1))
  max (concentrationThreshold b η δ)
    (⌈max ((t:ℝ)/δ) (max 0 R'/(c*δ^2)+(t:ℝ)*Real.sqrt (b/(2*c*δ^2)))⌉₊+1)

end TFIMPhaseDiagram.Classical.Supplement


