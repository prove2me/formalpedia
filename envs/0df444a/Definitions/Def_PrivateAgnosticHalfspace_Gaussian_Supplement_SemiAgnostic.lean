-- Prove2me | Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_SemiAgnostic
-- name    : PrivateAgnosticHalfspace_Gaussian_Supplement_SemiAgnostic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:07:07.315397+00:00
-- url     : https://prove2.me/theorems/5387c38e-142e-4628-b794-f5f9512805b9
-- title:
--   Algorithms 3 and 4: private ramp updates and geometric validation
-- statement:
--   Algorithm 3 uses the unnormalized ramp
--   $$r_{a,b}(z)=\begin{cases}0&z\le b-a,\\z-b+a&b-a<z<b+a,\\2a&z\ge b+a.\end{cases}$$
--   Every example vector is radially clipped to $L=2\sqrt d$. The threshold is computed from a label mean plus independent $\operatorname{Lap}(2/(\varepsilon m_0))$ noise: $\widehat\tau=\Phi^{-1}(\operatorname{clip}_{[\kappa,1-\kappa]}((1+\widehat y)/2))$, with $\kappa=c_\kappa\eta$. Initialization normalizes a private noisy mean of $XY$, using a uniform sphere direction when that mean is zero. Laplace noise is an independent fair sign times an exponential variable, and the sphere law is a normalized standard Gaussian.
--
--   For $s=c_s/(1+\log(1/\eta))^{3/2}$ and the positive rounded iteration count $T=\max(1,\lceil C_T(1+\log(1/\eta))^4\rceil)$, the $t$-th step uses $\phi_t=(\pi/2)(1-s^2/64)^t$, $a_t=\sin\phi_t$, $b_t=-\widehat\tau\cos\phi_t$ and step size $e^{\widehat\tau^2/2}s$. The empirical closed-band ramp subgradient is tangent to the current unit direction. Fresh Gaussian noise is projected onto the same tangent space before normalizing the update. Initialization, threshold estimation, and every step use disjoint blocks.
--
--   Algorithm 4 uses internal accuracy $\rho=\alpha/(4A_{\rm err}C_\eta)$, $K=\max(1,\lceil C_K\log(1/\rho)\rceil)$ and $\eta_k=2^k C_\eta\rho$ for $0\le k<K$. Each candidate gets a disjoint equal-sized public block; each call uses a public prefix sufficient for its own iteration schedule and discards the remainder. Calls outside $0<\eta<1/2$ return a fixed halfspace. A final independent validation block selects among the indexed candidate list, retaining multiplicities.
--
--   The block size is a positive rounded universal constant times $(d/\eta^2+d/(\varepsilon\eta))$ times a fixed power of the allowed parameter logarithms. Its concentration failure budget is $\beta/[16K(T+2)]$. Validation uses a public constant times $(\rho^{-2}+(\varepsilon\rho)^{-1})\log(16K/\beta)$. All constants and powers are public and chosen before the unknown labeled distribution. No desired learning, privacy or cost guarantee is assumed in this definition.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006 (October 2026), canonical held submission (not a proceedings-acceptance claim), pp.11–16,34–36, Algorithms 3–4, Eq. (12), Claims 4.3–4.6 and Appendix F

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Supplement_Core

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian.Supplement

noncomputable section

structure SemiConstants where
  error : ℝ
  gridStart : ℝ
  gridLength : ℝ
  etaMax : ℝ
  kappa : ℝ
  step : ℝ
  iterations : ℝ
  blockSample : ℝ
  validation : ℝ
  logPower : ℕ

/-- The unnormalized ramp of (12), with the boundary values fixed by continuity. -/
def ramp (a b z : ℝ) : ℝ := if z ≤ b - a then 0 else if z < b + a then z - b + a else 2 * a

def semiRho (c : SemiConstants) (α : ℝ) : ℝ := α / (4 * c.error * c.gridStart)
def semiK (c : SemiConstants) (α : ℝ) : ℕ := max 1 ⌈c.gridLength * Real.log (1 / semiRho c α)⌉₊
def semiEta (c : SemiConstants) (α : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ k * c.gridStart * semiRho c α

def semiS (c : SemiConstants) (η : ℝ) : ℝ := c.step / (1 + Real.log (1 / η)) ^ (3 / 2 : ℝ)
def semiT (c : SemiConstants) (η : ℝ) : ℕ := max 1 ⌈c.iterations * (1 + Real.log (1 / η)) ^ 4⌉₊

def semiBeta0 (c : SemiConstants) (α β η : ℝ) : ℝ :=
  β / (16 * semiK c α * (semiT c η + 2))

def semiBlock (c : SemiConstants) (d : ℕ) (α β ε δ η : ℝ) : ℕ :=
  max 2 ⌈c.blockSample * ((d : ℝ) / η ^ 2 + d / (ε * η)) *
    logs η (semiBeta0 c α β η) ε δ ^ c.logPower⌉₊

def semiCallSize (c : SemiConstants) (d : ℕ) (α β ε δ η : ℝ) : ℕ :=
  (semiT c η + 2) * semiBlock c d α β ε δ η

/-- The same public length is allocated to every candidate; each call uses its own prefix. -/
def semiTrainingSize (c : SemiConstants) (d : ℕ) (α β ε δ : ℝ) : ℕ :=
  ((List.ofFn fun k : Fin (semiK c α) =>
    let η := semiEta c α k.val
    if 0 < η ∧ η < 1 / 2 then semiCallSize c d α β ε δ η else 0).foldl max 0)

def semiValidationSize (c : SemiConstants) (α β ε : ℝ) : ℕ :=
  max 1 ⌈c.validation * ((semiRho c α)⁻¹ ^ 2 + (ε * semiRho c α)⁻¹) *
    Real.log (16 * (semiK c α : ℝ) / β)⌉₊

def semiSize (c : SemiConstants) (d : ℕ) (α β ε δ : ℝ) : ℕ :=
  semiK c α * semiTrainingSize c d α β ε δ + semiValidationSize c α β ε

/-- Lap(b) as an independent fair sign times an Exp(1) variate. -/
def laplace (b : ℝ) : Measure ℝ :=
  ((gaussianReal 0 1).prod (expMeasure 1)).map fun z =>
    (if 0 ≤ z.1 then b else -b) * z.2

def sphereLaw (d : ℕ) : Measure (Vec d) := (gaussian d).map normalize

def clippedExamples (d : ℕ) (S : List (Example d)) : List (Example d) :=
  S.map fun z => (radial (2 * Real.sqrt (d : ℝ)) z.1, z.2)

/-- At a ramp breakpoint use the source's closed-band subgradient. It is tangent at unit w;
this formula is the derivative of -y*ramp(a,b,<w,x>/||w||) away from the breakpoints. -/
def rampGradient {d : ℕ} (a b : ℝ) (w : Vec d) (S : List (Example d)) : Vec d :=
  average (S.map fun z => if |inner ℝ w z.1 - b| ≤ a then
    -label z.2 • (z.1 - (inner ℝ w z.1) • w) else 0)

/-- Iterative Algorithm 3 state transition with independent tangent Gaussian noise. -/
def semiIterate (c : SemiConstants) (d m₀ : ℕ) (η ε δ τ : ℝ)
    (S : List (Example d)) : ℕ → Vec d → Measure (Vec d)
  | 0, w => Measure.dirac w
  | t + 1, w =>
    (semiIterate c d m₀ η ε δ τ S t w).bind fun v =>
      let s := semiS c η
      let φ := (Real.pi / 2) * (1 - s ^ 2 / 64) ^ t
      let a := Real.sin φ
      let b := -τ * Real.cos φ
      let stepSize := Real.exp (τ ^ 2 / 2) * s
      let σ := 4 * Real.sqrt (d : ℝ) * Real.sqrt (2 * Real.log (2 / δ)) / (ε * m₀)
      let gradient := rampGradient a b v (block S ((t + 2) * m₀) m₀)
      (gaussian d).map fun Z => normalize (v - stepSize •
        (gradient + σ • (Z - (inner ℝ v Z) • v)))

def semiSubroutine (c : SemiConstants) (d m₀ : ℕ) (η ε δ : ℝ)
    (S : List (Example d)) : Measure (Halfspace d) :=
  let S := clippedExamples d S
  let Dτ := block S m₀ m₀
  let Dinit := block S 0 m₀
  let meanY : ℝ := average (Dτ.map fun z => label z.2)
  (laplace (2 / (ε * m₀))).bind fun zτ =>
    let κ := c.kappa * η
    let τ := normalQuantile (max κ (min (1 - κ) ((1 + meanY + zτ) / 2)))
    let σ := 4 * Real.sqrt (d : ℝ) * Real.sqrt (2 * Real.log (2 / δ)) / (ε * m₀)
    let meanXY : Vec d := average (Dinit.map fun z => label z.2 • z.1)
    (gaussian d).bind fun Z =>
      let v := meanXY + σ • Z
      let init := if ‖v‖ = 0 then sphereLaw d else Measure.dirac (normalize v)
      init.bind fun w => (semiIterate c d m₀ η ε δ τ S (semiT c η) w).map fun u => (u,τ)

/-- Algorithm 4, retaining the indexed candidate list. Grid entries outside the subroutine's
range return a public fixed halfspace. The validation block is disjoint from every call. -/
def semiLaw (c : SemiConstants) (d : ℕ) (α β ε δ : ℝ)
    (S : List (Example d)) : Measure (Halfspace d) :=
  let K := semiK c α
  let n₀ := semiTrainingSize c d α β ε δ
  let m := semiValidationSize c α β ε
  let candidates := Measure.pi fun k : Fin K =>
    let η := semiEta c α k.val
    if 0 < η ∧ η < 1 / 2 then
      semiSubroutine c d (semiBlock c d α β ε δ η) η ε δ (block S (k.val * n₀) n₀)
    else Measure.dirac (axis d, 0)
  candidates.bind fun hs => select (List.ofFn hs) classifier ε (block S (K * n₀) m)

def semiInput (c : SemiConstants) (d : ℕ) (α β ε δ : ℝ)
    (S : List (Example d)) : ℕ → ℝ :=
  input [d, S.length, α, β, ε, δ, c.error, c.gridStart, c.gridLength,
    c.etaMax, c.kappa, c.step, c.iterations, c.blockSample, c.validation, c.logPower] S

end
end PrivateAgnosticHalfspace.Gaussian.Supplement


