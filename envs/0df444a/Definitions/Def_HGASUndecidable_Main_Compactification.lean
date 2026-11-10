-- Prove2me | Definitions.Def_HGASUndecidable_Main_Compactification
-- name    : HGASUndecidable_Main_Compactification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:17:33.144016+00:00
-- url     : https://prove2.me/theorems/4f68d782-e0a6-418f-a438-527c817e3c95
-- title:
--   Intended trajectories, quantitative constants, and the compactified reward system
-- statement:
--   The intended map Γ_e is the complete coordinate formula (8.25), using the same coordinate order as X_e. Its theta derivative, reciprocal, oscillator and controller entries are explicit. The weight ρ*=1+1/m* uses the least positive integer satisfying (9.5). D_h is the maximum total degree of the test polynomials. The Fourier series (9.6) defines B_e, and Bounds94 records exactly the stated bounds, continuity, real-valuedness, derivative and constant-term conditions for the fixed rational M₀,K₀. K_e,w*,ε,m_e,κ_e have the formulas (9.7). Homogenization is a finite sum over monomial support and retains the polynomial value on w=0. The state of the compact system has consecutive coordinates y,w,u,u₀. Its set is the product of unit spheres, its field is exactly (9.1)–(9.2), and the reward is (9.3). The admissible even M bounds all X_e and test degrees uniformly in e.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §§8.4.3,9.1–9.4, printed pp. 58–66 (PDF 60–68)

import Definitions.Def_HGASUndecidable_Main_System

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate

namespace HGASUndecidable.Main

/-- Real coordinates of a complex number, in the same order as `splitComplex`. -/
def splitValue (z : ℂ) : List ℝ := [z.re,z.im]

def intendedList (a : DiophantineData) (e : ℕ) (φ : Fin (a.q+a.r) → ℝ) : List ℝ :=
  (List.ofFn (fun l : Fin (a.q+a.r) =>
    [(Real.sqrt (primeAt l.val))⁻¹, Real.sqrt (1-(primeAt l.val : ℝ)⁻¹)] ++
    splitValue (Complex.exp (Complex.I*φ l)))).flatten ++
  splitValue (∏ l, phaseChi a φ l ^ (-rhs a e l)) ++
  (List.ofFn (fun j : Fin a.q =>
    let τ := tauLambda + (4*φ (Fin.castAdd a.r j)/Real.pi : ℝ)
    let z : ℂ := (2/Real.pi : ℝ) * ∑ l, (a.B l j : ℂ)*φ (Fin.natAdd a.q l)
    let w := z+(1+τ)/2
    let wj := (phaseQ a φ j)⁻¹*phaseS a φ j
    [thetaConstant 2 τ^4,thetaConstant 4 τ^4,eisensteinTwo τ,thetaConstant 3 τ,
     thetaConstant 2 τ^2,thetaConstant 3 τ^2,thetaConstant 4 τ^2,eisensteinTwo τ/12,
     theta 1 w τ,theta 2 w τ,theta 3 w τ,theta 4 w τ,
     (Real.pi : ℂ)⁻¹*deriv (fun z => theta 1 z τ) w,(theta 1 w τ)⁻¹,
     Complex.exp (Real.pi*Complex.I*z+Real.pi*Complex.I*τ/4),
     (1-(eta : ℂ)*wj)⁻¹,(1-(eta : ℂ)*wj⁻¹)⁻¹].flatMap splitValue)).flatten

def intended (a : DiophantineData) (e : ℕ) (φ : Fin (a.q+a.r) → ℝ) : State (ns a) :=
  WithLp.toLp 2 (fun i => (intendedList a e φ)[i.val]?.getD 0)

def matrixMass (a : DiophantineData) (b : Bool) : ℕ :=
  ∑ l, ∑ j, (if b then a.B l j else a.A l j).natAbs

def rhoIndex (a : DiophantineData) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧
    (1/256 : ℚ)*(1+1/(m : ℚ))^(4+4*matrixMass a true) ≤ 1/8 ∧
    (1/2 : ℚ)*(1+1/(m : ℚ))^(4+4*matrixMass a false) ≤ 3/4}

def rhoStar (a : DiophantineData) : ℚ := 1+1/(rhoIndex a : ℚ)
def testDegree (a : DiophantineData) : ℕ := ((testsList a).map MvPolynomial.totalDegree).foldl max 0

def gainBound (a : DiophantineData) (K₀ : ℚ) (e : ℕ) : ℚ :=
  K₀*rhoStar a^(4*testDegree a*∑ l, (rhs a e l).natAbs)

def hFourier (a : DiophantineData) (e : ℕ) (k : Fin (a.q+a.r) → ℤ) (i : Fin (nh a)) : ℂ :=
  fourierCoeff (fun φ => (tests a (intended a e φ) i : ℂ)) k

def primitiveComplex (a : DiophantineData) (e : ℕ) (φ : Fin (a.q+a.r) → ℝ) (i : Fin (nh a)) : ℂ :=
  ∑' k : Fin (a.q+a.r) → ℤ, if k = 0 then 0 else
    hFourier a e k i / (Complex.I*∑ l, (k l : ℂ)*(Real.sqrt (primeAt l.val) : ℂ)) * character k φ

def primitive (a : DiophantineData) (e : ℕ) (φ : Fin (a.q+a.r) → ℝ) : State (nh a) :=
  WithLp.toLp 2 (fun i => (primitiveComplex a e φ i).re)

/-- Precisely the properties of the fixed rational constants in Lemma 9.4. -/
def Bounds94 (a : DiophantineData) (M₀ K₀ : ℚ) : Prop :=
  1 ≤ M₀ ∧ 0 < K₀ ∧ ∀ e,
    (∀ φ, ‖intended a e φ‖^2 ≤ (M₀ : ℝ)) ∧ Continuous (primitive a e) ∧
    (∀ φ i, (primitiveComplex a e φ i).im = 0) ∧
    (∀ φ, ‖primitive a e φ‖ ≤ (gainBound a K₀ e : ℝ)) ∧
    (∀ (φ : Fin (a.q+a.r) → ℝ) (t : ℝ), HasDerivAt
      (fun t : ℝ => primitive a e (fun l => φ l + Real.sqrt (primeAt l.val)*t))
      (tests a (intended a e (fun l => φ l + Real.sqrt (primeAt l.val)*t)) -
       WithLp.toLp 2 (fun i => (hFourier a e 0 i).re)) t) ∧
    (¬haltingSet e → ∀ i, hFourier a e 0 i = 0)

def wStar (M₀ : ℚ) : ℚ := 1/(1+M₀)
def margin (M₀ : ℚ) : ℚ := wStar M₀/4

def gainIndex (a : DiophantineData) (M₀ K₀ : ℚ) (e : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ (m : ℚ)^2*wStar M₀ ≥ 4*gainBound a K₀ e^2}
def gain (a : DiophantineData) (M₀ K₀ : ℚ) (e : ℕ) : ℚ :=
  1/(gainIndex a M₀ K₀ e : ℚ)

/-- Polynomial expansion at w=0 is retained, rather than using division by zero. -/
def homogenizedValue {n : ℕ} (M : ℕ) (p : RPoly n) (y : State n) (w : ℝ) : ℝ :=
  ∑ m ∈ p.support, p.coeff m * (∏ i, y i^(m i)) * w^(M-m.sum (fun _ b => b))

def admissiblePower (a : DiophantineData) (M : ℕ) : Prop :=
  Even M ∧ testDegree a ≤ M ∧ ∀ e i, (systemPolys a e i).totalDegree ≤ M

def compactDim (a : DiophantineData) : ℕ := ns a + 1 + nh a + 1

def coordinate {n : ℕ} (v : State n) (k : ℕ) : ℝ := if h : k<n then v ⟨k,h⟩ else 0

def centralY (a : DiophantineData) (v : State (compactDim a)) : State (ns a) :=
  WithLp.toLp 2 (fun i => coordinate v i.val)
def centralW (a : DiophantineData) (v : State (compactDim a)) : ℝ := coordinate v (ns a)
def stereoU (a : DiophantineData) (v : State (compactDim a)) : State (nh a) :=
  WithLp.toLp 2 (fun i => coordinate v (ns a+1+i.val))
def stereoU₀ (a : DiophantineData) (v : State (compactDim a)) : ℝ := coordinate v (ns a+1+nh a)

def compactSet (a : DiophantineData) : Set (State (compactDim a)) :=
  {v | ‖centralY a v‖^2+centralW a v^2=1 ∧ ‖stereoU a v‖^2+stereoU₀ a v^2=1}

def compactVector (a : DiophantineData) (e M : ℕ) (κ : ℚ)
    (v : State (compactDim a)) : State (compactDim a) :=
  let y := centralY a v; let w := centralW a v; let u := stereoU a v; let u₀ := stereoU₀ a v
  let X : State (ns a) := WithLp.toLp 2 (fun i => homogenizedValue M (systemPolys a e i) y w)
  let h : State (nh a) := WithLp.toLp 2 (fun i => homogenizedValue M (testPolys a i) y w)
  let yX := ∑ i, y i * X i
  let uh := ∑ i, u i * h i
  WithLp.toLp 2 (fun i =>
    if hi : i.val < ns a then w*(X ⟨i.val,hi⟩-yX*y ⟨i.val,hi⟩)
    else if i.val = ns a then -w^2*yX
    else if i.val < ns a+1+nh a then
      (1+u₀)*(κ : ℝ)*coordinate h (i.val-(ns a+1)) -
        (κ : ℝ)*uh*coordinate u (i.val-(ns a+1))
    else -(1+u₀)*(κ : ℝ)*uh)

def reward (a : DiophantineData) (M₀ : ℚ) (v : State (compactDim a)) : ℝ :=
  stereoU₀ a v+2*centralW a v^2-1-(margin M₀ : ℝ)

end HGASUndecidable.Main


