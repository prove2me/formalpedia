-- Prove2me | Definitions.Def_MasulloRH_ThetaCertificate
-- name    : MasulloRH_ThetaCertificate
-- status  : Definition
-- author  : @sflicht
-- created : 2026-11-21T19:57:16.513075+00:00
-- url     : https://prove2.me/theorems/55b584ef-23cf-4152-bb89-68f7cb944cd5
-- title:
--   Finite theta models and exact rational interval-certificate data
-- statement:
--   This module defines auxiliary finite functions and rational certificate data for bounding the canonical theta residual. For a truncation length $K\in\mathbb N$, put
--
--   $$P_K(r)=\sum_{n=1}^K\bigl(r^{n^2}-3r^{4n^2}+2r^{16n^2}\bigr).$$
--
--   The direct and reflected finite models are
--
--   $$D_K(x)=2P_K(e^{-\pi e^{2x}}),\qquad R_K(x)=e^{-x}P_K(e^{-(\pi/16)e^{-2x}}).$$
--
--   The module also defines their formal derivative expressions, the Gaussian pulse model, finite residuals formed with a chosen branch for each translate, and explicit truncation-error expressions. These are auxiliary definitions; their relation to the actual infinite theta function and its energy is established in separate theorems.
--
--   The rational certificate structures store candidate enclosures and exact arithmetic conditions. An exponential row specifies a rational argument and lower and upper bounds, together with one of four methods: the value at zero, positive Taylor scaling, negative Taylor scaling, or an integer-power upper bound for a negative argument. A theta row stores the rational interval endpoints and intermediate polynomial, product and derivative enclosures for either finite branch. The validity predicates are explicit rational equalities and inequalities; unsupported exponential modes are invalid.
--
--   This definition asserts no real exponential bound, no finite-model enclosure, and no bound on the actual theta residual. Separate soundness theorems connect valid rational data to those analytic conclusions. The canonical infinite theta, pulse, residual, energy and eleven-term witness remain the existing public definitions.
-- source:
--   Reusable certificate data constructed for the independent theta-approximation branch of the Prove2Me Masullo RH specialization mission. The finite Gaussian model, rational Taylor bounds and interval arithmetic are supporting constructions for this contribution, not claims extracted from a particular manuscript page. The actual residual uses the unchanged GaussianThetaApproximation definition, and the fixed witness is MasulloRH_HeightTwoWitness.

import Mathlib

/-! Pure finite-model and rational-check definitions for public theta certificates.
The canonical infinite theta, pulse, residual, energy and witness definitions
remain in their existing public Definition modules. No bound is asserted here. -/

set_option autoImplicit false
open scoped BigOperators

namespace MasulloRH.CertifiedExp

noncomputable def thetaPolynomial (K : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range K,
    (r ^ ((n + 1) ^ 2) - 3 * r ^ (4 * (n + 1) ^ 2) +
      2 * r ^ (16 * (n + 1) ^ 2))

noncomputable def thetaMomentPolynomial (K : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range K,
    ((((n + 1) ^ 2 : ℕ) : ℝ) * r ^ ((n + 1) ^ 2) -
      3 * ((4 * (n + 1) ^ 2 : ℕ) : ℝ) * r ^ (4 * (n + 1) ^ 2) +
      2 * ((16 * (n + 1) ^ 2 : ℕ) : ℝ) * r ^ (16 * (n + 1) ^ 2))

end MasulloRH.CertifiedExp

namespace MasulloRH.Certificates

open MasulloRH.CertifiedExp

noncomputable def thetaDirectModel (K : ℕ) (x : ℝ) : ℝ :=
  2 * thetaPolynomial K (Real.exp (-Real.pi * Real.exp (2 * x)))

noncomputable def thetaDirectDerivative (K : ℕ) (x : ℝ) : ℝ :=
  -4 * (Real.pi * Real.exp (2 * x)) *
    thetaMomentPolynomial K (Real.exp (-Real.pi * Real.exp (2 * x)))

noncomputable def thetaReflectedModel (K : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) *
    thetaPolynomial K (Real.exp (-(Real.pi / 16) * Real.exp (-2 * x)))

noncomputable def thetaReflectedDerivative (K : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) *
    (-thetaPolynomial K (Real.exp (-(Real.pi / 16) * Real.exp (-2 * x))) +
      2 * ((Real.pi / 16) * Real.exp (-2 * x)) *
        thetaMomentPolynomial K (Real.exp (-(Real.pi / 16) * Real.exp (-2 * x))))

noncomputable def thetaBranchModel (K : ℕ) (reflected : Bool) (x : ℝ) : ℝ :=
  if reflected then thetaReflectedModel K x else thetaDirectModel K x

noncomputable def thetaBranchDerivative (K : ℕ) (reflected : Bool) (x : ℝ) : ℝ :=
  if reflected then thetaReflectedDerivative K x else thetaDirectDerivative K x

/-- Both choices include the rational cutoff itself. -/

def thetaBranchValid (reflected : Bool) (x : ℝ) : Prop :=
  if reflected then x ≤ -1 else -1 ≤ x

noncomputable def pulseModel (T x : ℝ) : ℝ :=
  ((T + 1) / Real.sqrt Real.pi) * Real.exp (-(T + 1) ^ 2 * x ^ 2)

noncomputable def pulseDerivative (T x : ℝ) : ℝ :=
  (-2 * (T + 1) ^ 2 * x) * pulseModel T x

noncomputable def finiteResidualModel {m : ℕ} (K : ℕ) (T : ℝ)
    (a y : Fin m → ℝ) (branch : Fin m → Bool) (x : ℝ) : ℝ :=
  pulseModel T x - ∑ i, a i * thetaBranchModel K (branch i) (x - y i)

noncomputable def finiteResidualDerivative {m : ℕ} (K : ℕ) (T : ℝ)
    (a y : Fin m → ℝ) (branch : Fin m → Bool) (x : ℝ) : ℝ :=
  pulseDerivative T x - ∑ i, a i * thetaBranchDerivative K (branch i) (x - y i)

noncomputable def thetaTruncationFactor (K : ℕ) : ℝ :=
  24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3)

noncomputable def finiteResidualErrorBudget {m : ℕ} (K : ℕ)
    (a y : Fin m → ℝ) (left : ℝ) : ℝ :=
  thetaTruncationFactor K *
    ∑ i, |a i| * (1 + Real.exp (-(left - y i)) / 2)

end MasulloRH.Certificates

namespace MasulloRH.HeightTwoScalar

def taylorRat (x : ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℚ)

def remainderRat (x : ℚ) (n : ℕ) : ℚ :=
  x ^ n * (n + 1 : ℕ) / ((n.factorial : ℚ) * n)

def PositiveExpCheck (t x a b l u : ℚ) (power order : ℕ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 < order ∧ t = power * x ∧ 0 < a ∧
    a ≤ taylorRat x order - remainderRat x order ∧
    taylorRat x order + remainderRat x order ≤ b ∧
    l ≤ a ^ power ∧ b ^ power ≤ u

def NegativeExpCheck (t x a b l u : ℚ) (power order : ℕ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ 0 < order ∧ t = power * x ∧ 0 < a ∧
    a ≤ taylorRat x order - remainderRat x order ∧
    taylorRat x order + remainderRat x order ≤ b ∧
    l ≤ 1 / b ^ power ∧ 1 / a ^ power ≤ u

def PolynomialCheck (lo hi L U : ℚ) : Prop :=
  0 ≤ lo ∧ hi ≤ 1 ∧
    L ≤ lo - 2*hi^4 + lo^9 + lo^25 - 2*hi^36 - 5*hi^64 ∧
    hi - 2*lo^4 + hi^9 + hi^25 - 2*lo^36 + 6*hi^64 ≤ U

def MomentCheck (lo hi L U : ℚ) : Prop :=
  0 ≤ lo ∧ hi ≤ 1 ∧
    L ≤ lo - 8*hi^4 + 9*lo^9 + 25*lo^25 - 72*hi^36 - 508*hi^64 ∧
    hi - 8*lo^4 + 9*hi^9 + 25*hi^25 - 72*lo^36 + 2464*hi^64 ≤ U

def ProductCheck (a b c d L U : ℚ) : Prop :=
  L ≤ a*c ∧ L ≤ a*d ∧ L ≤ b*c ∧ L ≤ b*d ∧
    a*c ≤ U ∧ a*d ≤ U ∧ b*c ≤ U ∧ b*d ≤ U

structure ThetaRow where
  left : ℚ
  right : ℚ
  iArgL : ℚ
  iArgU : ℚ
  iL : ℚ
  iU : ℚ
  alphaL : ℚ
  alphaU : ℚ
  rArgL : ℚ
  rArgU : ℚ
  rL : ℚ
  rU : ℚ
  pL : ℚ
  pU : ℚ
  mL : ℚ
  mU : ℚ
  prefArgL : ℚ
  prefArgU : ℚ
  prefL : ℚ
  prefU : ℚ
  amL : ℚ
  amU : ℚ
  insideL : ℚ
  insideU : ℚ
  valueL : ℚ
  valueU : ℚ
  derivL : ℚ
  derivU : ℚ

def piLowerQ : ℚ := 314159265358979 / 100000000000000

def piUpperQ : ℚ := 314159265358980 / 100000000000000

def DirectCheck (q : ThetaRow) : Prop :=
  q.left ≤ q.right ∧
  q.iArgL = 2*q.left ∧ q.iArgU = 2*q.right ∧
  q.rArgL = -q.alphaU ∧ q.rArgU = -q.alphaL ∧
  ProductCheck piLowerQ piUpperQ q.iL q.iU q.alphaL q.alphaU ∧
  PolynomialCheck q.rL q.rU q.pL q.pU ∧
  MomentCheck q.rL q.rU q.mL q.mU ∧
  ProductCheck q.alphaL q.alphaU q.mL q.mU q.amL q.amU ∧
  q.valueL ≤ 2*q.pL ∧ 2*q.pU ≤ q.valueU ∧
  q.derivL ≤ -4*q.amU ∧ -4*q.amL ≤ q.derivU

def ReflectedCheck (q : ThetaRow) : Prop :=
  q.left ≤ q.right ∧
  q.iArgL = -2*q.right ∧ q.iArgU = -2*q.left ∧
  q.rArgL = -q.alphaU ∧ q.rArgU = -q.alphaL ∧
  q.prefArgL = -q.right ∧ q.prefArgU = -q.left ∧
  ProductCheck piLowerQ piUpperQ q.iL q.iU (16*q.alphaL) (16*q.alphaU) ∧
  PolynomialCheck q.rL q.rU q.pL q.pU ∧
  MomentCheck q.rL q.rU q.mL q.mU ∧
  ProductCheck q.alphaL q.alphaU q.mL q.mU q.amL q.amU ∧
  q.insideL ≤ -q.pU+2*q.amL ∧ -q.pL+2*q.amU ≤ q.insideU ∧
  ProductCheck q.prefL q.prefU q.pL q.pU q.valueL q.valueU ∧
  ProductCheck q.prefL q.prefU q.insideL q.insideU q.derivL q.derivU


/-- A uniform rational exponential certificate. Modes: 0 zero; 1 positive
Taylor; 2 negative Taylor; 3 negative integer cutoff. Other modes are invalid. -/
structure ExpRow where
  mode : ℕ
  argument : ℚ
  lower : ℚ
  upper : ℚ
  smallArg : ℚ
  baseL : ℚ
  baseU : ℚ
  power : ℕ
  order : ℕ
  natBound : ℕ

def ExpRow.Valid (q : ExpRow) : Prop :=
  if q.mode = 0 then q.argument = 0 ∧ q.lower ≤ 1 ∧ 1 ≤ q.upper
  else if q.mode = 1 then
    PositiveExpCheck q.argument q.smallArg q.baseL q.baseU q.lower q.upper q.power q.order
  else if q.mode = 2 then
    NegativeExpCheck (-q.argument) q.smallArg q.baseL q.baseU q.lower q.upper q.power q.order
  else if q.mode = 3 then
    (q.natBound : ℚ) ≤ -q.argument ∧ q.lower ≤ 0 ∧ 1/(2 : ℚ)^q.natBound ≤ q.upper
  else False

def ThetaRow.Valid (q : ThetaRow) (reflected : Bool) : Prop :=
  if reflected then ReflectedCheck q else DirectCheck q

instance (t x a b l u : ℚ) (power order : ℕ) :
    Decidable (PositiveExpCheck t x a b l u power order) := by
  unfold PositiveExpCheck
  infer_instance

instance (t x a b l u : ℚ) (power order : ℕ) :
    Decidable (NegativeExpCheck t x a b l u power order) := by
  unfold NegativeExpCheck
  infer_instance

instance (lo hi L U : ℚ) : Decidable (PolynomialCheck lo hi L U) := by
  unfold PolynomialCheck
  infer_instance

instance (lo hi L U : ℚ) : Decidable (MomentCheck lo hi L U) := by
  unfold MomentCheck
  infer_instance

instance (a b c d L U : ℚ) : Decidable (ProductCheck a b c d L U) := by
  unfold ProductCheck
  infer_instance

instance (q : ThetaRow) : Decidable (DirectCheck q) := by
  unfold DirectCheck
  infer_instance

instance (q : ThetaRow) : Decidable (ReflectedCheck q) := by
  unfold ReflectedCheck
  infer_instance

instance (q : ExpRow) : Decidable q.Valid := by
  unfold ExpRow.Valid
  infer_instance

instance (q : ThetaRow) (reflected : Bool) : Decidable (q.Valid reflected) := by
  unfold ThetaRow.Valid
  infer_instance

end MasulloRH.HeightTwoScalar


