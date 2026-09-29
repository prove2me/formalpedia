-- Prove2me | Definitions.Def_Freiman_certificates
-- name    : Freiman_certificates
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:47:19.707446+00:00
-- url     : https://prove2.me/theorems/fb2ac2b3-613e-4918-9f0a-dd330a6ac124
-- title:
--   Exact field, Bernstein and exclusion certificate records
-- statement:
--   Exact rational four-component field values, the two-parameter rational thresholds and strict/weak q-bounds, rectangular 3×3 Bernstein data, and a finite rational witness validator in the format of the report appendices.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), certificate guide; app:all-suffix-histories and app:h5-original, exact notation and sign rule.

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order

open scoped BigOperators

namespace Freiman

structure CertField where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

noncomputable def certFieldVal (z : CertField) : ℝ :=
  z.a + z.b * Real.sqrt 3 + z.c * Real.sqrt 7 + z.d * Real.sqrt 21

def certFieldAdd (x y : CertField) : CertField :=
  ⟨x.a+y.a, x.b+y.b, x.c+y.c, x.d+y.d⟩
def certFieldSub (x y : CertField) : CertField :=
  ⟨x.a-y.a, x.b-y.b, x.c-y.c, x.d-y.d⟩
def certFieldScale (q : ℚ) (x : CertField) : CertField :=
  ⟨q*x.a, q*x.b, q*x.c, q*x.d⟩
def certFieldMul (x y : CertField) : CertField :=
  ⟨x.a*y.a+3*x.b*y.b+7*x.c*y.c+21*x.d*y.d,
   x.a*y.b+x.b*y.a+7*x.c*y.d+7*x.d*y.c,
   x.a*y.c+x.c*y.a+3*x.b*y.d+3*x.d*y.b,
   x.a*y.d+x.d*y.a+x.b*y.c+x.c*y.b⟩

def certSqrt3Lower : ℚ := 1732050807568877293527446341505 / 10^30
def certSqrt3Upper : ℚ := 1732050807568877293527446341506 / 10^30
def certSqrt7Lower : ℚ := 2645751311064590590501615753639 / 10^30
def certSqrt7Upper : ℚ := 2645751311064590590501615753640 / 10^30
def certSqrt21Lower : ℚ := 4582575694955840006588047193728 / 10^30
def certSqrt21Upper : ℚ := 4582575694955840006588047193729 / 10^30

def certDirectedTerm (q lo hi : ℚ) : ℚ := q * (if 0 ≤ q then lo else hi)
def certFieldLower (z : CertField) : ℚ :=
  z.a + certDirectedTerm z.b certSqrt3Lower certSqrt3Upper +
    certDirectedTerm z.c certSqrt7Lower certSqrt7Upper +
    certDirectedTerm z.d certSqrt21Lower certSqrt21Upper

structure CertThreshold where
  c : CertField
  x0 : CertField
  x1 : CertField
  y0 : CertField
  y1 : CertField
  deriving DecidableEq

structure CertBound where
  lower : Bool
  strict : Bool
  threshold : CertThreshold
  deriving DecidableEq

structure CertRectangle where
  r0 : ℚ
  r1 : ℚ
  s0 : ℚ
  s1 : ℚ
  deriving DecidableEq

def certRectangleValid (R : CertRectangle) : Prop := R.r0 < R.r1 ∧ R.s0 < R.s1
def certRectangleMem (R : CertRectangle) (r s : ℝ) : Prop :=
  (R.r0 : ℝ) ≤ r ∧ r ≤ R.r1 ∧ (R.s0 : ℝ) ≤ s ∧ s ≤ R.s1

noncomputable def certThresholdDen (t : CertThreshold) (r : ℝ) : ℝ :=
  (1+r*certFieldVal t.x0)*(1+r*certFieldVal t.x1)
noncomputable def certThresholdNum (t : CertThreshold) (s : ℝ) : ℝ :=
  certFieldVal t.c*(1+s*certFieldVal t.y0)*(1+s*certFieldVal t.y1)
noncomputable def certThresholdVal (t : CertThreshold) (r s : ℝ) : ℝ :=
  certThresholdNum t s / certThresholdDen t r
noncomputable def certBoundHolds (b : CertBound) (r s q : ℝ) : Prop :=
  if b.lower then
    if b.strict then certThresholdVal b.threshold r s < q
    else certThresholdVal b.threshold r s ≤ q
  else
    if b.strict then q < certThresholdVal b.threshold r s
    else q ≤ certThresholdVal b.threshold r s

abbrev CertPoly22 := Fin 3 → Fin 3 → CertField

def certProductCoefficients (x y : CertField) (i : Fin 3) : CertField :=
  if i = 0 then ⟨1,0,0,0⟩ else if i = 1 then certFieldAdd x y else certFieldMul x y

def certCrossPolynomial (l u : CertThreshold) : CertPoly22 := fun i j =>
  certFieldSub
    (certFieldMul l.c (certFieldMul (certProductCoefficients u.x0 u.x1 i)
      (certProductCoefficients l.y0 l.y1 j)))
    (certFieldMul u.c (certFieldMul (certProductCoefficients l.x0 l.x1 i)
      (certProductCoefficients u.y0 u.y1 j)))

noncomputable def certPolyEval (P : CertPoly22) (r s : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, certFieldVal (P i j) * r ^ i.val * s ^ j.val

def certQuadBlend (a b : ℚ) (v : Fin 3 → CertField) (i : Fin 3) : CertField :=
  let e := if i = 0 then a else if i = 1 then (a+b)/2 else b
  let f := if i = 0 then a^2 else if i = 1 then a*b else b^2
  certFieldAdd (v 0) (certFieldAdd (certFieldScale e (v 1)) (certFieldScale f (v 2)))

def certBernsteinCoefficients (P : CertPoly22) (R : CertRectangle) : CertPoly22 :=
  fun i j => certQuadBlend R.r0 R.r1 (fun k => certQuadBlend R.s0 R.s1 (P k) j) i

noncomputable def certBernsteinBasis (i : Fin 3) (t : ℝ) : ℝ :=
  if i = 0 then (1-t)^2 else if i = 1 then 2*t*(1-t) else t^2
noncomputable def certBernsteinWeight (R : CertRectangle) (r s : ℝ)
    (i j : Fin 3) : ℝ :=
  certBernsteinBasis i ((r-R.r0)/(R.r1-R.r0)) *
    certBernsteinBasis j ((s-R.s0)/(R.s1-R.s0))
noncomputable def certBernsteinEval (C : CertPoly22) (R : CertRectangle) (r s : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, certFieldVal (C i j) * certBernsteinWeight R r s i j

structure CertWitness where
  lowerBound : CertBound
  upperBound : CertBound
  rectangle : CertRectangle
  coefficients : CertPoly22
  lowerBounds : Fin 3 → Fin 3 → ℚ

def certThresholdDataValid (t : CertThreshold) : Prop :=
  0 ≤ certFieldLower t.x0 ∧ 0 ≤ certFieldLower t.x1

def certCoefficientBoundValid (z : CertField) (q : ℚ) : Prop :=
  0 ≤ q ∧ if q = 0 then 0 ≤ certFieldLower z else q < certFieldLower z

def certWitnessValid (w : CertWitness) : Prop :=
  w.lowerBound.lower = true ∧ w.upperBound.lower = false ∧
  certRectangleValid w.rectangle ∧ 0 ≤ w.rectangle.r0 ∧
  certThresholdDataValid w.lowerBound.threshold ∧
  certThresholdDataValid w.upperBound.threshold ∧
  w.coefficients = certBernsteinCoefficients
    (certCrossPolynomial w.lowerBound.threshold w.upperBound.threshold) w.rectangle ∧
  (∀ i j : Fin 3, certCoefficientBoundValid (w.coefficients i j) (w.lowerBounds i j)) ∧
  ((∀ i j : Fin 3, 0 < w.lowerBounds i j) ∨
    w.lowerBound.strict = true ∨ w.upperBound.strict = true)

end Freiman


