-- Prove2me | Definitions.Def_Freiman_certDiagonal
-- name    : Freiman_certDiagonal
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:04:50.935339+00:00
-- url     : https://prove2.me/theorems/3b1880e6-1a7a-4127-968d-033f1b507011
-- title:
--   Freiman M2B: certDiagonal
-- statement:
--   Exact source model, finite certificate validator, or lossless data. Definitions only; no new axioms or theorem declarations.
-- source:
--   Freiman report (8 September 2026), M2B §§8–9 and complete middle-interval certificate appendix; m2b_readable_model.json, SHA256 a5ac6d3c8e0148e2e3137e8cfa09a2715de6a993dd6ab01eda4842a96bba4cdf.

import Definitions.Def_Freiman_certificates

namespace Freiman

def certDiagonalZero : CertField := ⟨0,0,0,0⟩
def certDiagonalPolynomial (a b c : CertField) : CertPoly22 := fun i j =>
  if i.val = 1 ∧ j.val = 0 then a else
  if i.val = 0 ∧ j.val = 1 then certFieldScale (-1) a else
  if i.val = 2 ∧ j.val = 0 then b else
  if i.val = 0 ∧ j.val = 2 then certFieldScale (-1) b else
  if i.val = 2 ∧ j.val = 1 then c else
  if i.val = 1 ∧ j.val = 2 then certFieldScale (-1) c else certDiagonalZero
def certDiagonalCorner (a b c : CertField) (r s : ℚ) : CertField :=
  certFieldAdd a (certFieldAdd (certFieldScale (r+s) b) (certFieldScale (r*s) c))
noncomputable def certDiagonalFactor (a b c : CertField) (r s : ℝ) : ℝ :=
  certFieldVal a + certFieldVal b * (r+s) + certFieldVal c * r*s
def certRectangleR (R : CertRectangle) (i : Fin 2) : ℚ := if i.val = 0 then R.r0 else R.r1
def certRectangleS (R : CertRectangle) (i : Fin 2) : ℚ := if i.val = 0 then R.s0 else R.s1

structure CertDiagonalData where
  lowerThreshold : CertThreshold
  upperThreshold : CertThreshold
  rectangle : CertRectangle
  positiveDirection : Bool
  a : CertField
  b : CertField
  c : CertField
  corners : Fin 2 → Fin 2 → CertField
  lowerBounds : Fin 2 → Fin 2 → ℚ

def certDiagonalDataValid (w : CertDiagonalData) : Prop :=
  certRectangleValid w.rectangle ∧ 0 ≤ w.rectangle.r0 ∧
  certThresholdDataValid w.lowerThreshold ∧ certThresholdDataValid w.upperThreshold ∧
  certCrossPolynomial w.lowerThreshold w.upperThreshold = certDiagonalPolynomial w.a w.b w.c ∧
  (∀ i j : Fin 2, w.corners i j = certFieldScale (if w.positiveDirection then 1 else -1)
    (certDiagonalCorner w.a w.b w.c (certRectangleR w.rectangle i) (certRectangleS w.rectangle j))) ∧
  ∀ i j : Fin 2, certCoefficientBoundValid (w.corners i j) (w.lowerBounds i j)
noncomputable def certDiagonalSide (w : CertDiagonalData) (r s : ℝ) : Prop :=
  if w.positiveDirection then s ≤ r else r ≤ s

end Freiman


