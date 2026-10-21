-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P42
-- name    : QAlgorithms_Papers_Independent_Claimed50_P42
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:03:37.065312+00:00
-- url     : https://prove2.me/theorems/782106b2-fc09-4d52-87f4-7d93f1782dab
-- title:
--   Definitions for Gaussian Entanglement of Formation
-- statement:
--   The objects the formalized statements of *Gaussian Entanglement of Formation* (arXiv:quant-ph/0306177) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pureGaussianCM`: PDF p.3, Eq.(16): grouped coordinates `(Q_1,...,Q_n,P_1,...,P_n)`. The inverse is used in the theorem only for symmetric positive definite X.
--   - `PrecisionParameters`: PDF p.7, Lemma 3: positive definite *precision* B and mean b. The subtype inherits the ordinary Borel sigma algebra from its finite real matrix/vector parameter space. No covariance matrix is mistaken for B.
--   - `precisionGaussianDensity`: PDF p.7, Eq.(A1): normalized classical Gaussian density for positive precision A. Here det A > 0, so sqrt(det A) is the printed |A|^(1/2). The exponent -n/2 is real, rather than truncated natural-number division.
--   - `IsPrecisionGaussianMixture`: PDF p.7, Eq.(A2): equality at every x of the actual Gaussian densities. Measurability and integrability explicitly impose the source's convention of genuine probability integrals; a divergent totalized real integral cannot satisfy this decomposition predicate. Probability normalization is imposed separately in the theorem.
-- source:
--   Gaussian Entanglement of Formation, arXiv:quant-ph/0306177v2, https://arxiv.org/abs/quant-ph/0306177v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
# Gaussian entanglement of formation: independent covariance and classical lemmas

Source: Wolf et al., arXiv:quant-ph/0306177v2, PDF pp.3–4 and 7–8.
Only Lemmas 1 and 3 are stated here. Other planned nodes are explicitly accounted
for in the unit HARD.md and GAPS.json. In particular no covariance optimization
is used as a definition of the probability-ensemble Gaussian convex roof.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P42

open MeasureTheory
open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase sigma pureCovariance)

/-- PDF p.3, Eq.(16): grouped coordinates `(Q_1,...,Q_n,P_1,...,P_n)`.
The inverse is used in the theorem only for symmetric positive definite X. -/
def pureGaussianCM {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Phase n) (Phase n) ℝ :=
  Matrix.fromBlocks X (X * Y) (Y * X) (Y * X * Y + X⁻¹)

example {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    pureGaussianCM X 0 = Matrix.fromBlocks X 0 0 X⁻¹ := by
  simp [pureGaussianCM]

/-- PDF p.7, Lemma 3: positive definite *precision* B and mean b.
The subtype inherits the ordinary Borel sigma algebra from its finite real
matrix/vector parameter space. No covariance matrix is mistaken for B. -/
abbrev PrecisionParameters (n : ℕ) :=
  {p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) // p.1.PosDef}

/-- PDF p.7, Lemma 3: the ordinary Borel sigma algebra on the positive
precision/mean parameter space, with its inherited finite-dimensional topology. -/
instance precisionParametersMeasurableSpace (n : ℕ) :
    MeasurableSpace (PrecisionParameters n) :=
  borel (PrecisionParameters n)

example {n : ℕ} (p : PrecisionParameters n) : p.val.1.PosDef := by
  exact p.property

/-- PDF p.7, Eq.(A1): normalized classical Gaussian density for positive
precision A. Here det A > 0, so sqrt(det A) is the printed |A|^(1/2).
The exponent -n/2 is real, rather than truncated natural-number division. -/
def precisionGaussianDensity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (a x : Fin n → ℝ) : ℝ :=
  Real.sqrt A.det * Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) *
    Real.exp (-dotProduct (x - a) (A.mulVec (x - a)) / 2)

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    precisionGaussianDensity A a a =
      Real.sqrt A.det * Real.rpow (2 * Real.pi) (-(n : ℝ) / 2) := by
  simp [precisionGaussianDensity]

/-- PDF p.7, Eq.(A2): equality at every x of the actual Gaussian densities.
Measurability and integrability explicitly impose the source's convention of
genuine probability integrals; a divergent totalized real integral cannot
satisfy this decomposition predicate. Probability normalization is imposed
separately in the theorem. -/
def IsPrecisionGaussianMixture {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (mu : Measure (PrecisionParameters n)) : Prop :=
  ∀ x : Fin n → ℝ,
    Measurable (fun p : PrecisionParameters n =>
      precisionGaussianDensity p.val.1 p.val.2 x) ∧
    Integrable (fun p : PrecisionParameters n =>
      precisionGaussianDensity p.val.1 p.val.2 x) mu ∧
    precisionGaussianDensity A 0 x =
      ∫ p : PrecisionParameters n,
        precisionGaussianDensity p.val.1 p.val.2 x ∂mu

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (mu : Measure (PrecisionParameters n)) (h : IsPrecisionGaussianMixture A mu)
    (x : Fin n → ℝ) :
    Integrable (fun p : PrecisionParameters n =>
      precisionGaussianDensity p.val.1 p.val.2 x) mu := by
  exact (h x).2.1

end QAlgorithms.Papers.Independent.Claimed50.P42


