-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P75
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P75
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:01:48.842199+00:00
-- url     : https://prove2.me/theorems/1024ebed-deb6-49a1-8660-4b2a35aae75a
-- title:
--   Definitions for Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States
-- statement:
--   The objects the formalized statements of *Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States* (arXiv:1210.4409) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `mapHilbertFactors`: PDF pp.1–2: bounded tensor maps on completed Hilbert tensor products. Generalizes accepted completedTensorAction to distinct codomains, extending along the canonical dense isometric completion embedding.
--   - `alice`: PDF pp.2–3: Alice's action on the physical tensor product.
--   - `bob`: PDF pp.2–3: Bob's action on the other physical tensor factor.
--   - `Dichotomic`: PDF pp.2,7: a bounded self-adjoint involution on the entire local space.
--   - `IsLocalHilbertUnitary`: PDF p.9, (35)–(37): a local unitary need not be Hermitian.
--   - `appendBasisKet`: PDF p.2, Fig.1, and p.10, Fig.2: append a computational ket. Output order: physical factor, then ancilla.
--   - `attachSchmidt`: PDF p.2, (1),(3): junk tensor a diagonal Schmidt target, in the fixed register order (H,Q_A),(K,Q_B). On a simple junk tensor h tensor k this is sum_i a_i (h tensor |i>) tensor (k tensor |i>). Continuity determines the action on arbitrary entangled junk. This is inverse register regrouping, without a phase or normalization change.
--   - `swapLocal`: PDF p.2, Fig.1: v maps to ((I+Z)v tensor |0> + X(I-Z)v tensor |1>)/2. No within-party anticommutation premise is built into the map.
--   - `transferError`: PDF p.2, (4): second on-state identity, lifted to separate tensor factors.
--   - `projectionWitness`: PDF p.9, (30): projection witness before normalization. On 0 <= theta <= pi/4 its denominator is strictly positive.
--   - `normalizedProjection`: PDF p.9, (30)–(32): explicit normalized junk witness. The robust theorem proves its pre-normalization vector is nonzero.
--   - `bellOperator`: PDF p.2, (5): the Bell operator, rather than its deficit.
--   - `bellValue`: PDF pp.1–2: physical expectation with conjugate-linear-first inner product. Hermiticity in the theorems makes this real part the actual real value.
--   - `ExtractsWithin`: PDF p.2, (1),(3): state extraction in Hilbert norm. Maps are complex-linear isometric embeddings, their tensor map is constructed, and junk is normalized but may be entangled. Zero tolerance means equality.
--   - `ProjectiveFamily`: PDF p.9, (33)–(34): complete pairwise orthogonal local projections.
--   - `quditLocal`: PDF pp.9–10, Fig.2, (33),(36),(37): the initialized local circuit action v maps to sum_i X(i)P(i)v tensor |i>. With omega=exp(2*pi*i/d) and F(j,k)=omega^(jk)/sqrt(d), F, controlled Z^k, inverse F records the projector index; controlled X(i) then rotates its physical component.
--   - `qubitCoefficients`: PDF pp.2–3: Schmidt coefficients, including the product endpoint.
--   - `schmidtTarget`: PDF pp.2–3,10: diagonal target as an actual completed tensor vector.
--   - `tiltParameter`: PDF pp.2–3, Theorem, corrected Schmidt parameter. Printed: tan theta = sqrt((4-alpha^2)/(2 alpha^2)). Changed: tan(2 theta) has that value in the interior. This alpha formula also handles theta=pi/4, alpha=0. It is forced by (4),(15),tan mu=sin(2 theta). The inconsistent independent p.6 alpha formula is not reused.
--   - `quantumMaximum`: PDF p.2, (5): maximal quantum Bell value.
--   - `extractionBudget`: PDF p.9, (29)–(32): conditional error budget, using cos theta rather than cos(2 theta) from unrelated earlier coefficient notation.
--   - `idealZ`: PDF p.2: accepted Pauli Z converted without changing its basis or action.
--   - `idealX`: PDF p.2: accepted Pauli X on the same qubit Hilbert space.
--   - `idealB0`: PDF p.6, (15), p.7: ideal B0 with mu=arctan(sin(2 theta)).
--   - `idealB1`: PDF p.6, (15), p.7: ideal B1 with the opposite X coefficient.
--   - `quditRatio`: PDF p.9, (35): finite amplitude ratios, with the identity base branch.
--   - `quditCoefficients`: PDF p.10, (38), corrected: square ratios in the normalization. Printed sqrt(1+sum tan(delta_i)) is incompatible with a unit output vector.
-- source:
--   Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States, arXiv:1210.4409v2, https://arxiv.org/abs/1210.4409v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

/-!
arXiv:1210.4409v2, Yang and Navascues, PDF pp.1–15.
Four state-extraction results; four defective or unpinned claims are deferred.
The independent-paper workflow permits reuse of the pinned accepted library:
HilbertTensor completes Mathlib's inner-product tensor product; tensorVector
is its canonical simple tensor. Physical spaces have no dimension bound.
The printed Theorem's Schmidt parameter and (38)'s normalization are corrected;
these corrections require independent moderation. See MODERATION_NOTES.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P75

universe u v w x

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)
open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

/-- PDF pp.1–2: bounded tensor maps on completed Hilbert tensor products.
Generalizes accepted completedTensorAction to distinct codomains, extending
along the canonical dense isometric completion embedding. -/
def mapHilbertFactors {H : Type u} {K : Type v} {L : Type w} {M : Type x}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (A : H →L[ℂ] L) (B : K →L[ℂ] M) :
    HilbertTensor H K →L[ℂ] HilbertTensor L M :=
  ((UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := TensorProduct ℂ L M)).comp
    (TensorProduct.mapL A B)).extend
      (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := TensorProduct ℂ H K))

section LocalDefinitions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- PDF pp.2–3: Alice's action on the physical tensor product. -/
def alice (A : H →L[ℂ] H) : HilbertTensor H K →L[ℂ] HilbertTensor H K :=
  mapHilbertFactors A (ContinuousLinearMap.id ℂ K)

/-- PDF pp.2–3: Bob's action on the other physical tensor factor. -/
def bob (B : K →L[ℂ] K) : HilbertTensor H K →L[ℂ] HilbertTensor H K :=
  mapHilbertFactors (ContinuousLinearMap.id ℂ H) B

/-- PDF pp.2,7: a bounded self-adjoint involution on the entire local space. -/
def Dichotomic (A : H →L[ℂ] H) : Prop :=
  A.adjoint = A ∧ A * A = 1

/-- PDF p.9, (35)–(37): a local unitary need not be Hermitian. -/
def IsLocalHilbertUnitary (A : H →L[ℂ] H) : Prop :=
  A.adjoint * A = 1 ∧ A * A.adjoint = 1

/-- PDF p.2, Fig.1, and p.10, Fig.2: append a computational ket.
Output order: physical factor, then ancilla. -/
def appendBasisKet {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    H →L[ℂ] HilbertTensor H (EuclideanSpace ℂ ι) :=
  (UniformSpace.Completion.toComplL
    (𝕜 := ℂ) (E := TensorProduct ℂ H (EuclideanSpace ℂ ι))).comp
      ((TensorProduct.mkL ℂ H (EuclideanSpace ℂ ι)).flip (QAlgorithms.ket i))

/-- PDF p.2, (1),(3): junk tensor a diagonal Schmidt target, in the fixed
register order (H,Q_A),(K,Q_B). On a simple junk tensor h tensor k this is
sum_i a_i (h tensor |i>) tensor (k tensor |i>). Continuity determines the
action on arbitrary entangled junk. This is inverse register regrouping,
without a phase or normalization change. -/
def attachSchmidt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (junk : HilbertTensor H K) :
    HilbertTensor (HilbertTensor H (EuclideanSpace ℂ ι))
      (HilbertTensor K (EuclideanSpace ℂ ι)) :=
  ∑ i, a i • mapHilbertFactors (appendBasisKet (H := H) i) (appendBasisKet (H := K) i) junk

/-- PDF p.2, Fig.1: v maps to
((I+Z)v tensor |0> + X(I-Z)v tensor |1>)/2.
No within-party anticommutation premise is built into the map. -/
def swapLocal (X Z : H →L[ℂ] H) :
    H →L[ℂ] HilbertTensor H (EuclideanSpace ℂ Bool) :=
  (1 / 2 : ℂ) • ((appendBasisKet false).comp (1 + Z) +
    (appendBasisKet true).comp (X * (1 - Z)))

/-- PDF p.2, (4): second on-state identity, lifted to separate tensor factors. -/
def transferError (theta : ℝ) (XA ZA : H →L[ℂ] H) (XB ZB : K →L[ℂ] K)
    (psi : HilbertTensor H K) : HilbertTensor H K :=
  (Real.sin theta : ℂ) • alice XA (bob (1 + ZB) psi) -
    (Real.cos theta : ℂ) • bob XB (alice (1 - ZA) psi)

/-- PDF p.9, (30): projection witness before normalization.
On 0 <= theta <= pi/4 its denominator is strictly positive. -/
def projectionWitness (theta : ℝ) (ZA : H →L[ℂ] H)
    (psi : HilbertTensor H K) : HilbertTensor H K :=
  (((2 * Real.cos theta)⁻¹ : ℝ) : ℂ) • alice (1 + ZA) psi

/-- PDF p.9, (30)–(32): explicit normalized junk witness.
The robust theorem proves its pre-normalization vector is nonzero. -/
def normalizedProjection (theta : ℝ) (ZA : H →L[ℂ] H)
    (psi : HilbertTensor H K) : HilbertTensor H K :=
  let q := projectionWitness theta ZA psi
  ((‖q‖⁻¹ : ℝ) : ℂ) • q

/-- PDF p.2, (5): the Bell operator, rather than its deficit. -/
def bellOperator (alpha : ℝ) (A0 A1 : H →L[ℂ] H) (B0 B1 : K →L[ℂ] K) :
    HilbertTensor H K →L[ℂ] HilbertTensor H K :=
  (alpha : ℂ) • alice A0 + mapHilbertFactors A0 (B0 + B1) + mapHilbertFactors A1 (B0 - B1)

/-- PDF pp.1–2: physical expectation with conjugate-linear-first inner product.
Hermiticity in the theorems makes this real part the actual real value. -/
def bellValue (alpha : ℝ) (A0 A1 : H →L[ℂ] H) (B0 B1 : K →L[ℂ] K)
    (psi : HilbertTensor H K) : ℝ :=
  (inner ℂ psi (bellOperator alpha A0 A1 B0 B1 psi)).re

/-- PDF p.2, (1),(3): state extraction in Hilbert norm.
Maps are complex-linear isometric embeddings, their tensor map is constructed,
and junk is normalized but may be entangled. Zero tolerance means equality. -/
def ExtractsWithin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (psi : HilbertTensor H K) (error : ℝ) : Prop :=
  ∃ (FA : H →L[ℂ] HilbertTensor H (EuclideanSpace ℂ ι))
    (FB : K →L[ℂ] HilbertTensor K (EuclideanSpace ℂ ι))
    (junk : HilbertTensor H K),
    Isometry FA ∧ Isometry FB ∧ ‖junk‖ = 1 ∧
      ‖mapHilbertFactors FA FB psi - attachSchmidt a junk‖ ≤ error

/-- PDF p.9, (33)–(34): complete pairwise orthogonal local projections. -/
def ProjectiveFamily {d : ℕ} (P : Fin d → H →L[ℂ] H) : Prop :=
  (∀ i, (P i).adjoint = P i ∧ P i * P i = P i) ∧
    (∀ i j, i ≠ j → P i * P j = 0) ∧ (∑ i, P i) = 1

/-- PDF pp.9–10, Fig.2, (33),(36),(37): the initialized local circuit action
v maps to sum_i X(i)P(i)v tensor |i>. With omega=exp(2*pi*i/d) and
F(j,k)=omega^(jk)/sqrt(d), F, controlled Z^k, inverse F records the projector
index; controlled X(i) then rotates its physical component. -/
def quditLocal {d : ℕ} (P X : Fin d → H →L[ℂ] H) :
    H →L[ℂ] HilbertTensor H (EuclideanSpace ℂ (Fin d)) :=
  ∑ i, (appendBasisKet i).comp (X i * P i)

/-- Sanity: bounded tensor maps take the zero vector to zero. -/
example (A : H →L[ℂ] H) (B : K →L[ℂ] K) : mapHilbertFactors A B 0 = 0 := map_zero _

/-- Sanity: the local extraction has the required zero-vector behavior. -/
example (X Z : H →L[ℂ] H) : swapLocal X Z 0 = 0 := map_zero _

/-- Sanity: the identity is a permitted dichotomic observable and unitary. -/
example : Dichotomic (1 : H →L[ℂ] H) ∧ IsLocalHilbertUnitary (1 : H →L[ℂ] H) := by
  simp [Dichotomic, IsLocalHilbertUnitary, ContinuousLinearMap.adjoint_one]

end LocalDefinitions

/-- PDF pp.2–3: Schmidt coefficients, including the product endpoint. -/
def qubitCoefficients (theta : ℝ) (b : Bool) : ℂ :=
  if b then (Real.sin theta : ℂ) else (Real.cos theta : ℂ)

/-- PDF pp.2–3,10: diagonal target as an actual completed tensor vector. -/
def schmidtTarget {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℂ) :
    HilbertTensor (EuclideanSpace ℂ ι) (EuclideanSpace ℂ ι) :=
  ∑ i, a i • tensorVector (QAlgorithms.ket i) (QAlgorithms.ket i)

/-- PDF pp.2–3, Theorem, corrected Schmidt parameter.
Printed: tan theta = sqrt((4-alpha^2)/(2 alpha^2)).
Changed: tan(2 theta) has that value in the interior. This alpha formula also
handles theta=pi/4, alpha=0. It is forced by (4),(15),tan mu=sin(2 theta).
The inconsistent independent p.6 alpha formula is not reused. -/
def tiltParameter (theta : ℝ) : ℝ :=
  2 * Real.cos (2 * theta) / Real.sqrt (1 + Real.sin (2 * theta) ^ 2)

/-- PDF p.2, (5): maximal quantum Bell value. -/
def quantumMaximum (alpha : ℝ) : ℝ := Real.sqrt (8 + 2 * alpha ^ 2)

/-- PDF p.9, (29)–(32): conditional error budget, using cos theta rather
than cos(2 theta) from unrelated earlier coefficient notation. -/
def extractionBudget (theta epsilon epsilon2 : ℝ) : ℝ :=
  4 * epsilon + epsilon2 / (2 * |Real.cos theta|)

/-- PDF p.2: accepted Pauli Z converted without changing its basis or action. -/
def idealZ : EuclideanSpace ℂ Bool →L[ℂ] EuclideanSpace ℂ Bool :=
  (Matrix.toEuclideanLin QAlgorithms.pauliZ).toContinuousLinearMap

/-- PDF p.2: accepted Pauli X on the same qubit Hilbert space. -/
def idealX : EuclideanSpace ℂ Bool →L[ℂ] EuclideanSpace ℂ Bool :=
  (Matrix.toEuclideanLin QAlgorithms.pauliX).toContinuousLinearMap

/-- PDF p.6, (15), p.7: ideal B0 with mu=arctan(sin(2 theta)). -/
def idealB0 (theta : ℝ) : EuclideanSpace ℂ Bool →L[ℂ] EuclideanSpace ℂ Bool :=
  (Real.cos (Real.arctan (Real.sin (2 * theta))) : ℂ) • idealZ +
    (Real.sin (Real.arctan (Real.sin (2 * theta))) : ℂ) • idealX

/-- PDF p.6, (15), p.7: ideal B1 with the opposite X coefficient. -/
def idealB1 (theta : ℝ) : EuclideanSpace ℂ Bool →L[ℂ] EuclideanSpace ℂ Bool :=
  (Real.cos (Real.arctan (Real.sin (2 * theta))) : ℂ) • idealZ -
    (Real.sin (Real.arctan (Real.sin (2 * theta))) : ℂ) • idealX

/-- PDF p.9, (35): finite amplitude ratios, with the identity base branch. -/
def quditRatio {d : ℕ} (delta : Fin d → ℝ) (i : Fin d) : ℝ :=
  if i.val = 0 then 1 else Real.tan (delta i)

/-- PDF p.10, (38), corrected: square ratios in the normalization.
Printed sqrt(1+sum tan(delta_i)) is incompatible with a unit output vector. -/
def quditCoefficients {d : ℕ} (delta : Fin d → ℝ) (i : Fin d) : ℂ :=
  (quditRatio delta i / Real.sqrt (∑ j, quditRatio delta j ^ 2) : ℝ)

/-- Sanity: the two-qubit product boundary is exactly |00>. -/
example : qubitCoefficients 0 false = 1 ∧ qubitCoefficients 0 true = 0 := by
  simp [qubitCoefficients]

/-- Sanity: corrected Bell parameter at the product boundary is 2. -/
example : tiltParameter 0 = 2 := by simp [tiltParameter]

/-- Sanity: base ratio is 1 regardless of the unused zeroth angle. -/
example (delta : Fin 2 → ℝ) : quditRatio delta 0 = 1 := by simp [quditRatio]

/-- Sanity: zero non-base ratios are allowed, without hidden full rank. -/
example : quditRatio (fun _ : Fin 2 => 0) 1 = 0 := by simp [quditRatio]

section ExtractionStatements

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

end ExtractionStatements

end QAlgorithms.Papers.Independent.Intakethird100.P75


