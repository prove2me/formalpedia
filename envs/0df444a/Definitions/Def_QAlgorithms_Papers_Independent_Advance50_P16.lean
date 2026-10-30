-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16
-- name    : QAlgorithms_Papers_Independent_Advance50_P16
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:26:11.391687+00:00
-- url     : https://prove2.me/theorems/6be9a183-150a-423b-bab2-35964463934c
-- title:
--   Definitions for Multiplicativity of completely bounded p-norms implies a new additivity result
-- statement:
--   The objects the formalized statements of *Multiplicativity of completely bounded p-norms implies a new additivity result* (arXiv:quant-ph/0506196) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteTracePower`: Finite ordinary trace power near one, PDF p.6. Unlike the frozen oscillator trace-power functional, this is a real trace on a finite matrix.
--   - `recip`: Reciprocal exponent, PDF pp.9–10: infinity has reciprocal zero.
--   - `outerSandwich`: Outer-factor multiplier in (3.2), PDF p.10. The frozen `sandwich` declarations act on different spaces; this applies A tensor I and B tensor I to a bipartite matrix.
--   - `infinityMixedSize`: (3.2), PDF p.10, in homogeneous unit-ball form. The extended supremum never assigns default zero to an unbounded set. It is finite for these finite matrices.
--   - `mixedSize`: (3.3), PDF p.10, including t=infinity as the genuine (3.2) endpoint. The factorization set contains A=B=I,Z=Y. All exponents used in statements are >=1.
--   - `mixedNorm`: Real-valued mixed norm (3.3), PDF p.10. Finite matrices and exponents >=1 make `mixedSize` finite; no unbounded CB supremum is converted here.
--   - `matrixMixedSize`: Matrix-level norm M_a(L_q(M_d;L_p(M_n))), source PDF pp.11,13–15. Concrete formula: Pisier, arXiv:math/9306206v1, Theorem 2(2), PDF pp.6–7. The amplification is first. Contract its indices with unit S_(2q) multipliers, then flatten the amplification and d indices into the outer q register. This is an actual formula, not an arbitrary norm constrained by the desired theorems.
--   - `tripleSize`: Iterated vector-valued norm via (3.3), PDF pp.10–11,17. The inner operator space's matrix norms are `matrixMixedSize`, rather than iterated partial traces. Thus arbitrary nonpositive triple matrices are covered.
--   - `amplifiedFlip`: Flip of the two inner factors, leaving the amplification fixed, Theorem 8, PDF p.15.
--   - `traceLast`: Partial trace of the last tensor factor in the intentional 1,3,2 order, (3.24), PDF p.17.
--   - `inducedSize`: Ordinary induced norm (2.1), PDF p.5, on its full complex unit ball.
--   - `positiveInducedSize`: Positive induced norm, PDF pp.5,11. This does not assume trace preservation.
--   - `amplificationSize`: Finite amplification norm in (3.4),(3.5), PDF p.10. Identical outer exponent t appears on both sides; it is not the ordinary Schatten q-to-p amplification.
--   - `positiveAmplificationSize`: Positive finite amplification in Theorem 12, PDF p.20.
--   - `cbSize`: Completely bounded norm, (3.5), PDF pp.9–10. Extended supremum over all positive ancillary dimensions; no maximizing dimension is built into the definition.
--   - `pureRatio`: Pure-input norm ratio (1.6), PDF p.4, with normalized vectors and reference isomorphic to the input. The denominator is strictly positive on these vectors.
--   - `cbOmega`: Omega_p of (1.6), PDF p.4; a norm-ratio supremum, distinct from the frozen `omega` vectors and numerical-range sets. Its unit sphere is compact for nonzero input. The finite-dimensional ratio is bounded, so the extended supremum is finite.
--   - `conditionalAt`: Conditional entropy at a pure input, (1.1),(2.9), PDF pp.3,7.
--   - `minCBEntropy`: Minimal CB entropy (1.1), PDF p.3. Used on CPT maps with nonzero input/output; then the set is nonempty and compact and the real infimum is finite and attained.
--   - `powerRatio`: The ratio differentiated in Lemma 1, PDF p.6.
--   - `uniformEntropyQuotient`: Uniform entropy-limit quotient and its extension at one, (2.6), PDF pp.6–7. The frozen oscillator entropy-increment quotient is a different function.
--   - `IsEBT`: EBT, PDF pp.24–25: CPT and separable outputs for every finite reference. Uses the accepted separable positive cone, equivalent to separable density at trace one.
--   - `AdmissibleDensity`: Support-compatible beta(X1), (6.8), PDF p.29. Singular B are permitted.
--   - `minimizerMatrix`: v(p,B), (6.6), PDF p.29, on its support-compatible domain.
--   - `minimizerObjective`: Extended minimization objective (6.8), PDF p.29: incompatible supports cost infinity, not the finite value returned by a zero pseudoinverse.
--   - `densityObjective`: Positive-density outerSandwich (3.22), PDF p.16, including the infinity endpoint.
--   - `positiveFactorSize`: Symmetric positive factorization objective, (3.19),(3.21), PDF p.16.
--   - `factorSize`: Extended factorization objective on all matrices, (3.19), PDF p.16.
--   - `multiplierSize`: Multiplier objective in (3.18), PDF p.16, using homogeneous unit balls.
--   - `positiveMultiplierSize`: Positive multiplier reduction of (3.18), PDF p.16.
--   - `variationalSize`: The inner supremum of (3.6), PDF p.11. B is restricted to invertible densities by its caller; A may be singular and Y need only be PSD.
--   - `dilationState`: R,A,E order in Lemma 4, PDF pp.8–9. U acts on A,E and the initial pure density on (R,A),E is explicitly reassociated before conjugation.
--   - `associateRAE`: Reassociation (R,A,E) to ((R,A),E) for tracing E, Lemma 4, PDF p.8.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, https://arxiv.org/abs/quant-ph/0506196v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Statements from Devetak–Junge–King–Ruskai, arXiv:quant-ph/0506196v2.
Entropy is in nats; all finite registers are nonempty in the theorem signatures.
The explicit mixed norms are (3.2),(3.3). Completely bounded norms use extended
suprema over every positive finite ancillary dimension, with t=min(q,p).
No claim about complete operator-space isometry is replaced by a scalar-norm claim.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology
open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Finite ordinary trace power near one, PDF p.6. Unlike the frozen oscillator
trace-power functional, this is a real trace on a finite matrix. -/
def finiteTracePower {I : Type} [Fintype I] (X : Mat I) (p : ℝ) : ℝ :=
  (supportPower X p).trace.re

/-- Reciprocal exponent, PDF pp.9–10: infinity has reciprocal zero. -/
def recip (p : ℝ≥0∞) : ℝ := (p⁻¹).toReal

/-- Outer-factor multiplier in (3.2), PDF p.10. The frozen `sandwich` declarations
act on different spaces; this applies A tensor I and B tensor I to a bipartite matrix. -/
def outerSandwich {D I : Type} [Fintype D] [Fintype I]
    (A B : Mat D) (Y : Mat (D × I)) : Mat (D × I) :=
  Matrix.kronecker A (1 : Mat I) * Y * Matrix.kronecker B (1 : Mat I)

/-- (3.2), PDF p.10, in homogeneous unit-ball form. The extended supremum
never assigns default zero to an unbounded set. It is finite for these finite matrices. -/
def infinityMixedSize {D I : Type} [Fintype D] [Fintype I]
    (p : ℝ≥0∞) (Y : Mat (D × I)) : ℝ≥0∞ :=
  ⨆ A : {A : Mat D // schattenNorm (2 * p) A ≤ 1},
    ⨆ B : {B : Mat D // schattenNorm (2 * p) B ≤ 1},
      ENNReal.ofReal (schattenNorm p (outerSandwich A.val B.val Y))

/-- (3.3), PDF p.10, including t=infinity as the genuine (3.2) endpoint.
The factorization set contains A=B=I,Z=Y. All exponents used in statements are >=1. -/
def mixedSize {D I : Type} [Fintype D] [Fintype I]
    (t p : ℝ≥0∞) (Y : Mat (D × I)) : ℝ≥0∞ :=
  if t = ⊤ then infinityMixedSize p Y else
    ⨅ A : Mat D, ⨅ B : Mat D,
      ⨅ Z : {Z : Mat (D × I) // Y = outerSandwich A B Z},
        ENNReal.ofReal (schattenNorm (2 * t) A * schattenNorm (2 * t) B) *
          infinityMixedSize p Z.val

/-- Real-valued mixed norm (3.3), PDF p.10. Finite matrices and exponents >=1
make `mixedSize` finite; no unbounded CB supremum is converted here. -/
def mixedNorm {D I : Type} [Fintype D] [Fintype I]
    (t p : ℝ≥0∞) (Y : Mat (D × I)) : ℝ := (mixedSize t p Y).toReal

/-- Matrix-level norm M_a(L_q(M_d;L_p(M_n))), source PDF pp.11,13–15.
Concrete formula: Pisier, arXiv:math/9306206v1, Theorem 2(2), PDF pp.6–7.
The amplification is first. Contract its indices with unit S_(2q) multipliers,
then flatten the amplification and d indices into the outer q register.
This is an actual formula, not an arbitrary norm constrained by the desired theorems. -/
def matrixMixedSize {A D I : Type} [Fintype A] [Fintype D] [Fintype I]
    (q p : ℝ≥0∞) (Y : Mat (A × (D × I))) : ℝ≥0∞ :=
  ⨆ L : {L : Mat A // schattenNorm (2*q) L ≤ 1},
    ⨆ R : {R : Mat A // schattenNorm (2*q) R ≤ 1},
      let Z := outerSandwich L.val R.val Y
      mixedSize q p (fun x y : (A × D) × I =>
        Z (x.1.1,(x.1.2,x.2)) (y.1.1,(y.1.2,y.2)))

/-- Iterated vector-valued norm via (3.3), PDF pp.10–11,17.
The inner operator space's matrix norms are `matrixMixedSize`, rather than
iterated partial traces. Thus arbitrary nonpositive triple matrices are covered. -/
def tripleSize {A D I : Type} [Fintype A] [Fintype D] [Fintype I]
    (t q p : ℝ≥0∞) (Y : Mat (A × (D × I))) : ℝ≥0∞ :=
  if t = ⊤ then matrixMixedSize q p Y else
    ⨅ L : Mat A, ⨅ R : Mat A,
      ⨅ Z : {Z : Mat (A × (D × I)) // Y = outerSandwich L R Z},
        ENNReal.ofReal (schattenNorm (2*t) L * schattenNorm (2*t) R) *
          matrixMixedSize q p Z.val

/-- Flip of the two inner factors, leaving the amplification fixed,
Theorem 8, PDF p.15. -/
def amplifiedFlip {A D I : Type} (Y : Mat (A × (D × I))) : Mat (A × (I × D)) :=
  fun x y => Y (x.1,(x.2.2,x.2.1)) (y.1,(y.2.2,y.2.1))

/-- Partial trace of the last tensor factor in the intentional 1,3,2 order,
(3.24), PDF p.17. -/
def traceLast {A D I : Type} [Fintype I] (Y : Mat (A × (D × I))) : Mat (A × D) :=
  fun x y => ∑ i, Y (x.1,(x.2,i)) (y.1,(y.2,i))

/-- Ordinary induced norm (2.1), PDF p.5, on its full complex unit ball. -/
def inducedSize {I J : Type} [Fintype I] [Fintype J]
    (q p : ℝ≥0∞) (Phi : Superop I J) : ℝ≥0∞ :=
  ⨆ X : {X : Mat I // schattenNorm q X ≤ 1}, ENNReal.ofReal (schattenNorm p (Phi X.val))

/-- Positive induced norm, PDF pp.5,11. This does not assume trace preservation. -/
def positiveInducedSize {I J : Type} [Fintype I] [Fintype J]
    (q p : ℝ≥0∞) (Phi : Superop I J) : ℝ≥0∞ :=
  ⨆ X : {X : Mat I // X.PosSemidef ∧ schattenNorm q X ≤ 1},
    ENNReal.ofReal (schattenNorm p (Phi X.val))

/-- Finite amplification norm in (3.4),(3.5), PDF p.10. Identical outer exponent t
appears on both sides; it is not the ordinary Schatten q-to-p amplification. -/
def amplificationSize {I J : Type} [Fintype I] [Fintype J]
    (d : ℕ) (t q p : ℝ≥0∞) (Phi : Superop I J) : ℝ≥0∞ :=
  ⨆ X : {X : Mat (Fin d × I) // mixedNorm t q X ≤ 1},
    ENNReal.ofReal (mixedNorm t p (idTensorSuperop Phi X.val))

/-- Positive finite amplification in Theorem 12, PDF p.20. -/
def positiveAmplificationSize {I J : Type} [Fintype I] [Fintype J]
    (d : ℕ) (t q p : ℝ≥0∞) (Phi : Superop I J) : ℝ≥0∞ :=
  ⨆ X : {X : Mat (Fin d × I) // X.PosSemidef ∧ mixedNorm t q X ≤ 1},
    ENNReal.ofReal (mixedNorm t p (idTensorSuperop Phi X.val))

/-- Completely bounded norm, (3.5), PDF pp.9–10. Extended supremum over all
positive ancillary dimensions; no maximizing dimension is built into the definition. -/
def cbSize {I J : Type} [Fintype I] [Fintype J]
    (q p : ℝ≥0∞) (Phi : Superop I J) : ℝ≥0∞ :=
  ⨆ d : {d : ℕ // 0 < d}, amplificationSize d.val (min q p) q p Phi

/-- Pure-input norm ratio (1.6), PDF p.4, with normalized vectors and reference
isomorphic to the input. The denominator is strictly positive on these vectors. -/
def pureRatio {I J : Type} [Fintype I] [Fintype J]
    (p : ℝ≥0∞) (Phi : Superop I J) (psi : EuclideanSpace ℂ (I × I)) : ℝ :=
  schattenNorm p (idTensorSuperop Phi (pureDensity psi)) /
    schattenNorm p (traceRight (pureDensity psi))

/-- Omega_p of (1.6), PDF p.4; a norm-ratio supremum, distinct from the frozen
`omega` vectors and numerical-range sets. Its unit sphere is compact for nonzero input.
The finite-dimensional ratio is bounded, so the extended supremum is finite. -/
def cbOmega {I J : Type} [Fintype I] [Fintype J]
    (p : ℝ≥0∞) (Phi : Superop I J) : ℝ :=
  (⨆ psi : {psi : EuclideanSpace ℂ (I × I) // ‖psi‖ = 1},
    ENNReal.ofReal (pureRatio p Phi psi.val)).toReal

/-- Conditional entropy at a pure input, (1.1),(2.9), PDF pp.3,7. -/
def conditionalAt {I J : Type} [Fintype I] [Fintype J]
    (Phi : Superop I J) (psi : EuclideanSpace ℂ (I × I)) : ℝ :=
  entropy (idTensorSuperop Phi (pureDensity psi)) - entropy (traceRight (pureDensity psi))

/-- Minimal CB entropy (1.1), PDF p.3. Used on CPT maps with nonzero input/output;
then the set is nonempty and compact and the real infimum is finite and attained. -/
def minCBEntropy {I J : Type} [Fintype I] [Fintype J] (Phi : Superop I J) : ℝ :=
  sInf {s : ℝ | ∃ psi : EuclideanSpace ℂ (I × I), ‖psi‖ = 1 ∧ s = conditionalAt Phi psi}

/-- The ratio differentiated in Lemma 1, PDF p.6. -/
def powerRatio {D I : Type} [Fintype D] [Fintype I]
    (X : Mat (D × I)) (p : ℝ) : ℝ := finiteTracePower X p / finiteTracePower (traceRight X) p

/-- Uniform entropy-limit quotient and its extension at one, (2.6), PDF pp.6–7.
The frozen oscillator entropy-increment quotient is a different function. -/
def uniformEntropyQuotient {D I : Type} [Fintype D] [Fintype I]
    (p : ℝ) (X : Mat (D × I)) : ℝ :=
  if p = 1 then entropy X - entropy (traceRight X) else (1 - powerRatio X p) / (p - 1)

/-- EBT, PDF pp.24–25: CPT and separable outputs for every finite reference.
Uses the accepted separable positive cone, equivalent to separable density at trace one. -/
def IsEBT {I J : Type} [Fintype I] [Fintype J] (Phi : Superop I J) : Prop :=
  IsChannel Phi ∧ ∀ d : ℕ, 0 < d → ∀ X : Mat (Fin d × I), IsDensityMatrix X →
    Entanglement.IsSeparablePositive (idTensorSuperop Phi X)

/-- Support-compatible beta(X1), (6.8), PDF p.29. Singular B are permitted. -/
def AdmissibleDensity {D I : Type} [Fintype D] [Fintype I]
    (X : Mat (D × I)) (B : Mat D) : Prop :=
  IsDensityMatrix B ∧ LinearMap.ker B.mulVecLin ≤ LinearMap.ker (traceRight X).mulVecLin

/-- v(p,B), (6.6), PDF p.29, on its support-compatible domain. -/
def minimizerMatrix {D I : Type} [Fintype D] [Fintype I]
    (p : ℝ) (X : Mat (D × I)) (B : Mat D) : Mat (D × I) :=
  supportPower X (1/2) * Matrix.kronecker (supportPower B (1/p-1)) (1 : Mat I) *
    supportPower X (1/2)

/-- Extended minimization objective (6.8), PDF p.29: incompatible supports cost infinity,
not the finite value returned by a zero pseudoinverse. -/
def minimizerObjective {D I : Type} [Fintype D] [Fintype I]
    (p : ℝ) (X : Mat (D × I)) (B : Mat D) : ℝ≥0∞ :=
  if AdmissibleDensity X B then ENNReal.ofReal (schattenNorm (ENNReal.ofReal p) (minimizerMatrix p X B))
  else ⊤

/-- Positive-density outerSandwich (3.22), PDF p.16, including the infinity endpoint. -/
def densityObjective {D I : Type} [Fintype D] [Fintype I]
    (p : ℝ≥0∞) (X : Mat (D × I)) (B : Mat D) : ℝ≥0∞ :=
  if AdmissibleDensity X B then ENNReal.ofReal
    (schattenNorm p (outerSandwich (supportPower B (-(1-recip p)/2))
      (supportPower B (-(1-recip p)/2)) X)) else ⊤

/-- Symmetric positive factorization objective, (3.19),(3.21), PDF p.16. -/
def positiveFactorSize {D I : Type} [Fintype D] [Fintype I]
    (q p r : ℝ≥0∞) (Y : Mat (D × I)) : ℝ≥0∞ :=
  ⨅ A : {A : Mat D // A.PosSemidef},
    ⨅ Z : {Z : Mat (D × I) // Z.PosSemidef ∧ Y = outerSandwich A.val A.val Z},
      ENNReal.ofReal (schattenNorm (2*r) A.val ^ 2 * schattenNorm p Z.val)

/-- Extended factorization objective on all matrices, (3.19), PDF p.16. -/
def factorSize {D I : Type} [Fintype D] [Fintype I]
    (p r : ℝ≥0∞) (Y : Mat (D × I)) : ℝ≥0∞ :=
  ⨅ A : Mat D, ⨅ B : Mat D, ⨅ Z : {Z : Mat (D × I) // Y = outerSandwich A B Z},
    ENNReal.ofReal (schattenNorm (2*r) A * schattenNorm (2*r) B * schattenNorm p Z.val)

/-- Multiplier objective in (3.18), PDF p.16, using homogeneous unit balls. -/
def multiplierSize {D I : Type} [Fintype D] [Fintype I]
    (q r : ℝ≥0∞) (Y : Mat (D × I)) : ℝ≥0∞ :=
  ⨆ A : {A : Mat D // schattenNorm (2*r) A ≤ 1},
    ⨆ B : {B : Mat D // schattenNorm (2*r) B ≤ 1},
      ENNReal.ofReal (schattenNorm q (outerSandwich A.val B.val Y))

/-- Positive multiplier reduction of (3.18), PDF p.16. -/
def positiveMultiplierSize {D I : Type} [Fintype D] [Fintype I]
    (q r : ℝ≥0∞) (Y : Mat (D × I)) : ℝ≥0∞ :=
  ⨆ A : {A : Mat D // A.PosSemidef ∧ schattenNorm (2*r) A ≤ 1},
    ENNReal.ofReal (schattenNorm q (outerSandwich A.val A.val Y))

/-- The inner supremum of (3.6), PDF p.11. B is restricted to invertible densities
by its caller; A may be singular and Y need only be PSD. -/
def variationalSize {D I : Type} [Fintype D] [Fintype I]
    (p : ℝ≥0∞) (Y : Mat (D × I)) (B : Mat D) : ℝ≥0∞ :=
  ⨆ A : {A : Mat D // IsDensityMatrix A},
    let L := supportPower A.val (recip p / 2) * supportPower B (-recip p / 2)
    let R := supportPower B (-recip p / 2) * supportPower A.val (recip p / 2)
    ENNReal.ofReal (schattenNorm p (outerSandwich L R Y))

/-- R,A,E order in Lemma 4, PDF pp.8–9. U acts on A,E and the initial
pure density on (R,A),E is explicitly reassociated before conjugation. -/
def dilationState {R A E : Type} [Fintype R] [Fintype A] [Fintype E]
    (U : Matrix.unitaryGroup (A × E) ℂ) (tau : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × A)) : Mat (R × (A × E)) :=
  let V := Matrix.kronecker (1 : Mat R) (U : Mat (A × E))
  let Q : Mat (R × (A × E)) := fun x y =>
    pureDensity psi (x.1,x.2.1) (y.1,y.2.1) * pureDensity tau x.2.2 y.2.2
  V * Q * Vᴴ

/-- Reassociation (R,A,E) to ((R,A),E) for tracing E, Lemma 4, PDF p.8. -/
def associateRAE {R A E : Type} (G : Mat (R × (A × E))) : Mat ((R × A) × E) :=
  fun x y => G (x.1.1,(x.1.2,x.2)) (y.1.1,(y.1.2,y.2))

/-! Sanity checks pin endpoints, tensor order, normalization and invalid-support behavior. -/

example : recip ⊤ = 0 := by simp [recip]

example {I : Type} [Fintype I] : entropy (0 : Mat I) = 0 := by simp [entropy]

example {D I : Type} [Fintype D] [Fintype I] (X : Mat (D × I)) :
    uniformEntropyQuotient 1 X = entropy X - entropy (traceRight X) := by simp [uniformEntropyQuotient]

example {D I : Type} [Fintype D] [Fintype I] (p : ℝ≥0∞) (X : Mat (D × I)) :
    mixedSize ⊤ p X = infinityMixedSize p X := by simp [mixedSize]

example {D I : Type} [Fintype D] [Fintype I] (X : Mat (D × I)) (B : Mat D)
    (h : ¬ AdmissibleDensity X B) (p : ℝ) : minimizerObjective p X B = ⊤ := by
  simp [minimizerObjective, h]

example {R A E : Type} (G : Mat (R × (A × E))) (r s : R) (a b : A) (e f : E) :
    associateRAE G ((r,a),e) ((s,b),f) = G (r,(a,e)) (s,(b,f)) := rfl

example {D I : Type} [Fintype D] [Fintype I] (Y : Mat (D × I)) :
    outerSandwich (1 : Mat D) (1 : Mat D) Y = Y := by
  simp [outerSandwich, Matrix.one_kronecker_one]

example {I J : Type} [Fintype I] : choi (fun _ : Mat I => (0 : Mat J)) = 0 := rfl

example {A D I : Type} (Y : Mat (A × (D × I))) :
    amplifiedFlip (amplifiedFlip Y) = Y := rfl

example {D I : Type} (Y : Mat (D × I)) :
    QAlgorithms.Papers.Independent.Dependency50.P19.flip
      (QAlgorithms.Papers.Independent.Dependency50.P19.flip Y) = Y := rfl

example {A D I : Type} [Fintype A] [Fintype D] [Fintype I]
    (q p : ℝ≥0∞) (Y : Mat (A × (D × I))) :
    tripleSize ⊤ q p Y = matrixMixedSize q p Y := by simp [tripleSize]

example {A D I : Type} [Fintype I] : traceLast (0 : Mat (A × (D × I))) = 0 := by
  ext x y
  simp [traceLast]

example {D I : Type} [Fintype D] [Fintype I] (X : Mat (D × I)) (B : Mat D)
    (h : ¬ AdmissibleDensity X B) (p : ℝ≥0∞) : densityObjective p X B = ⊤ := by
  simp [densityObjective, h]

end QAlgorithms.Papers.Independent.Advance50.P16


