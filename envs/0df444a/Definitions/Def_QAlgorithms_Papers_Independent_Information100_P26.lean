-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
-- name    : QAlgorithms_Papers_Independent_Information100_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T10:16:14.658777+00:00
-- url     : https://prove2.me/theorems/b47b52e9-319b-432b-bb11-4850fc7f11f0
-- title:
--   Definitions for A complete characterization of eventually entanglement breaking unital quantum channels
-- statement:
--   The objects the formalized statements of *A complete characterization of eventually entanglement breaking unital quantum channels* (arXiv:2609.24168) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat`
--   - `Vec`
--   - `Map`
--   - `Unitary`
--   - `applyMap`: Source pp.4–5, matrix action through the frozen Hilbert-space `QAlgorithms.act`. Flatten the input matrix in the ordered matrix-unit basis and read the output entries.
--   - `choi`: Source p.5, unnormalized output-first Choi reshuffle.
--   - `ad`: Source p.5, X ↦ B X B*.
--   - `outer`: Source p.4, |u><v|, with the conjugated bra.
--   - `vectorInner`: Source p.4, x* y.
--   - `coordinate`: Source p.4, standard ordered coordinate basis.
--   - `transposition`: Source p.5, fixed-basis transpose.
--   - `depolarizing`: Source (2.2), p.6: δ(X)=Tr(X) I/d.
--   - `dephasing`: Source p.7, standard-coordinate dephasing.
--   - `amplify`: Source Definition 2.2, p.5, φ⊗id_k with system factor first.
--   - `KPositive`: Source Definition 2.2, p.5.
--   - `CP`: Source Definition 2.2, p.5: all positive amplification sizes.
--   - `TwoCopositive`: Source Definition 2.2, p.5, input transposition.
--   - `CoCP`: Source Definition 2.2, p.5.
--   - `PPT`: Source Definition 2.2, p.5: PPT includes CP.
--   - `UnitalChannel`: Source p.5. Reuse the accepted CP+TP Kraus-channel predicate on the linear action.
--   - `EB`: Source Theorem 2.3(4), p.5: EB iff J is separable. Accepted positive separability permits zero and arbitrary total trace; no density normalization is imposed.
--   - `UEBTP`: Source p.8, precisely the unital EB channels.
--   - `beta`: Source (2.3), p.7, Ad(U) Δ Ad(V*).
--   - `Twisted`: Source p.7.
--   - `MTD`: Source Definition 2.13, p.8, finite convex mixtures.
--   - `Eventually`: Source Definitions 2.8 and 6.9, pp.6,24, positive thresholds.
--   - `Extreme`: Source p.9, extremality in UEBTP(d).
--   - `faceGenerators`: Source Theorem 3.1, p.9, the EB-dominated rank-one generators.
--   - `faceSpan`: Source Theorem 3.1, p.9.
--   - `krausSpace`: Source Remark 2.5, pp.5–6: span of the operators in Kraus representations. For CP maps these representations all have the same span; zero gives {0}.
--   - `krausRankOneSpan`: Source Corollary 3.3, p.10, the WHOLE rank-one Kraus-space span.
--   - `IsRealBasis`: Source pp.9–11, independence AND spanning the entire prescribed space.
--   - `products`: Source Theorem 3.1, p.9, Hermitian pairs over the real field.
--   - `ebRank`: Source Remark 2.7, p.6, minimum rank-one Kraus length. Non-EB input has empty defining set and default 0; no rank conclusion below uses that default.
--   - `choiRank`: Source Remark 2.5, p.6.
--   - `FullSpark`: Source Corollary 3.8, pp.11–12, every indexed d-element subfamily.
--   - `frameChannel`: Source Corollary 3.8, p.12, the constructed map.
--   - `ETF`: Source Definition 3.11, p.12. A frame is nonempty: this excludes the spurious empty family satisfying 0=(0/d)I. The source's d≤N uses this convention.
--   - `harmonic`: Source Example 3.10, p.12; Fin index k represents source k+1.
--   - `depolarizingMixture`: Source pp.7,26,29, for arbitrary real parameter.
--   - `dephasingMixture`: Source pp.21,23.
--   - `hsNorm`: Source pp.14,16, HS norm, unchanged by Choi reshuffling.
--   - `hsInner`: Source p.14, conjugate-linear in the first argument.
--   - `matrixInner`: Source p.17, HS orthogonality on matrices.
--   - `commutant`: Source pp.17,22, ordinary matrix multiplication.
--   - `center`: Source pp.18,22, inherited product.
--   - `CStar`: Source p.17, a unital *-subalgebra. Closedness is automatic in finite dimension.
--   - `Commutative`: Source p.17, all elements commute.
--   - `Fixes`: Source p.17, pointwise fixed.
--   - `Compatible`: Source p.17, A⊆Fix(t)∩Range(t)'.
--   - `complexCoordinates`: Source p.17, complex HS coordinates reconstructed from the frozen real `MatrixSketch.vectorize`, applied separately to real and imaginary parts. Reindexing back to pairs retains the source's ordered matrix-unit coordinates.
--   - `hilbertSubspace`: Source p.17, the matrix subspace A in its concrete Hilbert-space realization.
--   - `expectation`: Source p.17, unique TP expectation, CONSTRUCTED as the actual HS orthogonal projection of the matrix-unit basis. The finite-dimensional subspace is complete, so this definition uses no default-valued choice or unproved existence premise.
--   - `diagonalSpace`: Source p.7, standard diagonal algebra.
--   - `Reduces`: Source pp.18,22, invariance of S and its HS orthogonal complement.
--   - `peripheral`: Source Definition 6.1, p.22. Including zero in the generating set is harmless.
--   - `scalars`: Source p.25, scalar multiples of the identity.
--   - `Primitive`: Source p.25, the source's equivalent definition for discrete unital channels.
--   - `stableRange`: Source Theorem 6.11, p.24, all positive powers.
--   - `finiteStableRange`: Source Remark 6.12, p.25, finite intersection through d².
--   - `nonzeroGeneralizedSpan`: Source Remark 6.12, p.25, generalized eigenspaces at NONZERO eigenvalues.
--   - `EEB`: Source Remark 6.13, p.25.
--   - `Absorbing`: Source Remark 6.13, p.25, every eventually EB input.
--   - `UnitaryClosed`: Source Remark 6.13, p.25, both sides.
--   - `Blocks`: Source pp.17–18, positive consecutive coordinate block sizes.
--   - `offset`: Source p.18, starting coordinate.
--   - `blockProjection`: Source p.17, coordinate block projections.
--   - `blockAlgebra`: Source p.17, exactly ⊕ C I_mk, rather than an arbitrary conjugate algebra.
--   - `includeBlock`: Source p.18, zero extension. Off-diagonal INPUT and output blocks are killed.
--   - `restrictBlock`: Source p.18, ACTUAL restriction of the given map.
--   - `blockSum`: Source Definition 5.5, p.18, annihilating cross blocks.
--   - `binarySum`: Source Example 6.16, p.26, exactly two diagonal blocks, zero on cross blocks.
--   - `MinimalCentralFamily`: Source Lemma 5.4, p.18, COMPLETE minimal nonzero central projections.
--   - `NormalizedHaar`: Source p.14, normalized Haar by its defining intrinsic property; it is unique on the compact unitary group, so quantifying over it does not change the result.
--   - `InCommutant`: Source p.17, unitary elements of the commutant.
--   - `CommutantHaar`: Source p.17, Haar on U(A'), realized on U(d) with full mass on this closed subgroup. Invariance is required only under elements of U(A').
--   - `weightedIntegral`: Source pp.14–20, two independent Haar integrations and real weight.
--   - `integralDenominator`: Source pp.15,18–19, real denominator; only evaluated for m>1 in the formulas.
--   - `ChannelSemigroup`: Source pp.26–27. Actual continuous unital CHANNEL semigroup and its actual right-derivative generator, also related by the source exponential series. Negative times are unconstrained and unused.
--   - `poissonBoundary`: Source Definition 7.2, pp.26–27, imaginary generator eigenvalues.
--   - `SemigroupPrimitive`: Source Definition 7.3, p.27, unique strictly positive stationary density for the ADJOINT semigroup. Not defined by the conclusion ker L=C I.
--   - `EventuallyTime`: Source p.27, a positive real threshold and every later time.
--   - `exampleOperators`: Source Example 3.6, p.11, four actual operators.
--   - `bellTest`: Source Example 5.11, p.21, unnormalized Bell test vector.
--   - `negativeTestImage`: Source Example 5.11, p.21, expected block-amplification image.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, https://arxiv.org/abs/2609.24168v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_MultipleMatrixSketches

/-! arXiv:2609.24168v1. A map is its matrix in the ordered matrix-unit basis:
t[(i,j),(k,l)]=t(E_kl)[i,j]. Multiplication is composition, 1 is the identity,
and conjugate transpose is the HS adjoint. Choi matrices are unnormalized,
output first. Only paper-local interfaces are added; accepted files are frozen. -/

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

abbrev Vec (d : ℕ) := Fin d → ℂ

abbrev Map (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

abbrev Unitary (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Source pp.4–5, matrix action through the frozen Hilbert-space `QAlgorithms.act`.
Flatten the input matrix in the ordered matrix-unit basis and read the output entries. -/
def applyMap {d : ℕ} (t : Map d) (X : Mat d) : Mat d :=
  fun i j => QAlgorithms.act t (WithLp.toLp 2 (fun p => X p.1 p.2)) (i,j)

/-- Source p.5, unnormalized output-first Choi reshuffle. -/
def choi {d : ℕ} (t : Map d) : Map d := fun p q => t (p.1,q.1) (p.2,q.2)

/-- Source p.5, X ↦ B X B*. -/
def ad {d : ℕ} (B : Mat d) : Map d := fun p q => B p.1 q.1 * conj (B p.2 q.2)

/-- Source p.4, |u><v|, with the conjugated bra. -/
def outer {d : ℕ} (u v : Vec d) : Mat d := fun i j => u i * conj (v j)

/-- Source p.4, x* y. -/
def vectorInner {d : ℕ} (u v : Vec d) : ℂ := ∑ i, conj (u i) * v i

/-- Source p.4, standard ordered coordinate basis. -/
def coordinate {d : ℕ} (i : Fin d) : Vec d := fun j => if j = i then 1 else 0

/-- Source p.5, fixed-basis transpose. -/
def transposition (d : ℕ) : Map d := fun p q => if p = (q.2,q.1) then 1 else 0

/-- Source (2.2), p.6: δ(X)=Tr(X) I/d. -/
def depolarizing (d : ℕ) : Map d :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0

/-- Source p.7, standard-coordinate dephasing. -/
def dephasing (d : ℕ) : Map d := fun p q => if p.1 = p.2 ∧ p = q then 1 else 0

/-- Source Definition 2.2, p.5, φ⊗id_k with system factor first. -/
def amplify {d : ℕ} (t : Map d) (k : ℕ)
    (Z : Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ) :
    Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ :=
  fun p q => ∑ a, ∑ b, t (p.1,q.1) (a,b) * Z (a,p.2) (b,q.2)

/-- Source Definition 2.2, p.5. -/
def KPositive {d : ℕ} (k : ℕ) (t : Map d) : Prop :=
  ∀ Z : Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ,
    Z.PosSemidef → (amplify t k Z).PosSemidef

/-- Source Definition 2.2, p.5: all positive amplification sizes. -/
def CP {d : ℕ} (t : Map d) : Prop := ∀ k : ℕ, 0 < k → KPositive k t

/-- Source Definition 2.2, p.5, input transposition. -/
def TwoCopositive {d : ℕ} (t : Map d) : Prop := KPositive 2 (t * transposition d)

/-- Source Definition 2.2, p.5. -/
def CoCP {d : ℕ} (t : Map d) : Prop := CP (t * transposition d)

/-- Source Definition 2.2, p.5: PPT includes CP. -/
def PPT {d : ℕ} (t : Map d) : Prop := CP t ∧ CoCP t

/-- Source p.5. Reuse the accepted CP+TP Kraus-channel predicate on the linear action. -/
def UnitalChannel {d : ℕ} (t : Map d) : Prop :=
  QAlgorithms.IsChannel (applyMap t) ∧ applyMap t 1 = 1

/-- Source Theorem 2.3(4), p.5: EB iff J is separable. Accepted positive
separability permits zero and arbitrary total trace; no density normalization is imposed. -/
def EB {d : ℕ} (t : Map d) : Prop :=
  QAlgorithms.Entanglement.IsSeparablePositive (choi t)

/-- Source p.8, precisely the unital EB channels. -/
def UEBTP (d : ℕ) : Set (Map d) := {t | UnitalChannel t ∧ EB t}

/-- Source (2.3), p.7, Ad(U) Δ Ad(V*). -/
def beta {d : ℕ} (U V : Unitary d) : Map d :=
  ad (U : Mat d) * dephasing d * ad (V : Mat d)ᴴ

/-- Source p.7. -/
def Twisted {d : ℕ} (t : Map d) : Prop := ∃ U V : Unitary d, t = beta U V

/-- Source Definition 2.13, p.8, finite convex mixtures. -/
def MTD {d : ℕ} (t : Map d) : Prop :=
  ∃ n : ℕ, ∃ p : Fin n → ℝ, ∃ U V : Fin n → Unitary d,
    (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧ t = ∑ j, p j • beta (U j) (V j)

/-- Source Definitions 2.8 and 6.9, pp.6,24, positive thresholds. -/
def Eventually {d : ℕ} (P : Map d → Prop) (t : Map d) : Prop :=
  ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n → P (t ^ n)

/-- Source p.9, extremality in UEBTP(d). -/
def Extreme {d : ℕ} (t : Map d) : Prop :=
  t ∈ UEBTP d ∧ ∀ s r : Map d, s ∈ UEBTP d → r ∈ UEBTP d →
    ∀ p : ℝ, 0 < p → p < 1 → t = p • s + (1-p) • r → s = t ∧ r = t

/-- Source Theorem 3.1, p.9, the EB-dominated rank-one generators. -/
def faceGenerators {d : ℕ} (t : Map d) : Set (Map d) :=
  {s | ∃ B : Mat d, B.rank = 1 ∧ s = ad B ∧ EB (t - ad B)}

/-- Source Theorem 3.1, p.9. -/
def faceSpan {d : ℕ} (t : Map d) : Submodule ℝ (Map d) :=
  Submodule.span ℝ (faceGenerators t)

/-- Source Remark 2.5, pp.5–6: span of the operators in Kraus representations.
For CP maps these representations all have the same span; zero gives {0}. -/
def krausSpace {d : ℕ} (t : Map d) : Submodule ℂ (Mat d) :=
  Submodule.span ℂ {B | ∃ n : ℕ, ∃ A : Fin n → Mat d,
    t = ∑ j, ad (A j) ∧ B ∈ Set.range A}

/-- Source Corollary 3.3, p.10, the WHOLE rank-one Kraus-space span. -/
def krausRankOneSpan {d : ℕ} (t : Map d) : Submodule ℝ (Map d) :=
  Submodule.span ℝ {s | ∃ B : Mat d, B ∈ krausSpace t ∧ B.rank = 1 ∧ s = ad B}

/-- Source pp.9–11, independence AND spanning the entire prescribed space. -/
def IsRealBasis {d n : ℕ} (A : Fin n → Map d) (S : Submodule ℝ (Map d)) : Prop :=
  LinearIndependent ℝ A ∧ Submodule.span ℝ (Set.range A) = S

/-- Source Theorem 3.1, p.9, Hermitian pairs over the real field. -/
def products {d : ℕ} (B : Mat d) : Mat d × Mat d := (B * Bᴴ, Bᴴ * B)

/-- Source Remark 2.7, p.6, minimum rank-one Kraus length. Non-EB input has
empty defining set and default 0; no rank conclusion below uses that default. -/
def ebRank {d : ℕ} (t : Map d) : ℕ :=
  sInf {n | ∃ A : Fin n → Mat d, (∀ j, (A j).rank = 1) ∧ t = ∑ j, ad (A j)}

/-- Source Remark 2.5, p.6. -/
def choiRank {d : ℕ} (t : Map d) : ℕ := (choi t).rank

/-- Source Corollary 3.8, pp.11–12, every indexed d-element subfamily. -/
def FullSpark {d n : ℕ} (u : Fin n → Vec d) : Prop :=
  ∀ f : Fin d ↪ Fin n, LinearIndependent ℂ (fun i => u (f i))

/-- Source Corollary 3.8, p.12, the constructed map. -/
def frameChannel {d n : ℕ} (p : Fin n → ℝ) (u v : Fin n → Vec d) : Map d :=
  ∑ j, p j • ad (outer (u j) (v j))

/-- Source Definition 3.11, p.12. A frame is nonempty: this excludes the
spurious empty family satisfying 0=(0/d)I. The source's d≤N uses this convention. -/
def ETF {d n : ℕ} (w : Fin n → Vec d) : Prop :=
  0 < n ∧ (∀ j, QAlgorithms.RealRegisters.IsUnitVector (WithLp.toLp 2 (w j))) ∧
    (∀ i j, i ≠ j → ‖vectorInner (w i) (w j)‖ =
      Real.sqrt (((n : ℝ) - d) / ((d : ℝ) * ((n : ℝ) - 1)))) ∧
    (∑ j, outer (w j) (w j)) = ((n : ℝ) / d) • (1 : Mat d)

/-- Source Example 3.10, p.12; Fin index k represents source k+1. -/
def harmonic {d n : ℕ} (k : Fin n) : Vec d := fun j =>
  (Real.sqrt (d : ℝ) : ℂ)⁻¹ *
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) ^ (j.val * (k.val + 1))

/-- Source pp.7,26,29, for arbitrary real parameter. -/
def depolarizingMixture (d : ℕ) (a : ℝ) : Map d := a • 1 + (1-a) • depolarizing d

/-- Source pp.21,23. -/
def dephasingMixture (d : ℕ) (a : ℝ) : Map d := a • 1 + (1-a) • dephasing d

/-- Source pp.14,16, HS norm, unchanged by Choi reshuffling. -/
def hsNorm {d : ℕ} (t : Map d) : ℝ := Real.sqrt (∑ p, ∑ q, Complex.normSq (t p q))

/-- Source p.14, conjugate-linear in the first argument. -/
def hsInner {d : ℕ} (s t : Map d) : ℂ := ∑ p, ∑ q, conj (s p q) * t p q

/-- Source p.17, HS orthogonality on matrices. -/
def matrixInner {d : ℕ} (X Y : Mat d) : ℂ := (Xᴴ * Y).trace

/-- Source pp.17,22, ordinary matrix multiplication. -/
def commutant {d : ℕ} (S : Set (Mat d)) : Set (Mat d) :=
  {X | ∀ Y ∈ S, X * Y = Y * X}

/-- Source pp.18,22, inherited product. -/
def center {d : ℕ} (S : Set (Mat d)) : Set (Mat d) := S ∩ commutant S

/-- Source p.17, a unital *-subalgebra. Closedness is automatic in finite dimension. -/
def CStar {d : ℕ} (A : Submodule ℂ (Mat d)) : Prop :=
  (1 : Mat d) ∈ A ∧ (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ X ∈ A, Xᴴ ∈ A)

/-- Source p.17, all elements commute. -/
def Commutative {d : ℕ} (A : Submodule ℂ (Mat d)) : Prop :=
  ∀ X ∈ A, ∀ Y ∈ A, X * Y = Y * X

/-- Source p.17, pointwise fixed. -/
def Fixes {d : ℕ} (t : Map d) (A : Submodule ℂ (Mat d)) : Prop := ∀ X ∈ A, applyMap t X = X

/-- Source p.17, A⊆Fix(t)∩Range(t)'. -/
def Compatible {d : ℕ} (A : Submodule ℂ (Mat d)) (t : Map d) : Prop :=
  Fixes t A ∧ ∀ X : Mat d, applyMap t X ∈ commutant (A : Set (Mat d))

/-- Source p.17, complex HS coordinates reconstructed from the frozen real
`MatrixSketch.vectorize`, applied separately to real and imaginary parts.
Reindexing back to pairs retains the source's ordered matrix-unit coordinates. -/
def complexCoordinates {d : ℕ} (X : Mat d) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p =>
    (QAlgorithms.MatrixSketch.vectorize (fun i j => (X i j).re) (finProdFinEquiv p) : ℂ) +
    (QAlgorithms.MatrixSketch.vectorize (fun i j => (X i j).im) (finProdFinEquiv p) : ℂ) *
      Complex.I)

/-- Source p.17, the matrix subspace A in its concrete Hilbert-space realization. -/
def hilbertSubspace {d : ℕ} (A : Submodule ℂ (Mat d)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d × Fin d)) :=
  Submodule.span ℂ (Set.range (fun X : A => complexCoordinates (X : Mat d)))

/-- Source p.17, unique TP expectation, CONSTRUCTED as the actual HS orthogonal
projection of the matrix-unit basis. The finite-dimensional subspace is complete,
so this definition uses no default-valued choice or unproved existence premise. -/
def expectation {d : ℕ} (A : Submodule ℂ (Mat d)) : Map d :=
  fun p q => ((hilbertSubspace A).orthogonalProjectionOnto
    (complexCoordinates (Matrix.single q.1 q.2 (1 : ℂ)))).val p

/-- Source p.7, standard diagonal algebra. -/
def diagonalSpace (d : ℕ) : Submodule ℂ (Mat d) :=
  Submodule.span ℂ (Set.range (fun i : Fin d => Matrix.single i i (1 : ℂ)))

/-- Source pp.18,22, invariance of S and its HS orthogonal complement. -/
def Reduces {d : ℕ} (t : Map d) (S : Set (Mat d)) : Prop :=
  (∀ X ∈ S, applyMap t X ∈ S) ∧ ∀ X : Mat d,
    (∀ Y ∈ S, matrixInner Y X = 0) → ∀ Y ∈ S, matrixInner Y (applyMap t X) = 0

/-- Source Definition 6.1, p.22. Including zero in the generating set is harmless. -/
def peripheral {d : ℕ} (t : Map d) : Submodule ℂ (Mat d) :=
  Submodule.span ℂ {X | ∃ a : ℂ, ‖a‖ = 1 ∧ applyMap t X = a • X}

/-- Source p.25, scalar multiples of the identity. -/
def scalars (d : ℕ) : Submodule ℂ (Mat d) := Submodule.span ℂ {(1 : Mat d)}

/-- Source p.25, the source's equivalent definition for discrete unital channels. -/
def Primitive {d : ℕ} (t : Map d) : Prop := peripheral t = scalars d

/-- Source Theorem 6.11, p.24, all positive powers. -/
def stableRange {d : ℕ} (t : Map d) : Set (Mat d) :=
  {X | ∀ n : ℕ, 1 ≤ n → ∃ Y : Mat d, applyMap (t ^ n) Y = X}

/-- Source Remark 6.12, p.25, finite intersection through d². -/
def finiteStableRange {d : ℕ} (t : Map d) : Set (Mat d) :=
  {X | ∀ n : ℕ, 1 ≤ n → n ≤ d^2 → ∃ Y : Mat d, applyMap (t ^ n) Y = X}

/-- Source Remark 6.12, p.25, generalized eigenspaces at NONZERO eigenvalues. -/
def nonzeroGeneralizedSpan {d : ℕ} (t : Map d) : Submodule ℂ (Mat d) :=
  Submodule.span ℂ {X | ∃ a : ℂ, a ≠ 0 ∧ ∃ k : ℕ, 1 ≤ k ∧
    applyMap ((t - a • (1 : Map d)) ^ k) X = 0}

/-- Source Remark 6.13, p.25. -/
def EEB (d : ℕ) : Set (Map d) := {t | UnitalChannel t ∧ Eventually EB t}

/-- Source Remark 6.13, p.25, every eventually EB input. -/
def Absorbing {d : ℕ} (S : Set (Map d)) : Prop :=
  ∀ t ∈ EEB d, ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n → t^n ∈ S

/-- Source Remark 6.13, p.25, both sides. -/
def UnitaryClosed {d : ℕ} (S : Set (Map d)) : Prop :=
  ∀ t ∈ S, ∀ U V : Unitary d, ad (U : Mat d) * t * ad (V : Mat d) ∈ S

/-- Source pp.17–18, positive consecutive coordinate block sizes. -/
structure Blocks (d : ℕ) where
  count : ℕ
  count_pos : 0 < count
  size : Fin count → ℕ
  size_pos : ∀ k, 0 < size k
  total : ∑ k, size k = d

/-- Source p.18, starting coordinate. -/
def offset {d : ℕ} (b : Blocks d) (k : Fin b.count) : ℕ :=
  ∑ j : Fin b.count, if j < k then b.size j else 0

/-- Source p.17, coordinate block projections. -/
def blockProjection {d : ℕ} (b : Blocks d) (k : Fin b.count) : Mat d :=
  fun i j => if i = j ∧ offset b k ≤ i.val ∧ i.val < offset b k + b.size k then 1 else 0

/-- Source p.17, exactly ⊕ C I_mk, rather than an arbitrary conjugate algebra. -/
def blockAlgebra {d : ℕ} (b : Blocks d) : Submodule ℂ (Mat d) :=
  Submodule.span ℂ (Set.range (blockProjection b))

/-- Source p.18, zero extension. Off-diagonal INPUT and output blocks are killed. -/
def includeBlock {d : ℕ} (b : Blocks d) (k : Fin b.count) (t : Map (b.size k)) : Map d :=
  fun p q => ∑ i : Fin (b.size k), ∑ j : Fin (b.size k),
    ∑ a : Fin (b.size k), ∑ c : Fin (b.size k),
      if p.1.val = offset b k + i.val ∧ p.2.val = offset b k + j.val ∧
        q.1.val = offset b k + a.val ∧ q.2.val = offset b k + c.val
      then t (i,j) (a,c) else 0

/-- Source p.18, ACTUAL restriction of the given map. -/
def restrictBlock {d : ℕ} (b : Blocks d) (k : Fin b.count) (t : Map d) : Map (b.size k) :=
  fun p q => ∑ i : Fin d, ∑ j : Fin d, ∑ a : Fin d, ∑ c : Fin d,
    if i.val = offset b k + p.1.val ∧ j.val = offset b k + p.2.val ∧
      a.val = offset b k + q.1.val ∧ c.val = offset b k + q.2.val
    then t (i,j) (a,c) else 0

/-- Source Definition 5.5, p.18, annihilating cross blocks. -/
def blockSum {d : ℕ} (b : Blocks d) (t : (k : Fin b.count) → Map (b.size k)) : Map d :=
  ∑ k, includeBlock b k (t k)

/-- Source Example 6.16, p.26, exactly two diagonal blocks, zero on cross blocks. -/
def binarySum {m n : ℕ} (s : Map m) (t : Map n) : Map (m+n) :=
  fun p q =>
    (∑ i : Fin m, ∑ j : Fin m, ∑ a : Fin m, ∑ c : Fin m,
      if p.1.val = i.val ∧ p.2.val = j.val ∧ q.1.val = a.val ∧ q.2.val = c.val
      then s (i,j) (a,c) else 0) +
    (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ c : Fin n,
      if p.1.val = m+i.val ∧ p.2.val = m+j.val ∧ q.1.val = m+a.val ∧ q.2.val = m+c.val
      then t (i,j) (a,c) else 0)

/-- Source Lemma 5.4, p.18, COMPLETE minimal nonzero central projections. -/
def MinimalCentralFamily {d r : ℕ} (A : Submodule ℂ (Mat d)) (P : Fin r → Mat d) : Prop :=
  (∑ k, P k) = 1 ∧ (∀ k, P k ∈ center (A : Set (Mat d)) ∧
    P k ≠ 0 ∧ (P k)ᴴ = P k ∧ P k * P k = P k ∧
    ∀ Q ∈ center (A : Set (Mat d)), Qᴴ = Q → Q*Q = Q → P k * Q = Q → Q = 0 ∨ Q = P k) ∧
    ∀ i j, i ≠ j → P i * P j = 0

/-- Source p.14, finite-dimensional Borel topology. -/
local instance unitaryMeasurable (d : ℕ) : MeasurableSpace (Unitary d) := borel (Unitary d)

/-- Source p.14, normalized Haar by its defining intrinsic property; it is unique
on the compact unitary group, so quantifying over it does not change the result. -/
def NormalizedHaar {d : ℕ} (mu : Measure (Unitary d)) : Prop :=
  IsProbabilityMeasure mu ∧ ∀ U : Unitary d, Measure.map (fun V => U * V) mu = mu

/-- Source p.17, unitary elements of the commutant. -/
def InCommutant {d : ℕ} (A : Submodule ℂ (Mat d)) (U : Unitary d) : Prop :=
  (U : Mat d) ∈ commutant (A : Set (Mat d))

/-- Source p.17, Haar on U(A'), realized on U(d) with full mass on this closed
subgroup. Invariance is required only under elements of U(A'). -/
def CommutantHaar {d : ℕ} (A : Submodule ℂ (Mat d)) (mu : Measure (Unitary d)) : Prop :=
  IsProbabilityMeasure mu ∧ mu {U | ¬ InCommutant A U} = 0 ∧
    ∀ U : Unitary d, InCommutant A U → Measure.map (fun V => U * V) mu = mu

/-- Source pp.14–20, two independent Haar integrations and real weight. -/
def weightedIntegral {d : ℕ} (mu : Measure (Unitary d)) (w : Unitary d → Unitary d → ℝ) : Map d :=
  ∫ U, ∫ V, w U V • beta U V ∂mu ∂mu

/-- Source pp.15,18–19, real denominator; only evaluated for m>1 in the formulas. -/
def integralDenominator (m : ℕ) : ℝ := ((m : ℝ)-1) * ((m : ℝ)+1)^2

/-- Source pp.26–27. Actual continuous unital CHANNEL semigroup and its actual
right-derivative generator, also related by the source exponential series.
Negative times are unconstrained and unused. -/
structure ChannelSemigroup (d : ℕ) where
  time : ℝ → Map d
  generator : Map d
  zero_time : time 0 = 1
  add_time : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → time (s+t) = time s * time t
  continuous_time : ContinuousOn time (Ici 0)
  channel_time : ∀ t : ℝ, 0 ≤ t → UnitalChannel (time t)
  derivative : Tendsto (fun t : ℝ => t⁻¹ • (time t - 1)) (nhdsWithin 0 (Ioi 0)) (nhds generator)
  exponential : ∀ t : ℝ, 0 ≤ t → time t =
    ∑' n : ℕ, (t^n / (n.factorial : ℝ)) • generator^n

/-- Source Definition 7.2, pp.26–27, imaginary generator eigenvalues. -/
def poissonBoundary {d : ℕ} (s : ChannelSemigroup d) : Submodule ℂ (Mat d) :=
  Submodule.span ℂ {X | ∃ a : ℝ, applyMap s.generator X = ((a : ℂ) * Complex.I) • X}

/-- Source Definition 7.3, p.27, unique strictly positive stationary density for
the ADJOINT semigroup. Not defined by the conclusion ker L=C I. -/
def SemigroupPrimitive {d : ℕ} (s : ChannelSemigroup d) : Prop :=
  ∃! rho : Mat d, QAlgorithms.IsDensityMatrix rho ∧ rho.PosDef ∧
    ∀ t : ℝ, 0 ≤ t → applyMap (s.time t)ᴴ rho = rho

/-- Source p.27, a positive real threshold and every later time. -/
def EventuallyTime {d : ℕ} (P : Map d → Prop) (s : ChannelSemigroup d) : Prop :=
  ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, t0 ≤ t → P (s.time t)

/-- Source Example 3.6, p.11, four actual operators. -/
def exampleOperators : Fin 4 → Mat 2 :=
  let e1 := coordinate (0 : Fin 2)
  let e2 := coordinate (1 : Fin 2)
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  let u := c • (e1 + e2)
  let v := c • (e1 - e2)
  ![c • outer e1 e1, c • outer e2 u, c • outer u e2, c • outer v v]

/-- Source Example 5.11, p.21, unnormalized Bell test vector. -/
def bellTest (d : ℕ) : Fin d × Fin 2 → ℂ := fun p => if p.1.val = p.2.val then 1 else 0

/-- Source Example 5.11, p.21, expected block-amplification image. -/
def negativeTestImage (d : ℕ) (a : ℝ) : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ :=
  fun p q =>
    if (p.1.val = 0 ∧ p.2.val = 0 ∧ q.1.val = 0 ∧ q.2.val = 0) ∨
      (p.1.val = 1 ∧ p.2.val = 1 ∧ q.1.val = 1 ∧ q.2.val = 1) then 1
    else if (p.1.val = 1 ∧ p.2.val = 0 ∧ q.1.val = 0 ∧ q.2.val = 1) ∨
      (p.1.val = 0 ∧ p.2.val = 1 ∧ q.1.val = 1 ∧ q.2.val = 0) then (a : ℂ) else 0

/-! Sanity examples for local coordinates, not proofs of paper results. -/

example {d : ℕ} (t : Map d) : choi (choi t) = t := rfl

example : depolarizing 2 (0,0) (1,1) = (2 : ℂ)⁻¹ := by simp [depolarizing]

example : dephasing 2 (0,1) (0,1) = 0 := by simp [dephasing]

example : transposition 2 (0,1) (1,0) = 1 := by simp [transposition]

example : integralDenominator 2 = 9 := by norm_num [integralDenominator]

example : hsNorm (0 : Map 2) = 0 := by simp [hsNorm]

example {d : ℕ} (t : Map d) : t ^ (0 : ℕ) = 1 := pow_zero t

/-! Additional small model checks, including degenerate inputs. -/

example {d : ℕ} (X : Mat d) : applyMap (0 : Map d) X = 0 := by
  ext i j
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

example {d : ℕ} (u : Vec d) : outer (0 : Vec d) u = 0 := by
  ext i j
  simp [outer]

example : coordinate (0 : Fin 1) 0 = 1 := by simp [coordinate]

example : ¬ QAlgorithms.RealRegisters.IsUnitVector (WithLp.toLp 2 (0 : Vec 1)) := by
  simp [QAlgorithms.RealRegisters.IsUnitVector]

example : vectorInner (coordinate (0 : Fin 1)) (coordinate 0) = 1 := by
  simp [vectorInner, coordinate]

example {d : ℕ} (B : Mat d) (i j k l : Fin d) :
    choi (ad B) (i,k) (j,l) = B i k * conj (B j l) := rfl

example {d : ℕ} (u v : Vec d) (i j : Fin d) :
    outer u v i j = u i * conj (v j) := rfl

example {d k : ℕ} (Z : Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ) :
    amplify (0 : Map d) k Z = 0 := by
  ext p q
  simp [amplify]

example {d : ℕ} (t : Map d) :
    TwoCopositive t ↔ KPositive 2 (t * transposition d) := Iff.rfl

example {d : ℕ} (t : Map d) : PPT t ↔ CP t ∧ CoCP t := Iff.rfl

example {d : ℕ} (t : Map d) :
    UnitalChannel t ↔ QAlgorithms.IsChannel (applyMap t) ∧ applyMap t 1 = 1 := Iff.rfl

example {d : ℕ} : EB (0 : Map d) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j
  · ext p q
    simp [choi]

example {d : ℕ} (p : Fin 0 → ℝ) (u v : Fin 0 → Vec d) :
    frameChannel p u v = 0 := by simp [frameChannel]

example {d : ℕ} (w : Fin 0 → Vec d) : ¬ ETF w := by simp [ETF]

example {d : ℕ} : depolarizingMixture d 0 = depolarizing d := by
  simp [depolarizingMixture]

example {d : ℕ} : dephasingMixture d 0 = dephasing d := by
  simp [dephasingMixture]

example {d : ℕ} (t : Map d) : hsInner 0 t = 0 := by simp [hsInner]

example {d : ℕ} (B : Mat d) : products B = (B * Bᴴ, Bᴴ * B) := rfl

example {d : ℕ} (A : Submodule ℂ (Mat d)) (p q : Fin d × Fin d) :
    expectation A p q = ((hilbertSubspace A).orthogonalProjectionOnto
      (complexCoordinates (Matrix.single q.1 q.2 (1 : ℂ)))).val p := rfl

example {d : ℕ} (X : Mat d) (i j : Fin d) : complexCoordinates X (i,j) = X i j := by
  simp [complexCoordinates, QAlgorithms.MatrixSketch.vectorize, Complex.re_add_im]
  exact congrArg (fun p : Fin d × Fin d => X p.1 p.2)
    (finProdFinEquiv.symm_apply_apply (i, j))

example {m n : ℕ} : binarySum (0 : Map m) (0 : Map n) = 0 := by
  ext p q
  simp [binarySum]

example {d : ℕ} (s : ChannelSemigroup d) : s.time 0 = 1 := s.zero_time

example (a : ℝ) : negativeTestImage 2 a (1,0) (0,1) = (a : ℂ) := by
  simp [negativeTestImage]

example : bellTest 2 (0,0) = 1 ∧ bellTest 2 (0,1) = 0 := by simp [bellTest]

end QAlgorithms.Papers.Independent.Information100.P26


