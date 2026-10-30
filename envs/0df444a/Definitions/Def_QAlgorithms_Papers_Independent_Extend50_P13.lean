-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13
-- name    : QAlgorithms_Papers_Independent_Extend50_P13
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:31:47.526126+00:00
-- url     : https://prove2.me/theorems/500d37fa-d0ef-4d3f-ac7b-88fb16ee7195
-- title:
--   Definitions for Positive maps and trace polynomials from the symmetric group
-- statement:
--   The objects the formalized statements of *Positive maps and trace polynomials from the symmetric group* (arXiv:2002.12887) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tensorFamily`: Entrywise finite tensor product in the original factor order (pp.6–7).
--   - `tensorMatrices`: Homogeneous tensor product (pp.6–9).
--   - `append`: Append the output coordinate after the input coordinates (Eq.32).
--   - `contractInputs`: Partial-trace contraction of an arbitrary physical operator, Eq.57, p.14. The indices compute tr_inputs[P (X_1 ⊗ ... ⊗ X_r ⊗ I)].
--   - `linearContraction`: Linearization on the entire joint-input algebra, the first equality of Eq.53, p.13. It is independent of any factorization of the input.
--   - `copositiveAmplification`: Amplification of Z ↦ linearContraction P Z.transpose on a single, arbitrary ancilla (p.13). Transposition is on all input factors, not on the ancilla.
--   - `centralProjector`: Fixed normalized central Young projector, Eq.31, p.9. The partition bound is k, independent of physical d; shapes taller than d remain included. The character is computed from the accepted regular Young ideal, never supplied as a PSD certificate.
--   - `polarizedMap`: Definition 4, Eq.32, p.9, with its original normalization.
--   - `verticalOperators`: Vertical tensor product followed by regrouping into input/output copies of the global register, Eq.45, p.12. No factorization of the input is assumed.
--   - `mixedMap`: Mixed tensor product of the normalized maps, Eq.45–47, p.12.
--   - `rankOneOperator`: Arbitrary, unnormalized rank-one operator |v><w|, Eq.33, p.10.
--   - `RealNonnegative`: Scalar nonnegativity includes reality; discarding the imaginary part alone would not express the source's scalar inequalities (pp.5,14).
--   - `finiteMatrixElement`: Matrix element, with conjugate linearity in the bra, Eq.33.
--   - `FullyBlockPositive`: Full multipartite block positivity, tested on all unnormalized pure product vectors; by convexity this is exactly testing all fully separable states (p.14).
--   - `PositiveMap`: Positivity on every tuple in the positive cone, pp.6,15.
--   - `DiagonalUnitaryInvariant`: Diagonal-unitary invariance of the physical operator, pp.14–15.
--   - `ConjugationEquivariant`: Simultaneous-conjugation equivariance for arbitrary complex inputs, p.6 and footnote 61 on p.28.
--   - `TraceMonomial`: A multilinear trace monomial: one open word and finitely many traced words, using each variable exactly once in total, Eq.60, p.15. Empty open word is I.
--   - `matrixWord`: Ordered matrix-word evaluation, Eq.27, p.9.
--   - `TracePolynomial`: Finite complex linear combination of the actual multilinear trace monomials; raw syntax is not asserted to be unique (p.15).
--   - `evaluateTracePolynomial`: Evaluation of the syntax; scalar trace-only terms multiply I (pp.6,15).
--   - `IsTracePolynomial`: Evaluated trace-polynomial maps, modulo all evaluation identities (p.15).
--   - `fillSlot`: Fill one retained slot with a and the other slots with s, Eq.25, p.8.
--   - `partialTraceSlot`: Ordinary partial trace retaining slot q, pp.8–9.
--   - `cycleList`: Cycle written starting immediately after q and ending at q, Eq.27, p.9. Mathlib omits fixed points, so they are supplied explicitly as singleton words.
--   - `cycleLeaders`: Canonical cycle representatives: largest element in each cycle, including fixed points. Products of their scalar traces do not require a list ordering (p.9).
--   - `closedCycleExpression`: Full trace-word product over all canonical cycles, Eq.30.
--   - `openCycleExpression`: Traced closed cycles times the untraced word ending at the retained slot, Eq.28, pp.8–9. Untraced words are never cyclically rotated without changing q.
--   - `FullySeparableDensity`: Fully separable density matrices, using arbitrary finite convex combinations of product density matrices; no bipartite-only relaxation (p.14).
--   - `OptimalWernerWitness`: The paper's optimal Werner witness: invariant, block positive, detecting some entangled state, and saturating on a separable state (p.14).
--   - `Saturates`: The paper's saturation convention for optimal positive maps (p.15).
--   - `joinSubsystemCoordinates`: Join reduced and complement coordinates, preserving subsystem positions (Eqs.48–51, p.12).
--   - `embedSubsystemIdentity`: Tensor identities into the complement in its original positions (p.12).
--   - `transposeOn`: Partial transpose on a specified set of tensor factors, p.12.
--   - `shadow`: Shadow operator, Eq.48, p.12.
--   - `anti`: Anticommutator used in Eq.49 (p.12).
--   - `bilinearExpansion`: Eq.51 with the forced correction (2/3)^n, rather than printed (3/2)^n. All products are formed on the reduced register before embedding (p.12).
--   - `bipartiteExpansion`: Explicit bipartite Eq.49, p.12.
--   - `reductionPolynomial`: Unscaled reduction polynomial, p.10, Example 8.
--   - `antisymmetricThree`: Unscaled three-box antisymmetric polynomial, Eq.40, p.11.
--   - `mixedThree`: Unscaled (2,1) polynomial, p.12.
--   - `witnessThree`: Unscaled tripartite-witness polynomial, Eq.67, p.16.
--   - `finePolynomial`: The four literal fine-grained inequalities in Eq.54, p.13.
--   - `fineProjector`: Four normalized physical projectors, from the two decompositions above Eq.54. The sum of either pair is P_(2,1); each displayed polynomial is six times its map.
--   - `motzkin`: Motzkin matrix polynomial, Eq.70, p.17.
--   - `motzkinSquares`: Exact square decomposition printed in Eq.71, p.17.
--   - `homogeneousMotzkin`: Homogenized Motzkin formula, Eq.72, p.17. No division by a trace.
--   - `tableFour31`: Literal Table II entry for [3,1], with trace-only terms multiplying I (PDF p.25, table introduced p.24).
--   - `tableFour22`: Literal Table II entry for [2,2] (PDF p.25).
--   - `tableFour211`: Literal Table II entry for [2,1,1] (PDF p.25).
--   - `tableFour1111`: Literal Table II entry for [1,1,1,1] (PDF p.25).
--   - `TableProperties`: The properties asserted for each Table II map in the Appendix B introduction (PDF p.24): positive, dimension-dependent vanishing, equivariant, completely copositive, and tensor-stable, with positive dimensions and arbitrary ancillas.
--   - `GroupCoefficients`: The finite group algebra in its full coefficient-function coordinates (pp.18–21). Coefficients are constant complex numbers, independent of all inputs.
--   - `coefficientProduct`: Group-algebra multiplication in coefficient coordinates (pp.20–21).
--   - `groupOperator`: Fixed linear extension of the physical permutation action, pp.8,20.
--   - `centralCoefficients`: Character-computed central idempotent coefficients, Eq.A16 and Eq.31. These are independent of the physical dimension (pp.9,24).
--   - `InAntisymmetricIdeal`: The actual sum of isotypic ideals for shapes with more than d rows, Eq.C2, p.26. It is constructed as the sum of the central-idempotent-generated ideals, not defined as the physical representation's kernel.
--   - `inputSlot`: First r slots are matrix inputs, last t slots are marked tensor outputs (Eqs.81–85 and C3–C5, pp.18–19,26).
--   - `outputSlot`: Output marker in the shared input/output register (pp.18–19,26).
--   - `joinSlots`: Ordered concatenation of input and output coordinates (pp.18–19,26).
--   - `gPolynomial`: C1 with its last variable still present, p.26.
--   - `hPolynomial`: All-t-output contraction with identities in the output slots (C3–C5, p.26). The coordinate formula fixes the C5 alpha/beta, k−t argument and retained-slot typos.
--   - `TensorTraceMonomial`: Multilinear tensor-trace monomial with t ordered output words and arbitrary closed input trace words. Every input label appears once overall. Empty output words give identity factors (pp.6,18–19,25–26).
--   - `TensorTracePolynomial`: Formal finite tensor-trace polynomials, before taking evaluation identities (pp.6,18–19,25–26).
--   - `evaluateTensorTrace`: Ordered tensor-word evaluation; closed words supply scalar ordinary traces (pp.6,18–19).
--   - `IsNoncommutativePolynomial`: Noncommutative polynomial functions (Definition 29, p.25); evaluation is from actual words, not an arbitrary function with a desired output certificate.
--   - `IsTensorPolynomial`: Pure tensor-polynomial functions are the no-closed-trace subcase of the formal tensor-word evaluation (Definition 29, p.25).
--   - `monomialPermutation`: Concrete permutation for a tensor trace monomial: close each output word with its own output marker, close the trace words, then invert the disjoint cycle product to match the paper's T convention (pp.9,18–19).
--   - `tensorPermutationExpansion`: Constant-coefficient group-algebra expansion beta constructed from formal words, not selected separately for each evaluated input (Eqs.81,84, pp.18–19).
--   - `PureTraceMonomial`: Scalar pure trace monomial with each input label appearing once (pp.6,18).
--   - `PureTracePolynomial`: Scalar multilinear trace polynomials, pp.6,18.
--   - `evaluatePureTrace`: Scalar closed-word evaluation (pp.6,18).
--   - `outputPermutation`: Lift a fixed output permutation by its disjoint cycles onto the output markers; singleton cycles are retained in the cycle convention (p.19).
--   - `pureTracePermutation`: Permutation representing a scalar pure-trace monomial times a fixed output permutation. The input cycle factors are inverted, the output action is not (p.19).
--   - `pureTraceExpansion`: Constant-coefficient gamma after expanding the scalar invariant into closed trace words. This replaces the input-dependent group-algebra shorthand in Eq.83 (PDF p.19), without making that shorthand a definition.
--   - `FullNontrivialCycle`: Full-support single nontrivial cycle (Theorem 30(i)–(iii), p.26).
--   - `OutputMarkedCycles`: Exactly t cycles with exactly one marked output apiece and no extra input-only cycles. Output actions are required nontrivial where printed in Theorem 30(iv)–(v), p.26; empty words remain allowed in the general syntax.
--   - `ClosedOutputAction`: A closed prescribed output permutation, with input-only remaining cycles (Theorem 30(iv), C4, p.26).
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, https://arxiv.org/abs/2002.12887v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Entrywise finite tensor product in the original factor order (pp.6–7). -/
def tensorFamily {J : Type*} [Fintype J] (dims : J → ℕ)
    (X : (j : J) → (Matrix (Fin (dims j)) (Fin (dims j)) ℂ)) : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  fun a b => ∏ j, X j (a j) (b j)

/-- Homogeneous tensor product (pp.6–9). -/
def tensorMatrices {I : Type*} {r : ℕ} (X : Fin r → (Matrix I I ℂ)) : (Matrix (Fin r → I) (Fin r → I) ℂ) :=
  fun a b => ∏ i, X i (a i) (b i)

/-- Append the output coordinate after the input coordinates (Eq.32). -/
def append {I : Type*} {r : ℕ} (x : Fin r → I) (a : I) : Fin (r+1) → I :=
  Fin.lastCases a x

/-- Partial-trace contraction of an arbitrary physical operator, Eq.57, p.14.
The indices compute tr_inputs[P (X_1 ⊗ ... ⊗ X_r ⊗ I)]. -/
def contractInputs {I : Type*} [Fintype I] {r : ℕ}
    (P : (Matrix (Fin (r+1) → I) (Fin (r+1) → I) ℂ)) (X : Fin r → (Matrix I I ℂ)) : (Matrix I I ℂ) :=
  fun a b => ∑ x : Fin r → I, ∑ y : Fin r → I,
    P (append x a) (append y b) * ∏ i, X i (y i) (x i)

/-- Linearization on the entire joint-input algebra, the first equality of Eq.53,
p.13. It is independent of any factorization of the input. -/
def linearContraction {I : Type*} [Fintype I] {r : ℕ}
    (P : (Matrix (Fin (r+1) → I) (Fin (r+1) → I) ℂ)) (Z : (Matrix (Fin r → I) (Fin r → I) ℂ)) : (Matrix I I ℂ) :=
  fun a b => ∑ x : Fin r → I, ∑ y : Fin r → I,
    P (append x a) (append y b) * Z y x

/-- Amplification of Z ↦ linearContraction P Z.transpose on a single, arbitrary
ancilla (p.13). Transposition is on all input factors, not on the ancilla. -/
def copositiveAmplification {I : Type*} [Fintype I] {r : ℕ}
    (P : (Matrix (Fin (r+1) → I) (Fin (r+1) → I) ℂ)) (m : ℕ)
    (Z : (Matrix ((Fin r → I) × Fin m) ((Fin r → I) × Fin m) ℂ)) : (Matrix (I × Fin m) (I × Fin m) ℂ) :=
  fun a b => ∑ x : Fin r → I, ∑ y : Fin r → I,
    P (append x a.1) (append y b.1) * Z (x,a.2) (y,b.2)

/-- Fixed normalized central Young projector, Eq.31, p.9. The partition bound is
k, independent of physical d; shapes taller than d remain included. The character
is computed from the accepted regular Young ideal, never supplied as a PSD certificate. -/
def centralProjector {k : ℕ} (d : ℕ) (lambda : QAlgorithms.Schur.Partition k k) :
    (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) :=
  (QAlgorithms.Schur.spechtCharacter lambda 1 / (k.factorial : ℂ)) •
    ∑ pi : Equiv.Perm (Fin k), QAlgorithms.Schur.spechtCharacter lambda pi⁻¹ •
      QAlgorithms.Schur.tensorPermutation d k pi

/-- Definition 4, Eq.32, p.9, with its original normalization. -/
def polarizedMap {d r : ℕ} (lambda : QAlgorithms.Schur.Partition (r+1) (r+1))
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  contractInputs (centralProjector d lambda) X

/-- Vertical tensor product followed by regrouping into input/output copies of
the global register, Eq.45, p.12. No factorization of the input is assumed. -/
def verticalOperators {n k : ℕ} (dims : Fin n → ℕ)
    (P : (j : Fin n) → (Matrix (Fin k → Fin (dims j)) (Fin k → Fin (dims j)) ℂ)) :
    (Matrix (Fin k → (∀ j, Fin (dims j))) (Fin k → (∀ j, Fin (dims j))) ℂ) :=
  fun a b => ∏ j, P j (fun i => a i j) (fun i => b i j)

/-- Mixed tensor product of the normalized maps, Eq.45–47, p.12. -/
def mixedMap {n r : ℕ} (dims : Fin n → ℕ)
    (lambda : Fin n → QAlgorithms.Schur.Partition (r+1) (r+1))
    (X : Fin r → (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  contractInputs (verticalOperators dims (fun j => centralProjector (dims j) (lambda j))) X

/-- Arbitrary, unnormalized rank-one operator |v><w|, Eq.33, p.10. -/
def rankOneOperator {I : Type*} (v w : I → ℂ) : (Matrix I I ℂ) := fun a b => v a * conj (w b)

/-- Scalar nonnegativity includes reality; discarding the imaginary part alone
would not express the source's scalar inequalities (pp.5,14). -/
def RealNonnegative (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

/-- Matrix element, with conjugate linearity in the bra, Eq.33. -/
def finiteMatrixElement {I : Type*} [Fintype I] (w : I → ℂ) (A : (Matrix I I ℂ)) (v : I → ℂ) : ℂ :=
  ∑ a, ∑ b, conj (w a) * A a b * v b

/-- Full multipartite block positivity, tested on all unnormalized pure product
vectors; by convexity this is exactly testing all fully separable states (p.14). -/
def FullyBlockPositive {d k : ℕ} (P : (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) : Prop :=
  P.IsHermitian ∧ ∀ v : Fin k → (Fin d → ℂ),
    RealNonnegative (Matrix.trace (P * tensorMatrices (fun i => rankOneOperator (v i) (v i))))

/-- Positivity on every tuple in the positive cone, pp.6,15. -/
def PositiveMap {I : Type*} [Fintype I] {r : ℕ}
    (f : (Fin r → (Matrix I I ℂ)) → (Matrix I I ℂ)) : Prop :=
  ∀ X, (∀ i, (X i).PosSemidef) → (f X).PosSemidef

/-- Diagonal-unitary invariance of the physical operator, pp.14–15. -/
def DiagonalUnitaryInvariant {d k : ℕ} (P : (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    tensorMatrices (fun _ : Fin k => (U : (Matrix (Fin d) (Fin d) ℂ))) * P *
      star (tensorMatrices (fun _ : Fin k => (U : (Matrix (Fin d) (Fin d) ℂ)))) = P

/-- Simultaneous-conjugation equivariance for arbitrary complex inputs, p.6 and
footnote 61 on p.28. -/
def ConjugationEquivariant {d r : ℕ} (f : (Fin r → (Matrix (Fin d) (Fin d) ℂ)) → (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) X,
    f (fun i => (U : (Matrix (Fin d) (Fin d) ℂ)) * X i * star (U : (Matrix (Fin d) (Fin d) ℂ))) =
      (U : (Matrix (Fin d) (Fin d) ℂ)) * f X * star (U : (Matrix (Fin d) (Fin d) ℂ))

/-- A multilinear trace monomial: one open word and finitely many traced words,
using each variable exactly once in total, Eq.60, p.15. Empty open word is I. -/
structure TraceMonomial (r : ℕ) where
  openWord : List (Fin r)
  closedWords : List (List (Fin r))
  closed_nonempty : ∀ w ∈ closedWords, w ≠ []
  labels_once : (openWord ++ closedWords.flatten).Perm (List.finRange r)

/-- Ordered matrix-word evaluation, Eq.27, p.9. -/
def matrixWord {I : Type*} [Fintype I] [DecidableEq I] {r : ℕ}
    (X : Fin r → (Matrix I I ℂ)) (w : List (Fin r)) : (Matrix I I ℂ) := (w.map X).prod

/-- Finite complex linear combination of the actual multilinear trace monomials;
raw syntax is not asserted to be unique (p.15). -/
abbrev TracePolynomial (r : ℕ) := List (ℂ × TraceMonomial r)

/-- Evaluation of the syntax; scalar trace-only terms multiply I (pp.6,15). -/
def evaluateTracePolynomial {I : Type*} [Fintype I] [DecidableEq I] {r : ℕ}
    (p : TracePolynomial r) (X : Fin r → (Matrix I I ℂ)) : (Matrix I I ℂ) :=
  (p.map fun t => (t.1 * (t.2.closedWords.map fun w => Matrix.trace (matrixWord X w)).prod) •
    matrixWord X t.2.openWord).sum

/-- Evaluated trace-polynomial maps, modulo all evaluation identities (p.15). -/
def IsTracePolynomial {d r : ℕ} (f : (Fin r → (Matrix (Fin d) (Fin d) ℂ)) → (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∃ p : TracePolynomial r, ∀ X, evaluateTracePolynomial p X = f X

/-- Fill one retained slot with a and the other slots with s, Eq.25, p.8. -/
def fillSlot {d k : ℕ} (q : Fin k) (a : Fin d)
    (s : {i : Fin k // i ≠ q} → Fin d) : Fin k → Fin d :=
  fun i => if h : i = q then a else s ⟨i,h⟩

/-- Ordinary partial trace retaining slot q, pp.8–9. -/
def partialTraceSlot {d k : ℕ} (q : Fin k) (M : (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  fun a b => ∑ s : {i : Fin k // i ≠ q} → Fin d, M (fillSlot q a s) (fillSlot q b s)

/-- Cycle written starting immediately after q and ending at q, Eq.27, p.9.
Mathlib omits fixed points, so they are supplied explicitly as singleton words. -/
def cycleList {k : ℕ} (pi : Equiv.Perm (Fin k)) (q : Fin k) : List (Fin k) :=
  if pi q = q then [q] else (pi.toList q).rotate 1

/-- Canonical cycle representatives: largest element in each cycle, including
fixed points. Products of their scalar traces do not require a list ordering (p.9). -/
def cycleLeaders {k : ℕ} (pi : Equiv.Perm (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter fun q => ∀ j ∈ cycleList pi q, j ≤ q

/-- Full trace-word product over all canonical cycles, Eq.30. -/
def closedCycleExpression {d k : ℕ} (pi : Equiv.Perm (Fin k))
    (X : Fin k → (Matrix (Fin d) (Fin d) ℂ)) : ℂ :=
  ∏ q ∈ cycleLeaders pi, Matrix.trace (matrixWord X (cycleList pi q))

/-- Traced closed cycles times the untraced word ending at the retained slot,
Eq.28, pp.8–9. Untraced words are never cyclically rotated without changing q. -/
def openCycleExpression {d k : ℕ} (pi : Equiv.Perm (Fin k)) (q : Fin k)
    (X : Fin k → (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (∏ c ∈ (cycleLeaders pi).filter (fun c => q ∉ cycleList pi c),
    Matrix.trace (matrixWord X (cycleList pi c))) • matrixWord X (cycleList pi q)

/-- Fully separable density matrices, using arbitrary finite convex combinations
of product density matrices; no bipartite-only relaxation (p.14). -/
def FullySeparableDensity {d k : ℕ} (rho : (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) : Prop :=
  ∃ m : ℕ, ∃ p : Fin m → ℝ, ∃ sigma : Fin m → Fin k → (Matrix (Fin d) (Fin d) ℂ),
    (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
    (∀ a j, QAlgorithms.IsDensityMatrix (sigma a j)) ∧
    rho = ∑ a, (p a : ℂ) • tensorMatrices (sigma a)

/-- The paper's optimal Werner witness: invariant, block positive, detecting
some entangled state, and saturating on a separable state (p.14). -/
def OptimalWernerWitness {d k : ℕ} (W : (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) : Prop :=
  DiagonalUnitaryInvariant W ∧ FullyBlockPositive W ∧
  (∃ rho, QAlgorithms.IsDensityMatrix rho ∧ ¬ FullySeparableDensity rho ∧ (Matrix.trace (W * rho)).re < 0) ∧
  (∃ rho, QAlgorithms.IsDensityMatrix rho ∧ FullySeparableDensity rho ∧ Matrix.trace (W * rho) = 0)

/-- The paper's saturation convention for optimal positive maps (p.15). -/
def Saturates {d r : ℕ} (f : (Fin r → (Matrix (Fin d) (Fin d) ℂ)) → (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  PositiveMap f ∧ ∃ X, (∀ i, (X i).PosSemidef ∧ X i ≠ 0) ∧
    ∃ v : Fin d → ℂ, v ≠ 0 ∧ (f X).mulVec v = 0

/-- Join reduced and complement coordinates, preserving subsystem positions
(Eqs.48–51, p.12). -/
def joinSubsystemCoordinates {J : Type*} (dims : J → ℕ) (S : Finset J)
    (a : (j : {j // j ∈ S}) → Fin (dims j.val))
    (e : (j : {j // j ∉ S}) → Fin (dims j.val)) : (∀ j, Fin (dims j)) :=
  fun j => if h : j ∈ S then a ⟨j,h⟩ else e ⟨j,h⟩

/-- Tensor identities into the complement in its original positions (p.12). -/
def embedSubsystemIdentity {J : Type*} [Fintype J] (dims : J → ℕ) (S : Finset J)
    (M : (Matrix ((j : {j // j ∈ S}) → Fin (dims j.val)) ((j : {j // j ∈ S}) → Fin (dims j.val)) ℂ)) : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  fun a b => if ∀ j, j ∉ S → a j = b j then
    M (fun j => a j.val) (fun j => b j.val) else 0

/-- Partial transpose on a specified set of tensor factors, p.12. -/
def transposeOn {J : Type*} (dims : J → ℕ) (T : J → Prop)
    (M : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  fun a b => M (fun j => if T j then b j else a j)
    (fun j => if T j then a j else b j)

/-- Shadow operator, Eq.48, p.12. -/
def shadow {n : ℕ} (dims : Fin n → ℕ) (T : Finset (Fin n))
    (rho : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  ∑ S : Finset (Fin n), ((-1 : ℂ) ^ (S ∩ T).card) • embedSubsystemIdentity dims S (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) rho S)

/-- Anticommutator used in Eq.49 (p.12). -/
def anti {I : Type*} [Fintype I] (A B : (Matrix I I ℂ)) : (Matrix I I ℂ) := A*B+B*A

/-- Eq.51 with the forced correction (2/3)^n, rather than printed (3/2)^n.
All products are formed on the reduced register before embedding (p.12). -/
def bilinearExpansion {n : ℕ} (dims : Fin n → ℕ)
    (rho mu : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  ((2/3 : ℂ)^n) • ∑ S : Finset (Fin n), ∑ A ∈ S.powerset,
    ((-1/2 : ℂ)^S.card) • embedSubsystemIdentity dims S
      (transposeOn (fun j : {j // j ∈ S} => dims j.val) (fun j => j.val ∈ A)
        (transposeOn (fun j : {j // j ∈ S} => dims j.val) (fun j => j.val ∈ A)
          (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) rho S) *
         transposeOn (fun j : {j // j ∈ S} => dims j.val) (fun j => j.val ∈ A)
          (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) mu S)))

/-- Explicit bipartite Eq.49, p.12. -/
def bipartiteExpansion (dims : Fin 2 → ℕ) (rho mu : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) :
    (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ) :=
  (1/9 : ℂ) • ((4 : ℂ) • (1 : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) +
    transposeOn dims (fun j => j = 0)
      (transposeOn dims (fun j => j = 0) rho * transposeOn dims (fun j => j = 0) mu) +
    transposeOn dims (fun j => j = 1)
      (transposeOn dims (fun j => j = 1) rho * transposeOn dims (fun j => j = 1) mu) -
    (2 : ℂ) • (embedSubsystemIdentity dims {0} (anti (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) rho {0}) (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) mu {0})) +
      embedSubsystemIdentity dims {1} (anti (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) rho {1}) (QAlgorithms.Papers.Independent.Gap48.P38.subsystemReduction (fun j => Fin (dims j)) mu {1}))) + anti rho mu)

/-- Unscaled reduction polynomial, p.10, Example 8. -/
def reductionPolynomial {d : ℕ} (X : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.trace X • (1 : (Matrix (Fin d) (Fin d) ℂ)) - X

/-- Unscaled three-box antisymmetric polynomial, Eq.40, p.11. -/
def antisymmetricThree {d : ℕ} (X Y : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (Matrix.trace X * Matrix.trace Y - Matrix.trace (X*Y)) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
    Matrix.trace X • Y - Matrix.trace Y • X + X*Y + Y*X

/-- Unscaled (2,1) polynomial, p.12. -/
def mixedThree {d : ℕ} (X Y : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (2 * Matrix.trace X * Matrix.trace Y) • (1 : (Matrix (Fin d) (Fin d) ℂ)) - X*Y-Y*X

/-- Unscaled tripartite-witness polynomial, Eq.67, p.16. -/
def witnessThree {d : ℕ} (X Y : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.trace (X*Y) • (1 : (Matrix (Fin d) (Fin d) ℂ)) + Matrix.trace X • Y +
    Matrix.trace Y • X-X*Y-Y*X

/-- The four literal fine-grained inequalities in Eq.54, p.13. -/
def finePolynomial {d : ℕ} (i : Fin 4) (X Y : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  if i = 0 then
    (2*Matrix.trace X*Matrix.trace Y+2*Matrix.trace (X*Y)) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
      Matrix.trace X • Y-Matrix.trace Y • X-X*Y-Y*X
  else if i = 1 then
    (2*Matrix.trace X*Matrix.trace Y-2*Matrix.trace (X*Y)) • (1 : (Matrix (Fin d) (Fin d) ℂ)) +
      Matrix.trace X • Y+Matrix.trace Y • X-X*Y-Y*X
  else if i = 2 then
    (2*Matrix.trace X*Matrix.trace Y-Matrix.trace (X*Y)) • (1 : (Matrix (Fin d) (Fin d) ℂ)) +
      (2*Matrix.trace X) • Y-Matrix.trace Y • X-X*Y-Y*X
  else
    (2*Matrix.trace X*Matrix.trace Y+Matrix.trace (X*Y)) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
      (2*Matrix.trace X) • Y+Matrix.trace Y • X-X*Y-Y*X

/-- Four normalized physical projectors, from the two decompositions above Eq.54.
The sum of either pair is P_(2,1); each displayed polynomial is six times its map. -/
def fineProjector (d : ℕ) (i : Fin 4) : (Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) :=
  let T := QAlgorithms.Schur.tensorPermutation d 3
  let c : Equiv.Perm (Fin 3) := (List.finRange 3).formPerm
  let s : Equiv.Perm (Fin 3) := if i.val < 2 then Equiv.swap 0 1 else Equiv.swap 1 2
  let e : ℂ := if i.val % 2 = 0 then 1 else -1
  (1/6 : ℂ) • ((2 : ℂ) • (1 : (Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ)) +
    e • ((3 : ℂ) • T s - (T (Equiv.swap 0 1)+T (Equiv.swap 0 2)+T (Equiv.swap 1 2))) -
    T c-T c⁻¹)

/-- Motzkin matrix polynomial, Eq.70, p.17. -/
def motzkin {d : ℕ} (A B : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  A*B^4*A+A^2*B^2*A^2-(3 : ℂ) • (A*B^2*A)+1

/-- Exact square decomposition printed in Eq.71, p.17. -/
def motzkinSquares {d : ℕ} (A B : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (A^2-A)*B^2*(A^2-A) +
    (A*B^2+A^2-(2 : ℂ) • A)*(B^2*A+A^2-(2 : ℂ) • A) +
    (1-A)*(1+(2 : ℂ) • A-A^2)*(1-A)

/-- Homogenized Motzkin formula, Eq.72, p.17. No division by a trace. -/
def homogeneousMotzkin {d : ℕ} (A B : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (Matrix.trace A)^2 • (A*B^4*A) + (Matrix.trace B)^2 • (A^2*B^2*A^2) -
    (3*(Matrix.trace A)^2*(Matrix.trace B)^2) • (A*B^2*A) +
    ((Matrix.trace A)^4*(Matrix.trace B)^4) • (1 : (Matrix (Fin d) (Fin d) ℂ))

/-- Empty words and zero inputs retain their literal algebraic meanings. -/
example {d r : ℕ} (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) : matrixWord X [] = 1 := rfl

example {d : ℕ} (B : (Matrix (Fin d) (Fin d) ℂ)) : motzkin (0 : (Matrix (Fin d) (Fin d) ℂ)) B = 1 := by
  simp [motzkin]

example {d : ℕ} (B : (Matrix (Fin d) (Fin d) ℂ)) : homogeneousMotzkin (0 : (Matrix (Fin d) (Fin d) ℂ)) B = 0 := by
  simp [homogeneousMotzkin]

example {k : ℕ} (q : Fin k) : cycleList (1 : Equiv.Perm (Fin k)) q = [q] := by
  simp [cycleList]

/-- Literal Table II entry for [3,1], with trace-only terms multiplying I
(PDF p.25, table introduced p.24). -/
def tableFour31 {d : ℕ} (A B C : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (3*Matrix.trace A*Matrix.trace B*Matrix.trace C + Matrix.trace A*Matrix.trace (C*B) +
    Matrix.trace (B*A)*Matrix.trace C + Matrix.trace (C*A)*Matrix.trace B) •
      (1 : (Matrix (Fin d) (Fin d) ℂ)) +
    (Matrix.trace A*Matrix.trace B) • C + (Matrix.trace C*Matrix.trace A) • B -
    Matrix.trace (B*A) • C-C*B*A-B*A*C-C*A*B -
    Matrix.trace (C*A) • B-B*C*A-A*B*C +
    (Matrix.trace B*Matrix.trace C) • A-A*C*B-Matrix.trace (C*B) • A

/-- Literal Table II entry for [2,2] (PDF p.25). -/
def tableFour22 {d : ℕ} (A B C : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (2*Matrix.trace A*Matrix.trace B*Matrix.trace C-Matrix.trace (C*B*A)-
    Matrix.trace (B*C*A)) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
    Matrix.trace A • (C*B)-Matrix.trace A • (B*C) +
    (2*Matrix.trace (B*A)) • C-Matrix.trace C • (B*A)-Matrix.trace B • (C*A) +
    (2*Matrix.trace (C*A)) • B-Matrix.trace C • (A*B)-Matrix.trace B • (A*C) +
    (2*Matrix.trace (C*B)) • A

/-- Literal Table II entry for [2,1,1] (PDF p.25). -/
def tableFour211 {d : ℕ} (A B C : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (3*Matrix.trace A*Matrix.trace B*Matrix.trace C-Matrix.trace A*Matrix.trace (C*B)-
    Matrix.trace (B*A)*Matrix.trace C-Matrix.trace (C*A)*Matrix.trace B) •
      (1 : (Matrix (Fin d) (Fin d) ℂ)) -
    (Matrix.trace A*Matrix.trace B) • C-(Matrix.trace C*Matrix.trace A) • B -
    Matrix.trace (B*A) • C+C*B*A+B*A*C+C*A*B -
    Matrix.trace (C*A) • B+B*C*A+A*B*C -
    (Matrix.trace B*Matrix.trace C) • A+A*C*B-Matrix.trace (C*B) • A

/-- Literal Table II entry for [1,1,1,1] (PDF p.25). -/
def tableFour1111 {d : ℕ} (A B C : (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  (Matrix.trace A*Matrix.trace B*Matrix.trace C-Matrix.trace A*Matrix.trace (C*B)-
    Matrix.trace (B*A)*Matrix.trace C+Matrix.trace (C*B*A)+Matrix.trace (B*C*A)-
    Matrix.trace (C*A)*Matrix.trace B) • (1 : (Matrix (Fin d) (Fin d) ℂ)) -
    (Matrix.trace A*Matrix.trace B) • C + Matrix.trace A • (C*B) +
    Matrix.trace A • (B*C)-(Matrix.trace C*Matrix.trace A) • B +
    Matrix.trace (B*A) • C-C*B*A-B*A*C+Matrix.trace C • (B*A)-C*A*B +
    Matrix.trace B • (C*A)+Matrix.trace (C*A) • B-B*C*A-A*B*C +
    Matrix.trace C • (A*B)+Matrix.trace B • (A*C) -
    (Matrix.trace B*Matrix.trace C) • A-A*C*B+Matrix.trace (C*B) • A

/-- The properties asserted for each Table II map in the Appendix B introduction
(PDF p.24): positive, dimension-dependent vanishing, equivariant, completely
copositive, and tensor-stable, with positive dimensions and arbitrary ancillas. -/
def TableProperties {r : ℕ} (lambda : QAlgorithms.Schur.Partition (r+1) (r+1)) : Prop :=
  (∀ (d : ℕ), 0 < d →
    PositiveMap (polarizedMap (d := d) lambda) ∧
    (d < lambda.val.colLen 0 → ∀ X : Fin r → (Matrix (Fin d) (Fin d) ℂ), polarizedMap lambda X = 0) ∧
    ConjugationEquivariant (polarizedMap (d := d) lambda) ∧
    (∀ (m : ℕ), 0 < m → ∀ Z : (Matrix ((Fin r → Fin d) × Fin m) ((Fin r → Fin d) × Fin m) ℂ), Z.PosSemidef →
      (copositiveAmplification (centralProjector d lambda) m Z).PosSemidef)) ∧
  (∀ (n : ℕ) (dims : Fin n → ℕ), (∀ j, 0 < dims j) →
    PositiveMap (mixedMap dims (fun _ => lambda)))

/-- The finite group algebra in its full coefficient-function coordinates
(pp.18–21). Coefficients are constant complex numbers, independent of all inputs. -/
abbrev GroupCoefficients (k : ℕ) := Equiv.Perm (Fin k) → ℂ

/-- Group-algebra multiplication in coefficient coordinates (pp.20–21). -/
def coefficientProduct {k : ℕ} (a b : GroupCoefficients k) : GroupCoefficients k :=
  fun pi => ∑ sigma : Equiv.Perm (Fin k), a sigma*b (sigma⁻¹*pi)

/-- Fixed linear extension of the physical permutation action, pp.8,20. -/
def groupOperator {k : ℕ} (d : ℕ) (a : GroupCoefficients k) : (Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) :=
  ∑ pi : Equiv.Perm (Fin k), a pi • QAlgorithms.Schur.tensorPermutation d k pi

/-- Character-computed central idempotent coefficients, Eq.A16 and Eq.31.
These are independent of the physical dimension (pp.9,24). -/
def centralCoefficients {k : ℕ} (lambda : QAlgorithms.Schur.Partition k k) :
    GroupCoefficients k :=
  fun pi => QAlgorithms.Schur.spechtCharacter lambda 1 / (k.factorial : ℂ) *
    QAlgorithms.Schur.spechtCharacter lambda pi⁻¹

/-- The actual sum of isotypic ideals for shapes with more than d rows, Eq.C2,
p.26. It is constructed as the sum of the central-idempotent-generated ideals,
not defined as the physical representation's kernel. -/
def InAntisymmetricIdeal {k : ℕ} (d : ℕ) (a : GroupCoefficients k) : Prop :=
  ∃ b : QAlgorithms.Schur.Partition k k → GroupCoefficients k,
    ∀ pi, a pi = ∑ lambda : QAlgorithms.Schur.Partition k k,
      if d < lambda.val.colLen 0 then
        coefficientProduct (centralCoefficients lambda) (b lambda) pi else 0

/-- First r slots are matrix inputs, last t slots are marked tensor outputs
(Eqs.81–85 and C3–C5, pp.18–19,26). -/
def inputSlot {r t : ℕ} (i : Fin r) : Fin (r+t) := ⟨i.val, by omega⟩

/-- Output marker in the shared input/output register (pp.18–19,26). -/
def outputSlot {r t : ℕ} (j : Fin t) : Fin (r+t) := ⟨r+j.val, by omega⟩

/-- Ordered concatenation of input and output coordinates (pp.18–19,26). -/
def joinSlots {I : Type*} {r t : ℕ} (x : Fin r → I) (a : Fin t → I) : Fin (r+t) → I :=
  fun i => if h : i.val < r then x ⟨i.val,h⟩ else a ⟨i.val-r,by omega⟩

/-- C1 with its last variable still present, p.26. -/
def gPolynomial {d r : ℕ} (a : GroupCoefficients (r+1))
    (X : Fin (r+1) → (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin d) (Fin d) ℂ) :=
  partialTraceSlot (Fin.last r) (groupOperator d a * tensorMatrices X)

/-- All-t-output contraction with identities in the output slots (C3–C5, p.26).
The coordinate formula fixes the C5 alpha/beta, k−t argument and retained-slot typos. -/
def hPolynomial {d r t : ℕ} (a : GroupCoefficients (r+t))
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ) :=
  fun u v => ∑ x : Fin r → Fin d, ∑ y : Fin r → Fin d,
    groupOperator d a (joinSlots x u) (joinSlots y v) * ∏ i, X i (y i) (x i)

/-- Multilinear tensor-trace monomial with t ordered output words and arbitrary
closed input trace words. Every input label appears once overall. Empty output
words give identity factors (pp.6,18–19,25–26). -/
structure TensorTraceMonomial (r t : ℕ) where
  outputWords : Fin t → List (Fin r)
  closedWords : List (List (Fin r))
  closed_nonempty : ∀ w ∈ closedWords, w ≠ []
  labels_once : ((List.ofFn outputWords).flatten ++ closedWords.flatten).Perm (List.finRange r)

/-- Formal finite tensor-trace polynomials, before taking evaluation identities
(pp.6,18–19,25–26). -/
abbrev TensorTracePolynomial (r t : ℕ) := List (ℂ × TensorTraceMonomial r t)

/-- Ordered tensor-word evaluation; closed words supply scalar ordinary traces
(pp.6,18–19). -/
def evaluateTensorTrace {d r t : ℕ} (p : TensorTracePolynomial r t)
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) : (Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ) :=
  (p.map fun term =>
    (term.1 * (term.2.closedWords.map fun w => Matrix.trace (matrixWord X w)).prod) •
      tensorMatrices (fun j => matrixWord X (term.2.outputWords j))).sum

/-- Noncommutative polynomial functions (Definition 29, p.25); evaluation is
from actual words, not an arbitrary function with a desired output certificate. -/
def IsNoncommutativePolynomial {d r : ℕ} (f : (Fin r → (Matrix (Fin d) (Fin d) ℂ)) → (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∃ p : List (ℂ × List (Fin r)),
    ∀ X, (p.map fun term => term.1 • matrixWord X term.2).sum = f X

/-- Pure tensor-polynomial functions are the no-closed-trace subcase of the
formal tensor-word evaluation (Definition 29, p.25). -/
def IsTensorPolynomial {d r t : ℕ}
    (f : (Fin r → (Matrix (Fin d) (Fin d) ℂ)) → (Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ)) : Prop :=
  ∃ p : TensorTracePolynomial r t,
    (∀ term ∈ p, term.2.closedWords = []) ∧ ∀ X, evaluateTensorTrace p X = f X

/-- Concrete permutation for a tensor trace monomial: close each output word
with its own output marker, close the trace words, then invert the disjoint cycle
product to match the paper's T convention (pp.9,18–19). -/
def monomialPermutation {r t : ℕ} (term : TensorTraceMonomial r t) :
    Equiv.Perm (Fin (r+t)) :=
  (((List.ofFn fun j : Fin t =>
      ((term.outputWords j).map (inputSlot (t := t)) ++ [outputSlot (r := r) j]).formPerm).prod) *
    ((term.closedWords.map fun w => (w.map (inputSlot (t := t))).formPerm).prod))⁻¹

/-- Constant-coefficient group-algebra expansion beta constructed from formal
words, not selected separately for each evaluated input (Eqs.81,84, pp.18–19). -/
def tensorPermutationExpansion {r t : ℕ} (p : TensorTracePolynomial r t) :
    GroupCoefficients (r+t) :=
  fun pi => (p.map fun term => if pi = monomialPermutation term.2 then term.1 else 0).sum

/-- Scalar pure trace monomial with each input label appearing once (pp.6,18). -/
structure PureTraceMonomial (r : ℕ) where
  closedWords : List (List (Fin r))
  closed_nonempty : ∀ w ∈ closedWords, w ≠ []
  labels_once : closedWords.flatten.Perm (List.finRange r)

/-- Scalar multilinear trace polynomials, pp.6,18. -/
abbrev PureTracePolynomial (r : ℕ) := List (ℂ × PureTraceMonomial r)

/-- Scalar closed-word evaluation (pp.6,18). -/
def evaluatePureTrace {d r : ℕ} (p : PureTracePolynomial r)
    (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) : ℂ :=
  (p.map fun term => term.1 * (term.2.closedWords.map fun w => Matrix.trace (matrixWord X w)).prod).sum

/-- Lift a fixed output permutation by its disjoint cycles onto the output
markers; singleton cycles are retained in the cycle convention (p.19). -/
def outputPermutation {r t : ℕ} (rho : Equiv.Perm (Fin t)) : Equiv.Perm (Fin (r+t)) :=
  (List.ofFn fun j : Fin t => if j ∈ cycleLeaders rho then
    ((cycleList rho j).map (outputSlot (r := r))).formPerm else 1).prod

/-- Permutation representing a scalar pure-trace monomial times a fixed output
permutation. The input cycle factors are inverted, the output action is not (p.19). -/
def pureTracePermutation {r t : ℕ} (term : PureTraceMonomial r)
    (rho : Equiv.Perm (Fin t)) : Equiv.Perm (Fin (r+t)) :=
  ((term.closedWords.map fun w => (w.map (inputSlot (t := t))).formPerm).prod)⁻¹ *
    outputPermutation rho

/-- Constant-coefficient gamma after expanding the scalar invariant into closed
trace words. This replaces the input-dependent group-algebra shorthand in Eq.83
(PDF p.19), without making that shorthand a definition. -/
def pureTraceExpansion {r t : ℕ} (p : PureTracePolynomial r)
    (rho : Equiv.Perm (Fin t)) : GroupCoefficients (r+t) :=
  fun pi => (p.map fun term => if pi = pureTracePermutation term.2 rho then term.1 else 0).sum

/-- Full-support single nontrivial cycle (Theorem 30(i)–(iii), p.26). -/
def FullNontrivialCycle {k : ℕ} (pi : Equiv.Perm (Fin k)) : Prop :=
  (∀ i, pi i ≠ i) ∧ ∀ i j : Fin k, j ∈ cycleList pi i

/-- Exactly t cycles with exactly one marked output apiece and no extra
input-only cycles. Output actions are required nontrivial where printed in
Theorem 30(iv)–(v), p.26; empty words remain allowed in the general syntax. -/
def OutputMarkedCycles {r t : ℕ} (pi : Equiv.Perm (Fin (r+t))) : Prop :=
  (∀ j : Fin t, pi (outputSlot j) ≠ outputSlot j) ∧
  (∀ j l : Fin t, outputSlot l ∈ cycleList pi (outputSlot j) ↔ l = j) ∧
  (∀ i : Fin (r+t), ∃ j : Fin t, i ∈ cycleList pi (outputSlot j))

/-- A closed prescribed output permutation, with input-only remaining cycles
(Theorem 30(iv), C4, p.26). -/
def ClosedOutputAction {r t : ℕ} (rho : Equiv.Perm (Fin t))
    (pi : Equiv.Perm (Fin (r+t))) : Prop :=
  ∀ j : Fin t, pi (outputSlot j) = outputSlot (rho j)

/-- Empty formal sums evaluate to zero, without introducing phantom terms. -/
example {d r t : ℕ} (X : Fin r → (Matrix (Fin d) (Fin d) ℂ)) :
    evaluateTensorTrace ([] : TensorTracePolynomial r t) X = 0 := rfl

example {r t : ℕ} : tensorPermutationExpansion ([] : TensorTracePolynomial r t) = 0 := rfl

/-- Empty-family tensor conventions, pp.6,12. -/
example (dims : Fin 0 → ℕ) (X : (j : Fin 0) → (Matrix (Fin (dims j)) (Fin (dims j)) ℂ))
    (a b : (∀ j, Fin (dims j))) : tensorFamily dims X a b = 1 := by
  simp [tensorFamily]

example {k : ℕ} (dims : Fin 0 → ℕ)
    (P : (j : Fin 0) → (Matrix (Fin k → Fin (dims j)) (Fin k → Fin (dims j)) ℂ))
    (a b : Fin k → (∀ j, Fin (dims j))) : verticalOperators dims P a b = 1 := by
  simp [verticalOperators]

example {k : ℕ} (d : ℕ) : groupOperator d (0 : GroupCoefficients k) = 0 := by
  simp [groupOperator]

/-- Product-input specialization of the full linear extension, Eq.53, p.13. -/
example {I : Type*} [Fintype I] {r : ℕ}
    (P : (Matrix (Fin (r+1) → I) (Fin (r+1) → I) ℂ)) (X : Fin r → (Matrix I I ℂ)) :
    linearContraction P (tensorMatrices X) = contractInputs P X := rfl

example {I : Type*} [Fintype I] {r : ℕ} (X : Fin r → (Matrix I I ℂ)) :
    contractInputs (0 : (Matrix (Fin (r+1) → I) (Fin (r+1) → I) ℂ)) X = 0 := by
  ext a b
  simp [contractInputs]

example {J : Type*} (dims : J → ℕ) (M : (Matrix ((∀ j, Fin (dims j))) ((∀ j, Fin (dims j))) ℂ)) :
    transposeOn dims (fun _ => False) M = M := by
  ext a b
  simp [transposeOn]

end QAlgorithms.Papers.Independent.Extend50.P13


