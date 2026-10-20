-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20
-- name    : QAlgorithms_Papers_Independent_Frontier30_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T18:30:12.58986+00:00
-- url     : https://prove2.me/theorems/41d42c93-1186-4f88-845f-c0930f7c19e6
-- title:
--   Definitions for Dividing Quantum Channels
-- statement:
--   The objects the formalized statements of *Dividing Quantum Channels* (arXiv:math-ph/0611057) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Cone`: PDF p.4: select the positive or completely positive cone.
--   - `InClass`: PDF p.4: the corresponding trace-preserving class.
--   - `Channel`: PDF p.4: channels are Schrödinger-picture CPTP maps.
--   - `complexDet`: PDF p.6: the full complex determinant, before taking its real part.
--   - `determinant`: PDF p.6: the real value of the determinant for Hermiticity-preserving maps. Statements asserting positivity also assert that the imaginary part vanishes.
--   - `superTrace`: PDF p.5: trace on Hilbert--Schmidt space.
--   - `jamiolkowskiState`: PDF p.4, Eq.(3): the accepted output-first Choi matrix divided by d. The frozen unnormalized Choi definition is preserved.
--   - `krausRank`: PDF p.4 and p.12 footnote 5: Choi rank, including for positive non-CP maps.
--   - `twoSidedMap`: PDF p.4: continuous adapter of the accepted two-sided multiplication map.
--   - `IsUnitaryConjugation`: PDF p.5 footnote 2: a unitary conjugation, not an arbitrary invertible filter.
--   - `FilterMap`: PDF pp.12,15: invertible CP filters with exactly one Kraus operator.
--   - `fromCoefficients`: PDF p.4: continuous adapter of the accepted coefficient constructor. No separate linearity proof or second coefficient convention is introduced.
--   - `continuousTranspose`: PDF p.7: continuous adapter of the accepted complex-linear transposition.
--   - `TransposeEquivalent`: PDF pp.6--7: transposition up to unitary pre- and post-conjugation.
--   - `Maximizer`: PDF p.5: a genuine maximizing unitary for right composition TU.
--   - `canonicalGenerator`: PDF p.4, Eq.(5): continuous coordinate adapter of the accepted Kossakowski action. Basis, positivity and Hermiticity constraints are imposed at use sites; the accepted arbitrary-jump LindbladData is not a canonical traceless-basis object.
--   - `hsOperatorNorm`: PDF p.4, Eq.(2): induced Hilbert--Schmidt norm, computed on matrix units. This is not the norm of a map acting on spectral-normed input matrices.
--   - `IsGenerator`: PDF p.4: a semigroup generator, characterized by all its CPTP exponentials.
--   - `PurelyDissipative`: PDF p.4: zero Hamiltonian in a traceless Hilbert--Schmidt orthonormal basis.
--   - `Markovian`: PDF p.4: an element of a continuous CPTP one-parameter semigroup.
--   - `Indivisible`: PDF p.11, Definition 8: all factorizations have a unitary-conjugation factor.
--   - `Divisible`: PDF p.11: an actual nontrivial two-factor decomposition in the chosen class.
--   - `fineProducts`: PDF p.13: exact arbitrarily fine products; a list preserves composition order.
--   - `Infinitesimal`: PDF p.13, Definition 14: ambient norm closure, retaining singular endpoints.
--   - `InfiniteDivisible`: PDF p.13: roots in the CPTP class for every positive integer order.
--   - `evolutionEndpoints`: PDF p.13: the set J, with continuous two-parameter CP evolutions. No differentiability or generator regularity is required.
--   - `Propagates`: PDF pp.15--16, Eq.(31): an initial-value propagator on the closed unit interval.
--   - `cornerTranspose`: PDF p.7: the corner transpose exchanges only the two distinct corner entries. The example theorem restricts d to at least two.
--   - `negativeChannel`: PDF p.7, Eq.(14): linear extension includes I tr(rho), not just I.
--   - `pauliEigenvectors`: PDF pp.7--8: six normalized X,Y,Z eigenvectors, phases fixed for concreteness.
--   - `dualIdentity`: PDF p.12: adjoint applied to I, a d-by-d matrix (not a superoperator determinant).
--   - `canonicalChannel`: PDF pp.17--18, Eq.(37): the two explicitly constructed Kraus operators.
--   - `CanonicalData`: PDF p.18, Eq.(38): phase conventions and the trace-preserving constraint.
--   - `ClassThree`: PDF p.18, Definition 21: canonical class 3 excludes classes 1 and 2.
--   - `classInput`: PDF pp.18--19, Eq.(41): normalized input state with c1 in (0,1).
--   - `classOutput`: PDF pp.18--19, Eq.(41): y is fixed by normalization; the output's second component is x c1.
--   - `pauliFin`: PDF p.16: computational-basis reindexing of the frozen X,Y,Z Pauli basis.
--   - `pauliBlock`: PDF p.16, Eq.(32): the real 3-by-3 Pauli block.
--   - `translation`: PDF p.16, Eq.(32): the translation part of the full Pauli representation.
--   - `DiagonalBranch`: PDF pp.16--17: diagonal Lorentz branch includes unitality, not just diagonal pauliBlock.
--   - `OtherBranch`: PDF p.17, Theorem 18: the two other normal-form branches, including reset.
--   - `NormalRepresentative`: PDF pp.16--17: normal forms are independently defined by invertible CP filters.
--   - `HasDiagonalNormalForm`: PDF p.19, Theorem 23: existence of a diagonal Lorentz normal form.
--   - `SingularCriterion`: PDF p.21, Eq.(51): s_min(pauliBlock)^2 >= det(pauliBlock) > 0, without a default-valued infimum. The quadratic inequality for every real vector is exactly the least-singular-value bound.
-- source:
--   Dividing Quantum Channels, arXiv:math-ph/0611057v3, https://arxiv.org/abs/math-ph/0611057v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

/-!
Statements from Wolf and Cirac, Dividing Quantum Channels, arXiv:math-ph/0611057v3.
The quantitative norm is explicitly hsOperatorNorm: the Euclidean operator norm
of the matrix-unit coefficients, exactly Eq.(2). Ambient topology is the accepted
finite-dimensional continuous-map topology, which gives the same closures.
All new interfaces are paper-local. Theorem 19 is deferred: see HARD.md.
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

-- These names denote pinned accepted definitions, not local copies.
open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)
open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

-- Accepted matrix-unit coordinates on the action of a superoperator.
local notation "coefficients" =>
  QAlgorithms.Papers.Independent.Dependency50.P12.superOfAction

/-- PDF p.4: select the positive or completely positive cone. -/
def Cone {d : ℕ} (completely : Bool) (T : Super d) : Prop :=
  if completely then QAlgorithms.Entanglement.IsCompletelyPositive T.toLinearMap
  else QAlgorithms.Papers.Independent.Dependency50.P28.Positive T.toLinearMap

/-- PDF p.4: the corresponding trace-preserving class. -/
def InClass {d : ℕ} (completely : Bool) (T : Super d) : Prop :=
  Cone completely T ∧
    QAlgorithms.Papers.Independent.Dependency50.P28.TP T.toLinearMap

/-- PDF p.4: channels are Schrödinger-picture CPTP maps. -/
def Channel {d : ℕ} (T : Super d) : Prop := InClass true T

/-- PDF p.6: the full complex determinant, before taking its real part. -/
def complexDet {d : ℕ} (T : Super d) : ℂ := (coefficients T).det

/-- PDF p.6: the real value of the determinant for Hermiticity-preserving maps.
Statements asserting positivity also assert that the imaginary part vanishes. -/
def determinant {d : ℕ} (T : Super d) : ℝ := (complexDet T).re

/-- PDF p.5: trace on Hilbert--Schmidt space. -/
def superTrace {d : ℕ} (T : Super d) : ℂ := QAlgorithms.Papers.Independent.Information100.P59.superoperatorTrace T

/-- PDF p.4, Eq.(3): the accepted output-first Choi matrix divided by d.
The frozen unnormalized Choi definition is preserved. -/
def jamiolkowskiState {d : ℕ} (T : Super d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (d : ℂ)⁻¹ • QAlgorithms.Papers.Independent.Information100.P50.choiMatrix T.toLinearMap

/-- PDF p.4 and p.12 footnote 5: Choi rank, including for positive non-CP maps. -/
def krausRank {d : ℕ} (T : Super d) : ℕ := (jamiolkowskiState T).rank

/-- PDF p.4: continuous adapter of the accepted two-sided multiplication map. -/
def twoSidedMap {d : ℕ} (A B : Mat d) : Super d :=
  LinearMap.toContinuousLinearMap
    (QAlgorithms.Papers.Independent.Dependency50.P16.sandwich A B)

/-- PDF p.5 footnote 2: a unitary conjugation, not an arbitrary invertible filter. -/
def IsUnitaryConjugation {d : ℕ} (T : Super d) : Prop :=
  ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
    T = twoSidedMap (U : Mat d) (U : Mat d)ᴴ

/-- PDF pp.12,15: invertible CP filters with exactly one Kraus operator. -/
def FilterMap {d : ℕ} (T : Super d) : Prop :=
  ∃ A : Mat d, IsUnit A ∧ T = twoSidedMap A Aᴴ

/-- PDF p.4: continuous adapter of the accepted coefficient constructor.
No separate linearity proof or second coefficient convention is introduced. -/
def fromCoefficients {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Super d :=
  LinearMap.toContinuousLinearMap
    (QAlgorithms.Papers.Independent.Information100.P50.coefficientMap
      (fun i j a b => M (i,j) (a,b)))

/-- PDF p.7: continuous adapter of the accepted complex-linear transposition. -/
def continuousTranspose (d : ℕ) : Super d :=
  LinearMap.toContinuousLinearMap
    (QAlgorithms.Papers.Independent.Dependency50.P49.transposeMap d)

/-- PDF pp.6--7: transposition up to unitary pre- and post-conjugation. -/
def TransposeEquivalent {d : ℕ} (T : Super d) : Prop :=
  ∃ U V : Super d, IsUnitaryConjugation U ∧ IsUnitaryConjugation V ∧ T = U * continuousTranspose d * V

/-- PDF p.5: a genuine maximizing unitary for right composition TU. -/
def Maximizer {d : ℕ} (T U : Super d) : Prop :=
  IsUnitaryConjugation U ∧ ∀ V : Super d, IsUnitaryConjugation V →
    (superTrace (T * V)).re ≤ (superTrace (T * U)).re

/-- PDF p.4, Eq.(5): continuous coordinate adapter of the accepted Kossakowski
action. Basis, positivity and Hermiticity constraints are imposed at use sites;
the accepted arbitrary-jump LindbladData is not a canonical traceless-basis object. -/
def canonicalGenerator {d : ℕ} (F : Fin (d ^ 2 - 1) → Mat d) (H : Mat d)
    (G : Matrix (Fin (d ^ 2 - 1)) (Fin (d ^ 2 - 1)) ℂ) : Super d :=
  fromCoefficients (coefficients
    (QAlgorithms.Papers.Independent.Information100.P59.kossakowskiAction F H G))

/-- PDF p.4, Eq.(2): induced Hilbert--Schmidt norm, computed on matrix units.
This is not the norm of a map acting on spectral-normed input matrices. -/
def hsOperatorNorm {d : ℕ} (T : Super d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ) (coefficients T)‖

/-- PDF p.4: a semigroup generator, characterized by all its CPTP exponentials. -/
def IsGenerator {d : ℕ} (L : Super d) : Prop :=
  ∀ t : ℝ, 0 ≤ t → Channel (NormedSpace.exp (t • L))

/-- PDF p.4: zero Hamiltonian in a traceless Hilbert--Schmidt orthonormal basis. -/
def PurelyDissipative {d : ℕ} (L : Super d) : Prop :=
  ∃ (F : Fin (d ^ 2 - 1) → Mat d)
      (G : Matrix (Fin (d ^ 2 - 1)) (Fin (d ^ 2 - 1)) ℂ),
    (∀ a, (F a).trace = 0) ∧
    (∀ a b, ((F a)ᴴ * F b).trace = if a = b then 1 else 0) ∧
    G.PosSemidef ∧ L = canonicalGenerator F 0 G

/-- PDF p.4: an element of a continuous CPTP one-parameter semigroup. -/
def Markovian {d : ℕ} (T : Super d) : Prop :=
  ∃ L : Super d, IsGenerator L ∧ T = NormedSpace.exp L

/-- PDF p.11, Definition 8: all factorizations have a unitary-conjugation factor. -/
def Indivisible {d : ℕ} (completely : Bool) (T : Super d) : Prop :=
  InClass completely T ∧ ∀ A B : Super d,
    InClass completely A → InClass completely B → T = A * B → IsUnitaryConjugation A ∨ IsUnitaryConjugation B

/-- PDF p.11: an actual nontrivial two-factor decomposition in the chosen class. -/
def Divisible {d : ℕ} (completely : Bool) (T : Super d) : Prop :=
  InClass completely T ∧ ∃ A B : Super d,
    InClass completely A ∧ InClass completely B ∧ T = A * B ∧ ¬ IsUnitaryConjugation A ∧ ¬ IsUnitaryConjugation B

/-- PDF p.13: exact arbitrarily fine products; a list preserves composition order. -/
def fineProducts (d : ℕ) (completely markov : Bool) : Set (Super d) :=
  {T | InClass completely T ∧ ∀ eps : ℝ, 0 < eps → ∃ factors : List (Super d),
    (∀ A ∈ factors, InClass completely A ∧ hsOperatorNorm (A - 1) ≤ eps ∧
      (markov = true → Markovian A)) ∧ factors.prod = T}

/-- PDF p.13, Definition 14: ambient norm closure, retaining singular endpoints. -/
def Infinitesimal {d : ℕ} (completely : Bool) (T : Super d) : Prop :=
  T ∈ closure (fineProducts d completely false)

/-- PDF p.13: roots in the CPTP class for every positive integer order. -/
def InfiniteDivisible {d : ℕ} (T : Super d) : Prop :=
  Channel T ∧ ∀ n : ℕ, 0 < n → ∃ R : Super d, Channel R ∧ R ^ n = T

/-- PDF p.13: the set J, with continuous two-parameter CP evolutions.
No differentiability or generator regularity is required. -/
def evolutionEndpoints (d : ℕ) : Set (Super d) :=
  {T | ∃ (horizon : ℝ) (E : ℝ × ℝ → Super d), 0 < horizon ∧
    ContinuousOn E (Set.Icc (0 : ℝ) horizon ×ˢ Set.Icc (0 : ℝ) horizon) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) horizon, ∀ t ∈ Set.Icc (0 : ℝ) horizon,
      s ≤ t → Channel (E (t,s))) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) horizon, E (s,s) = 1) ∧
    (∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ horizon →
      E (c,b) * E (b,a) = E (c,a)) ∧ T = E (horizon,0)}

/-- PDF pp.15--16, Eq.(31): an initial-value propagator on the closed unit interval. -/
def Propagates {d : ℕ} (L X : ℝ → Super d) : Prop :=
  X 0 = 1 ∧ ContinuousOn X (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt X (L t * X t) (Set.Icc (0 : ℝ) 1) t

/-- PDF p.7: the corner transpose exchanges only the two distinct corner entries.
The example theorem restricts d to at least two. -/
def cornerTranspose (d : ℕ) : Super d :=
  fromCoefficients (fun i j =>
    if (i.1.val = 0 ∧ i.2.val + 1 = d) ∨ (i.2.val = 0 ∧ i.1.val + 1 = d)
    then if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0
    else if i = j then 1 else 0)

/-- PDF p.7, Eq.(14): linear extension includes I tr(rho), not just I. -/
def negativeChannel (d : ℕ) : Super d :=
  ((d + 1 : ℂ)⁻¹) • (cornerTranspose d +
    fromCoefficients (fun i j => if i.1 = i.2 ∧ j.1 = j.2 then 1 else 0))

/-- PDF pp.7--8: six normalized X,Y,Z eigenvectors, phases fixed for concreteness. -/
def pauliEigenvectors : Fin 6 → (Fin 2 → ℂ) :=
  ![![((Real.sqrt 2)⁻¹ : ℂ), ((Real.sqrt 2)⁻¹ : ℂ)],
    ![((Real.sqrt 2)⁻¹ : ℂ), -((Real.sqrt 2)⁻¹ : ℂ)],
    ![((Real.sqrt 2)⁻¹ : ℂ), Complex.I * ((Real.sqrt 2)⁻¹ : ℂ)],
    ![((Real.sqrt 2)⁻¹ : ℂ), -Complex.I * ((Real.sqrt 2)⁻¹ : ℂ)],
    ![1,0], ![0,1]]

/-- PDF p.12: adjoint applied to I, a d-by-d matrix (not a superoperator determinant). -/
def dualIdentity {d : ℕ} (T : Super d) : Mat d :=
  fun i j => conj (∑ k, T (Matrix.single i j 1) k k)

/-- PDF pp.17--18, Eq.(37): the two explicitly constructed Kraus operators. -/
def canonicalChannel (a b : Fin 2 → ℂ) (x : ℝ) : Super 2 :=
  let e0 : Fin 2 → ℂ := ![1,0]
  let e1 : Fin 2 → ℂ := ![0,1]
  let A := outer e0 a
  let B := outer e0 b + (x : ℂ) • outer e1 e1
  twoSidedMap A Aᴴ + twoSidedMap B Bᴴ

/-- PDF p.18, Eq.(38): phase conventions and the trace-preserving constraint. -/
def CanonicalData (a b : Fin 2 → ℂ) (x : ℝ) : Prop :=
  (a 0).im = 0 ∧ (b 0).im = 0 ∧
    outer a a + outer b b = (1 : Mat 2) - (x ^ 2 : ℂ) • outer ![0,1] ![0,1]

/-- PDF p.18, Definition 21: canonical class 3 excludes classes 1 and 2. -/
def ClassThree (T : Super 2) : Prop :=
  Channel T ∧ krausRank T = 2 ∧ ∃ a b : Fin 2 → ℂ, ∃ x : ℝ,
    CanonicalData a b x ∧ T = canonicalChannel a b x ∧ a 0 ≠ 0 ∧ 0 < x ∧ x < 1

/-- PDF pp.18--19, Eq.(41): normalized input state with c1 in (0,1). -/
def classInput (c1 phi : ℝ) : Fin 2 → ℂ :=
  ![(Real.sqrt (1 - c1 ^ 2) : ℂ) * Complex.exp (Complex.I * (phi : ℂ)), (c1 : ℂ)]

/-- PDF pp.18--19, Eq.(41): y is fixed by normalization; the output's second component is x c1. -/
def classOutput (c1 x phi : ℝ) : Fin 2 → ℂ :=
  ![(Real.sqrt (1 - (x * c1) ^ 2) : ℂ) * Complex.exp (Complex.I * (phi : ℂ)),
    ((x * c1 : ℝ) : ℂ)]

/-- PDF p.16: computational-basis reindexing of the frozen X,Y,Z Pauli basis. -/
def pauliFin (i : Fin 3) : Mat 2 :=
  fun j k => QAlgorithms.QubitChannels.sigma i (decide (j.val = 1)) (decide (k.val = 1))

/-- PDF p.16, Eq.(32): the real 3-by-3 Pauli block. -/
def pauliBlock (T : Super 2) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((pauliFin i * T (pauliFin j)).trace).re / 2

/-- PDF p.16, Eq.(32): the translation part of the full Pauli representation. -/
def translation (T : Super 2) : Fin 3 → ℝ :=
  fun i => ((pauliFin i * T 1).trace).re / 2

/-- PDF pp.16--17: diagonal Lorentz branch includes unitality, not just diagonal pauliBlock. -/
def DiagonalBranch (S : Super 2) : Prop :=
  translation S = 0 ∧ ∃ lam : Fin 3 → ℝ, pauliBlock S = Matrix.diagonal lam

/-- PDF p.17, Theorem 18: the two other normal-form branches, including reset. -/
def OtherBranch (S : Super 2) : Prop :=
  (∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧ translation S = ![0,0,2/3] ∧
    pauliBlock S = Matrix.diagonal ![x / Real.sqrt 3, x / Real.sqrt 3, 1/3]) ∨
  (translation S = ![0,0,1] ∧ pauliBlock S = 0)

/-- PDF pp.16--17: normal forms are independently defined by invertible CP filters. -/
def NormalRepresentative (T S : Super 2) : Prop :=
  Channel S ∧ (∃ A B : Super 2, FilterMap A ∧ FilterMap B ∧ S = A * T * B) ∧
    (DiagonalBranch S ∨ OtherBranch S)

/-- PDF p.19, Theorem 23: existence of a diagonal Lorentz normal form. -/
def HasDiagonalNormalForm (T : Super 2) : Prop :=
  ∃ S : Super 2, NormalRepresentative T S ∧ DiagonalBranch S

/-- PDF p.21, Eq.(51): s_min(pauliBlock)^2 >= det(pauliBlock) > 0, without a default-valued infimum.
The quadratic inequality for every real vector is exactly the least-singular-value bound. -/
def SingularCriterion (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  0 < M.det ∧ ∀ v : Fin 3 → ℝ,
    M.det * (∑ j, (v j) ^ 2) ≤ ∑ i, (∑ j, M i j * v j) ^ 2

/-- Sanity: positive and completely positive choices are not identified. -/
example {d : ℕ} (T : Super d) : InClass false T = (QAlgorithms.Papers.Independent.Dependency50.P28.Positive T.toLinearMap ∧
    QAlgorithms.Papers.Independent.Dependency50.P28.TP T.toLinearMap) := rfl

/-- Sanity: zero-time exponential is the identity. -/
example {d : ℕ} (L : Super d) : NormedSpace.exp ((0 : ℝ) • L) = 1 := by
  calc
    NormedSpace.exp ((0 : ℝ) • L) = NormedSpace.exp (0 : Super d) :=
      congrArg (fun X : Super d => NormedSpace.exp X) (_root_.zero_smul ℝ L)
    _ = 1 := NormedSpace.exp_zero

/-- Sanity: a list of zero factors composes to the identity, rather than the zero map. -/
example {d : ℕ} : ([] : List (Super d)).prod = 1 := rfl

/-- Sanity: the output phase convention agrees with the input at x=1. -/
example (c1 phi : ℝ) : classOutput c1 1 phi = classInput c1 phi := by
  simp [classOutput, classInput]

/-- Sanity: the identity channel preserves trace on every matrix. -/
example {d : ℕ} : QAlgorithms.Papers.Independent.Dependency50.P28.TP (1 : Super d).toLinearMap := by
  intro X
  rfl

/-- Sanity: complete positivity includes the identity on every ancilla. -/
example {d : ℕ} : QAlgorithms.Entanglement.IsCompletelyPositive (1 : Super d).toLinearMap := by
  intro r X hX
  change X.PosSemidef
  exact hX

/-- Sanity: the zero map is CP but is not assigned a normalized Choi state. -/
example {d : ℕ} : jamiolkowskiState (0 : Super d) = 0 := by
  ext i j
  simp [jamiolkowskiState, QAlgorithms.Papers.Independent.Information100.P50.choiMatrix]

/-- Sanity: the Choi-rank convention assigns zero rank to the zero map. -/
example {d : ℕ} : krausRank (0 : Super d) = 0 := by
  change ((d : ℂ)⁻¹ •
    (0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)).rank = 0
  simp

/-- Sanity: unit basis vectors give the expected rank-one matrix unit. -/
example : outer (![1,0] : Fin 2 → ℂ) ![0,1] 0 1 = 1 := by
  norm_num [outer]

/-- Sanity: an output/reference diagonal Choi entry includes the factor 1/d. -/
example (T : Super 2) : jamiolkowskiState T (0,0) (1,1) =
    (2 : ℂ)⁻¹ * T (Matrix.single 0 1 1) 0 1 := rfl

/-- Sanity: singular limits are tested in ambient space, without an inverse binder. -/
example {d : ℕ} (T : Super d) : Infinitesimal false T ↔
    T ∈ closure (fineProducts d false false) := Iff.rfl

/-- Sanity: the strict rank threshold admits a zero Delta block and excludes rank two. -/
example : (0 : Matrix (Fin 3) (Fin 3) ℝ).rank < 2 := by simp

/-- Sanity: coefficient construction delegates to the frozen linear constructor. -/
example {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    (fromCoefficients M).toLinearMap =
      QAlgorithms.Papers.Independent.Information100.P50.coefficientMap
        (fun i j a b => M (i,j) (a,b)) := rfl

/-- Sanity: transposition adapter preserves the accepted action exactly. -/
example {d : ℕ} (X : Mat d) : continuousTranspose d X = X.transpose := rfl

/-- Sanity: Eq.(2) uses the Euclidean norm of the full matrix-unit action. -/
example {d : ℕ} (T : Super d) : hsOperatorNorm T =
    ‖Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ) (coefficients T)‖ := rfl

end QAlgorithms.Papers.Independent.Frontier30.P20


