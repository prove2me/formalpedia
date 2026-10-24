-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22
-- name    : QAlgorithms_Papers_Independent_Support50_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:47:20.552855+00:00
-- url     : https://prove2.me/theorems/51ca86df-d24b-4de1-8fab-991cfebb620a
-- title:
--   Definitions for Post-selection technique for quantum channels with applications to quantum cryptography
-- statement:
--   The objects the formalized statements of *Post-selection technique for quantum channels with applications to quantum cryptography* (arXiv:0809.3019) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tensorId`: Apply a map to the first register. The two swaps explicitly convert to and from the accepted reference-first `idTensorSuperop` convention (PDF p.2).
--   - `FinitePurification`: Normalized purification, system first and reference last (PDF p.4, footnote 12). The reduced state is specified, not the target postselection.
--   - `permuteInput`: Source tensor permutation on operators: the vector action uses pi inverse, so conjugation reads matrix coordinates at x composed with pi (footnote 10).
--   - `pairPermutation`: Simultaneous permutation of H and K copies (PDF pp.2,4).
--   - `pairedSymmetricSpace`: The simultaneous-pair symmetric subspace, not the space of invariant mixed operators (PDF p.2 and footnote 10).
--   - `subspaceProjectorMatrix`: Coordinate matrix of the actual orthogonal projector onto a subspace, used for the identities on PDF p.2 and the substitution in footnote 17.
--   - `factor`: Exact symmetric-space dimension factor in Theorem 1, PDF p.2.
--   - `pairedCopiesEquiv`: Explicit regrouping of paired copies, PDF p.2.
--   - `pairVector`: Identify Fin(d*d) Haar coordinates with H tensor K, K a copy of H. The lexicographic equivalence is fixed independently of the map or input.
--   - `pairedPower`: Regrouped n-fold tensor power of a bipartite operator (PDF p.2). This is the tensor power reindexed by `pairedCopiesEquiv`, evaluated coordinatewise.
--   - `densityTensorPower`: Tensor power of a single-system operator, equation (1), PDF p.1.
--   - `hilbertSchmidtLaw`: The Hilbert--Schmidt induced density law: push forward Haar pure states on H tensor a d-dimensional copy K by partial trace (PDF p.2, citation [5]). This is a constructed law, not an arbitrary mixing measure.
--   - `deFinettiState`: The specific de Finetti state in equation (1), PDF p.1. The integrand is a continuous polynomial on the compact support of the induced probability law.
--   - `tauPair`: Haar extension of the specified test state, PDF p.2. This is constructed from the integral; the projector identity is a conclusion below.
--   - `basisPurification`: Canonical basis purification of the normalized projector onto S (PDF p.2). The reference is a coordinate copy of S identified by b; the formula is r^(-1/2) sum_i b_i tensor |i>. Its use below has r=g(n,d)>0.
--   - `postselect`: Scalar-valued CP postselection functional applied on the last register. For an effect M this is (id tensor [X ↦ Tr(XM)]); its scalar codomain is literal complex numbers, not a surviving output register (Lemma 2, PDF p.2).
--   - `RangeSupported`: Range support in a vector subspace, as in Lemma 2 (PDF p.2).
--   - `linearExtension`: Matrix-unit complex-linear extension, used to construct the ideal protocol on all operators from its specified classical replacement rule (PDF p.3).
--   - `KeyOut`: Finite variable-length classical output: length branch, Alice's key, Bob's key, and the complete public transcript (PDF p.3). Zero length allowed.
--   - `replaceKeys`: Ideal key replacement S, PDF p.3. The length branch and transcript are preserved; keys are replaced by the identical uniform pair of that length. The rule discards coherences because this is a classical output operation.
--   - `keyReplacement`: Complex-linear ideal output map S, constructed by matrix units (PDF p.3).
--   - `idealProtocol`: F = S composed with E, constructed from E (PDF p.3).
--   - `publicSymmetrize`: Uniform permutation average WITH a retained classical permutation label, PDF pp.3--4, footnote 16. Its probability is 1/n!, including 0!=1.
--   - `relabelPublic`: Relabel the publicly communicated permutation p by p composed with pi; this expression pulls output coordinates back by pi inverse (footnote 16).
--   - `dualPairAction`: Dual action U(g inverse)^T on W and the product action on V tensor W, PDF p.4, footnote 17. W uses the dual rather than the original representation.
--   - `invariantSpace`: The fixed VECTOR subspace (V tensor dual V)^G (footnote 17, PDF p.4).
--   - `groupTau`: The group test state is the normalized invariant-space projector, constructed from the representation (footnote 17). No Haar measure on a possibly noncompact group is used.
-- source:
--   Post-selection technique for quantum channels with applications to quantum cryptography, arXiv:0809.3019v1, https://arxiv.org/abs/0809.3019v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

/-!
Statements from Christandl--Koenig--Renner, arXiv:0809.3019v1.
All new constructions are local to this paper. Physical registers use fixed finite
complex coordinates. Trace norms have no factor 1/2. The two underspecified
operational hashing/rate claims are recorded in HARD.md, rather than weakened.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P69 (diamond)
open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

/-- Borel sigma algebra of the fixed finite matrix coordinates (PDF pp.1--2).
This makes the Hilbert--Schmidt pushforward a measure on actual matrices. -/
local instance postselectionMatrixMeasurableSpace (A : Type*) : MeasurableSpace (Matrix A A ℂ) := borel _

/-- The matrix measurable structure is its Borel structure (PDF pp.1--2). -/
local instance postselectionMatrixBorelSpace (A : Type*) : BorelSpace (Matrix A A ℂ) := ⟨rfl⟩

/-- Apply a map to the first register. The two swaps explicitly convert to and
from the accepted reference-first `idTensorSuperop` convention (PDF p.2). -/
def tensorId {A B R : Type*} (D : Superop A B) : Superop (A × R) (B × R) :=
  fun X p q => idTensorSuperop (R := R) D
    (fun a b => X (a.2,a.1) (b.2,b.1)) (p.2,p.1) (q.2,q.1)

/-- Normalized purification, system first and reference last (PDF p.4,
footnote 12). The reduced state is specified, not the target postselection. -/
def FinitePurification {A R : Type*} [Fintype A] [Fintype R]
    (psi : EuclideanSpace ℂ (A × R)) (rho : Matrix A A ℂ) : Prop :=
  IsState psi ∧ traceRight (pureDensity psi) = rho

/-- Source tensor permutation on operators: the vector action uses pi inverse,
so conjugation reads matrix coordinates at x composed with pi (footnote 10). -/
def permuteInput {n d : ℕ} (pi : Equiv.Perm (Fin n)) : Superop (Copies (Fin d) n) (Copies (Fin d) n) :=
  fun X a b => X (a ∘ pi) (b ∘ pi)

/-- Simultaneous permutation of H and K copies (PDF pp.2,4). -/
def pairPermutation (n d : ℕ) (pi : Equiv.Perm (Fin n)) :
    Matrix (Copies (Fin d) n × Copies (Fin d) n) (Copies (Fin d) n × Copies (Fin d) n) ℂ :=
  Matrix.kronecker (Schur.tensorPermutation d n pi) (Schur.tensorPermutation d n pi)

/-- The simultaneous-pair symmetric subspace, not the space of invariant
mixed operators (PDF p.2 and footnote 10). -/
def pairedSymmetricSpace (n d : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Copies (Fin d) n × Copies (Fin d) n)) :=
  ⨅ pi : Equiv.Perm (Fin n), LinearMap.ker
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Copies (Fin d) n × Copies (Fin d) n) (pairPermutation n d pi)).toLinearMap - LinearMap.id)

/-- Coordinate matrix of the actual orthogonal projector onto a subspace,
used for the identities on PDF p.2 and the substitution in footnote 17. -/
def subspaceProjectorMatrix {A : Type*} [Fintype A] [DecidableEq A]
    (S : Submodule ℂ (EuclideanSpace ℂ A)) : Matrix A A ℂ :=
  fun a b => S.starProjection (ket b) a

/-- Exact symmetric-space dimension factor in Theorem 1, PDF p.2. -/
def factor (n d : ℕ) : ℕ := Nat.choose (n + d ^ 2 - 1) n

/-- Explicit regrouping of paired copies, PDF p.2. -/
def pairedCopiesEquiv (n d : ℕ) : (Fin n → Fin d × Fin d) ≃ (Copies (Fin d) n × Copies (Fin d) n) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x := fun i => (x.1 i,x.2 i)
  left_inv x := by funext i; exact Prod.eta (x i)
  right_inv x := by cases x; rfl

/-- Identify Fin(d*d) Haar coordinates with H tensor K, K a copy of H.
The lexicographic equivalence is fixed independently of the map or input. -/
def pairVector (d : ℕ) (psi : EuclideanSpace ℂ (Fin (d*d))) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun x => psi (finProdFinEquiv x))

/-- Regrouped n-fold tensor power of a bipartite operator (PDF p.2).
This is the tensor power reindexed by `pairedCopiesEquiv`, evaluated coordinatewise. -/
def pairedPower (n d : ℕ) (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Copies (Fin d) n × Copies (Fin d) n) (Copies (Fin d) n × Copies (Fin d) n) ℂ :=
  fun a b => ∏ i, rho (a.1 i,a.2 i) (b.1 i,b.2 i)

/-- Tensor power of a single-system operator, equation (1), PDF p.1. -/
def densityTensorPower (n d : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ :=
  fun a b => ∏ i, rho (a i) (b i)

/-- The Hilbert--Schmidt induced density law: push forward Haar pure states on
H tensor a d-dimensional copy K by partial trace (PDF p.2, citation [5]).
This is a constructed law, not an arbitrary mixing measure. -/
def hilbertSchmidtLaw (d : ℕ) (hd : 0 < d) : Measure (Matrix (Fin d) (Fin d) ℂ) :=
  (QuditFidelity.haarPureStateLaw (d*d) (Nat.mul_pos hd hd)).map
    (fun psi => traceRight (pureDensity (pairVector d psi)))

/-- The specific de Finetti state in equation (1), PDF p.1. The integrand is a
continuous polynomial on the compact support of the induced probability law. -/
def deFinettiState (n d : ℕ) (hd : 0 < d) : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ :=
  ∫ rho, densityTensorPower n d rho ∂hilbertSchmidtLaw d hd

/-- Haar extension of the specified test state, PDF p.2. This is constructed
from the integral; the projector identity is a conclusion below. -/
def tauPair (n d : ℕ) (hd : 0 < d) :
    Matrix (Copies (Fin d) n × Copies (Fin d) n) (Copies (Fin d) n × Copies (Fin d) n) ℂ :=
  ∫ psi, pairedPower n d (pureDensity (pairVector d psi))
    ∂QuditFidelity.haarPureStateLaw (d*d) (Nat.mul_pos hd hd)

/-- Canonical basis purification of the normalized projector onto S (PDF p.2).
The reference is a coordinate copy of S identified by b; the formula is
r^(-1/2) sum_i b_i tensor |i>. Its use below has r=g(n,d)>0. -/
def basisPurification {A : Type*} [Fintype A]
    (S : Submodule ℂ (EuclideanSpace ℂ A))
    (b : OrthonormalBasis (Fin (Module.finrank ℂ S)) ℂ S) :
    EuclideanSpace ℂ (A × Fin (Module.finrank ℂ S)) :=
  WithLp.toLp 2 (fun x => ((Real.sqrt (Module.finrank ℂ S) : ℂ)⁻¹) * (b x.2).val x.1)

/-- Scalar-valued CP postselection functional applied on the last register.
For an effect M this is (id tensor [X ↦ Tr(XM)]); its scalar codomain is
literal complex numbers, not a surviving output register (Lemma 2, PDF p.2). -/
def postselect {A N : Type*} [Fintype N] (M : Matrix N N ℂ)
    (X : Matrix (A × N) (A × N) ℂ) : Matrix A A ℂ :=
  fun a b => ∑ i, ∑ j, X (a,i) (b,j) * M j i

/-- Range support in a vector subspace, as in Lemma 2 (PDF p.2). -/
def RangeSupported {A : Type*} [Fintype A] (rho : Matrix A A ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ A)) : Prop :=
  ∀ psi, act rho psi ∈ S

/-- Matrix-unit complex-linear extension, used to construct the ideal protocol
on all operators from its specified classical replacement rule (PDF p.3). -/
def linearExtension {A B : Type*} [Fintype A] [DecidableEq A]
    (f : Superop A B) : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun X a b := ∑ i, ∑ j, X i j * f (Matrix.single i j 1) a b
  map_add' X Y := by
    ext a b
    change (∑ i, ∑ j, (X i j + Y i j) * f (Matrix.single i j 1) a b) =
      (∑ i, ∑ j, X i j * f (Matrix.single i j 1) a b) +
        (∑ i, ∑ j, Y i j * f (Matrix.single i j 1) a b)
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b
    change (∑ i, ∑ j, (c * X i j) * f (Matrix.single i j 1) a b) =
      c * (∑ i, ∑ j, X i j * f (Matrix.single i j 1) a b)
    simp only [Finset.mul_sum, mul_assoc]

/-- Finite variable-length classical output: length branch, Alice's key,
Bob's key, and the complete public transcript (PDF p.3). Zero length allowed. -/
abbrev KeyOut (L C : Type*) (len : L → ℕ) :=
  (l : L) × ((Qubits (len l) × Qubits (len l)) × C)

/-- Ideal key replacement S, PDF p.3. The length branch and transcript are
preserved; keys are replaced by the identical uniform pair of that length.
The rule discards coherences because this is a classical output operation. -/
def replaceKeys {L C : Type*} [Fintype L] [Fintype C] (len : L → ℕ) :
    Superop (KeyOut L C len) (KeyOut L C len) :=
  fun X a b => if a = b ∧ a.2.1.1 = a.2.1.2 then
    ((2 : ℂ) ^ len a.1)⁻¹ * ∑ s : Qubits (len a.1), ∑ t : Qubits (len a.1),
      X ⟨a.1,((s,t),a.2.2)⟩ ⟨a.1,((s,t),a.2.2)⟩ else 0

/-- Complex-linear ideal output map S, constructed by matrix units (PDF p.3). -/
def keyReplacement {L C : Type*} [Fintype L] [Fintype C] (len : L → ℕ) :
    Matrix (KeyOut L C len) (KeyOut L C len) ℂ →ₗ[ℂ]
      Matrix (KeyOut L C len) (KeyOut L C len) ℂ :=
  linearExtension (replaceKeys len)

/-- F = S composed with E, constructed from E (PDF p.3). -/
def idealProtocol {A L C : Type*} [Fintype A] [Fintype L] [Fintype C]
    (len : L → ℕ)
    (E : Matrix A A ℂ →ₗ[ℂ] Matrix (KeyOut L C len) (KeyOut L C len) ℂ) :=
  (keyReplacement len).comp E

/-- Uniform permutation average WITH a retained classical permutation label,
PDF pp.3--4, footnote 16. Its probability is 1/n!, including 0!=1. -/
def publicSymmetrize {n d : ℕ} {B : Type*}
    (E : Superop (Copies (Fin d) n) B) :
    Superop (Copies (Fin d) n) (Equiv.Perm (Fin n) × B) :=
  fun X a b => if a.1 = b.1 then
    ((Nat.factorial n : ℂ)⁻¹) * E (permuteInput a.1 X) a.2 b.2 else 0

/-- Relabel the publicly communicated permutation p by p composed with pi;
this expression pulls output coordinates back by pi inverse (footnote 16). -/
def relabelPublic {n : ℕ} {B : Type*} (pi : Equiv.Perm (Fin n)) :
    Superop (Equiv.Perm (Fin n) × B) (Equiv.Perm (Fin n) × B) :=
  fun X a b => X (a.1 * pi.symm,a.2) (b.1 * pi.symm,b.2)

/-- Dual action U(g inverse)^T on W and the product action on V tensor W,
PDF p.4, footnote 17. W uses the dual rather than the original representation. -/
def dualPairAction {G : Type*} [Group G] {v : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin v) ℂ) (g : G) :
    Matrix (Fin v × Fin v) (Fin v × Fin v) ℂ :=
  Matrix.kronecker (U g : Matrix (Fin v) (Fin v) ℂ)
    (U g⁻¹ : Matrix (Fin v) (Fin v) ℂ).transpose

/-- The fixed VECTOR subspace (V tensor dual V)^G (footnote 17, PDF p.4). -/
def invariantSpace {G : Type*} [Group G] {v : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin v) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin v × Fin v)) :=
  ⨅ g : G, LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin v × Fin v) (dualPairAction U g)).toLinearMap - LinearMap.id)

/-- The group test state is the normalized invariant-space projector,
constructed from the representation (footnote 17). No Haar measure on a
possibly noncompact group is used. -/
def groupTau {G : Type*} [Group G] {v : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin v) ℂ) :
    Matrix (Fin v × Fin v) (Fin v × Fin v) ℂ :=
  ((Module.finrank ℂ (invariantSpace U) : ℂ)⁻¹) • subspaceProjectorMatrix (invariantSpace U)

/-- Small semantic checks. These establish conventions rather than prove any
of the paper's results. -/

example (d : ℕ) : factor 0 d = 1 := by simp [factor]

example {A R : Type*} (X : Matrix (A × R) (A × R) ℂ) :
    tensorId (fun Y : Matrix A A ℂ => Y) X = X := by ext a b; rfl

example {n d : ℕ} (X : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ) :
    permuteInput (1 : Equiv.Perm (Fin n)) X = X := by rfl

example (d : ℕ) (rho : Matrix (Fin d) (Fin d) ℂ) (a b : Copies (Fin d) 0) :
    densityTensorPower 0 d rho a b = 1 := by simp [densityTensorPower]

example {A N : Type*} [Fintype N] [DecidableEq N]
    (X : Matrix (A × N) (A × N) ℂ) :
    postselect (1 : Matrix N N ℂ) X = traceRight X := by
  ext a b
  simp [postselect, traceRight, Matrix.one_apply]

example {L C : Type*} [Fintype L] [Fintype C] (len : L → ℕ) :
    keyReplacement len (0 : Matrix (KeyOut L C len) (KeyOut L C len) ℂ) = 0 :=
  map_zero _

example {G : Type*} [Group G] {v : ℕ} (U : G →* Matrix.unitaryGroup (Fin v) ℂ) :
    dualPairAction U 1 = 1 := by
  simp [dualPairAction]

example (n : ℕ) : factor n 1 = 1 := by simp [factor]

end QAlgorithms.Papers.Independent.Support50.P22


