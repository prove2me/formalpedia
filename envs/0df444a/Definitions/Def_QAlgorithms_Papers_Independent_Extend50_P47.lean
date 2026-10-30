-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47
-- name    : QAlgorithms_Papers_Independent_Extend50_P47
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T21:09:55.677194+00:00
-- url     : https://prove2.me/theorems/d884ba9d-3aea-435b-a89f-e82400760e67
-- title:
--   Definitions for Testing symmetry on quantum computers
-- statement:
--   The objects the formalized statements of *Testing symmetry on quantum computers* (arXiv:2105.12758) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsProjectiveUnitaryLift`: pp.3–4: unitary projective lift; scalar multipliers have modulus one.
--   - `symmetryControlAverage`: pp.3–4, (1),(19): raw average, used as a projector only with an ordinary law.
--   - `Bose`: p.7, (40): normalized Bose states, with support in P.
--   - `Sym`: p.8, (46): normalized states invariant under conjugation.
--   - `Extension`: pp.3–4: normalized extension, tracing out exactly R.
--   - `BSE`: p.4, Definition 2.2.
--   - `SE`: p.3, Definition 2.1.
--   - `conjugateTensorAction`: p.5, (22): phases cancel in U tensor conjugate U.
--   - `controlReturnProbability`: pp.6–7: control preparation, controlled U, and return-to-control amplitude K have acceptance Tr(K† K rho). This definition also applies to weighted controls.
--   - `firstChannel`: pp.8–12: N acts on the purifying register only, preserving all S blocks.
--   - `proverValues`: pp.8–12: all allowed prover operations; private environments are discarded.
--   - `symmetryFidelityValues`: p.7: attained comparison values, with normalized comparison states in Q.
--   - `TestIdentity`: pp.9–12: equality of attained operational and squared-fidelity maxima.
--   - `symTest`: p.9: returned S-hat first, retained S second.
--   - `seTest`: p.11: returned R,R-hat,S-hat first; retained S second.
--   - `hsChannelAdjoint`: pp.33–36: Hilbert–Schmidt adjoint in the computational matrix-unit basis.
--   - `BoseChannel`: p.33, Definition 7.1: CPTP and N†(Qout) ≥ Qin in Löwner order.
--   - `IsOperatorCovariant`: p.15, (110): covariance as equality on every operator.
--   - `ChannelExtension`: p.35, (233): a channel extension includes the marginal identity on all operators.
--   - `SEChannel`: pp.34–35, Definition 7.2, with the fixed reference representations retained.
--   - `BSEChannel`: p.36, Definition 7.3, with the adjoint inequality, rather than covariance.
--   - `densityPreparation`: p.33: the preparation channel from a fully trivial input.
--   - `replaceReference`: p.35: replace R with its normalized identity and retain S, also on entangled inputs.
--   - `StandardStep`: p.5: placed gates from H,CNOT,T and the replacement T†.
--   - `conjugateStep`: p.5: replace T by T†; real H,CNOT are unchanged.
--   - `standardStepOperator`: p.5: actual matrices of the placed gates.
--   - `standardCircuit`: p.5: head is applied first, hence reverse product.
--   - `incoherentClock`: pp.9–10, (55): cyclic phase-shift family in the incoherent basis.
--   - `symmetryTensorCopies`: p.13: independent copies of a density in their computational basis.
--   - `permutation`: p.13: the frozen tensor-permutation matrix, transported from a finite basis labeling. Its convention sends |x> to |x composed with pi inverse>.
--   - `tensorSymmetrizer`: p.13, (15): symmetric-subspace projection.
--   - `pureBipFamily`: p.13, (79)–(80): permute only the B shares of k copies of AB.
--   - `bipartiteAcceptance`: p.13: actual control-return acceptance on k pure AB copies.
--   - `kFamily`: pp.4,14: full extension basis is (remaining B copies, retained AB).
--   - `separableExtension`: p.14, (94): the extension computed from the pure-product mixture.
--   - `multiPureFamily`: p.14, (89): independent permutations of each party's k copies.
--   - `multiCopies`: p.14: regroup k copies so each party's copies are adjacent.
--   - `multiProjector`: p.14: tensor product of the local symmetric projections.
--   - `multiFamily`: p.15, (97)–(107): remaining copies first, first copy of every party retained.
--   - `choiFamily`: p.16, (121): conjugate input representation tensor output representation.
--   - `outcomeMatrix`: p.16: the supplied outcome-label permutation representation.
--   - `povmOutcomeChannel`: p.16, (124): the quantum-to-classical measurement channel.
--   - `qcBlockMatrix`: p.17: quantum-classical blocks are subnormalized; only their sum has trace one.
--   - `rootValues`: p.18: root-fidelity values, distinct from the squared operational values.
--   - `stateSDP`: p.18, (142)–(143): every SDP block and constraint, including the orientation of X†.
--   - `extensionSDP`: p.18, (144)–(145): X,rho act on S, omega on RS, with Tr_R omega in the block.
--   - `IsIrreducibleUnitaryLift`: pp.18–19: irreducibility means no nontrivial invariant subspace, expressed by its orthogonal projector. No scalar-commutant conclusion is assumed.
--   - `InequivalentFamilies`: pp.18–19: inequivalent irreducible unitary families have no unitary intertwiner.
--   - `IsotypicData`: pp.18–19, (146)–(148): isotypic data defined through unitary intertwining and inequivalent irreducibility, rather than the desired state parameterization. The block families inherit the actual project's multiplier through intertwining.
--   - `isotypicDensity`: p.18, (154): the state computed from multiplicity blocks.
--   - `schurBlocks`: p.18, (153): trace out the irrep factor, retaining the multiplicity factor.
--   - `TrivialBlock`: p.19, (155)–(157): a multiplicity block is Bose-allowed only for the trivial irrep.
--   - `booleanSinglet`: p.23: normalized two-qubit singlet in the computational basis.
--   - `collectiveSU2Average`: p.23, (160): normalized Haar average of the collective SU(2) action.
--   - `pauliAxisRotation`: p.23, (165): rotation about the Pauli axis a by theta.
--   - `bilateral`: p.23, (163): bilateral rotation at the paper's sign convention.
--   - `twelveRotations`: p.23, (166): literal list of twelve products, retaining their matrix phases.
--   - `bitHammingWeight`: pp.26–28: the number of one bits.
--   - `weightProjector`: pp.26–28: projector onto the entire weight-k sector.
--   - `collectiveZRotation`: p.26, (175)–(178): collective phase; subtraction takes place in the reals.
--   - `collectiveZAverage`: p.26, (174): normalized integral over the complete 4pi period.
--   - `finitePhase`: p.26, (183): the literal finite unitary family; no odd-n group law is asserted.
--   - `collectiveZTwirl`: p.27, (197): continuous collective dephasing.
--   - `KChannel`: p.35, (244)–(245): k-extendible channels through their actual copy permutations.
--   - `KBoseChannel`: p.36, (255)–(258): k-Bose channels use symmetric support, not covariance.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, https://arxiv.org/abs/2105.12758v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

/-!
Statements from LaBorde–Rethinasamy–Wilde, arXiv:2105.12758v3.
Paper-specific objects are local; identical Mat, copies, and normalizedChoi
objects are imported from the pinned accepted library. All page references are PDF pages.
The operational model uses all CPTP maps on the purifying register, equivalently
all prover isometries with a discarded private environment. No operation acts on
retained S. Maxima are expressed by IsGreatest, which includes attainment.
Raw Bose averages require an ordinary representation; conjugation results permit
projective lifts. Fidelity always means rootFidelity squared unless explicitly root.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff
open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}
variable [Fintype G] [Group G] [DecidableEq G]
variable [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype P] [DecidableEq P] [Nonempty P]
variable [Fintype T] [DecidableEq T] [Nonempty T]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype R2] [DecidableEq R2] [Nonempty R2]
variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- pp.3–4: unitary projective lift; scalar multipliers have modulus one. -/
def IsProjectiveUnitaryLift (U : G → Matrix.unitaryGroup S ℂ) : Prop :=
  ∀ g h, ∃ z : ℂ, ‖z‖ = 1 ∧
    (U (g * h) : Mat S) = z • ((U g : Mat S) * (U h : Mat S))

/-- pp.3–4, (1),(19): raw average, used as a projector only with an ordinary law. -/
def symmetryControlAverage (U : G → Mat S) : Mat S :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, U g

/-- p.7, (40): normalized Bose states, with support in P. -/
def Bose (Q : Mat S) (rho : Mat S) : Prop :=
  IsDensityMatrix rho ∧ rho = Q * rho * Q

/-- p.8, (46): normalized states invariant under conjugation. -/
def Sym (U : G → Mat S) (rho : Mat S) : Prop :=
  IsDensityMatrix rho ∧ ∀ g, rho = U g * rho * (U g)ᴴ

/-- pp.3–4: normalized extension, tracing out exactly R. -/
def Extension (Q : Mat (R × S) → Prop) (rho : Mat S) : Prop :=
  IsDensityMatrix rho ∧ ∃ omega, Q omega ∧ traceLeft omega = rho

/-- p.4, Definition 2.2. -/
def BSE (U : G → Mat (R × S)) (rho : Mat S) : Prop :=
  Extension (Bose (symmetryControlAverage U)) rho

/-- p.3, Definition 2.1. -/
def SE (U : G → Mat (R × S)) (rho : Mat S) : Prop :=
  Extension (Sym U) rho

/-- p.5, (22): phases cancel in U tensor conjugate U. -/
def conjugateTensorAction (U : G → Mat S) (g : G) : Mat (S × S) :=
  Matrix.kronecker (U g) ((U g).map conj)

/-- pp.6–7: control preparation, controlled U, and return-to-control amplitude K
have acceptance Tr(K† K rho). This definition also applies to weighted controls. -/
def controlReturnProbability (K rho : Mat S) : ℝ := effectProb (Kᴴ * K) rho

/-- pp.8–12: N acts on the purifying register only, preserving all S blocks. -/
def firstChannel (N : Superop P T) : Superop (P × S) (T × S) :=
  fun X => Matrix.of fun a b =>
    N (Matrix.of fun p q => X (p, a.2) (q, b.2)) a.1 b.1

/-- pp.8–12: all allowed prover operations; private environments are discarded. -/
def proverValues (psi : EuclideanSpace ℂ (P × S)) (K : Mat (T × S)) : Set ℝ :=
  {v | ∃ N : Superop P T, IsChannel N ∧
    v = controlReturnProbability K (firstChannel N (pureDensity psi))}

/-- p.7: attained comparison values, with normalized comparison states in Q. -/
def symmetryFidelityValues (rho : Mat S) (Q : Mat S → Prop) : Set ℝ :=
  {v | ∃ sigma, Q sigma ∧ v = rootFidelity rho sigma ^ 2}

/-- pp.9–12: equality of attained operational and squared-fidelity maxima. -/
def TestIdentity (psi : EuclideanSpace ℂ (P × S)) (K : Mat (T × S))
    (rho : Mat S) (Q : Mat S → Prop) : Prop :=
  ∃ v, IsGreatest (proverValues psi K) v ∧ IsGreatest (symmetryFidelityValues rho Q) v

/-- p.9: returned S-hat first, retained S second. -/
def symTest (U : G → Mat S) : Mat (S × S) :=
  symmetryControlAverage fun g => (conjugateTensorAction U g).submatrix Prod.swap Prod.swap

/-- p.11: returned R,R-hat,S-hat first; retained S second. -/
def seTest (U : G → Mat (R × S)) : Mat ((R × (R × S)) × S) :=
  (symmetryControlAverage (conjugateTensorAction U)).submatrix
    (fun p => ((p.1.1, p.2), p.1.2)) (fun p => ((p.1.1, p.2), p.1.2))

/-- pp.33–36: Hilbert–Schmidt adjoint in the computational matrix-unit basis. -/
def hsChannelAdjoint (N : Superop A B) (Y : Mat B) : Mat A :=
  Matrix.of fun i j => ∑ a, ∑ b, conj (N (Matrix.single i j 1) a b) * Y a b

/-- p.33, Definition 7.1: CPTP and N†(Qout) ≥ Qin in Löwner order. -/
def BoseChannel (Qin : Mat A) (Qout : Mat B) (N : Superop A B) : Prop :=
  IsChannel N ∧ (hsChannelAdjoint N Qout - Qin).PosSemidef

/-- p.15, (110): covariance as equality on every operator. -/
def IsOperatorCovariant (U : G → Mat A) (V : G → Mat B) (N : Superop A B) : Prop :=
  ∀ g X, N (U g * X * (U g)ᴴ) = V g * N X * (V g)ᴴ

/-- p.35, (233): a channel extension includes the marginal identity on all operators. -/
def ChannelExtension (N : Superop S S2) (M : Superop (R × S) (R2 × S2)) : Prop :=
  IsChannel M ∧ ∀ X, traceLeft (M X) = N (traceLeft X)

/-- pp.34–35, Definition 7.2, with the fixed reference representations retained. -/
def SEChannel (U : G → Mat (R × S)) (V : G → Mat (R2 × S2))
    (N : Superop S S2) : Prop :=
  IsChannel N ∧ ∃ M, ChannelExtension N M ∧ IsOperatorCovariant U V M

/-- p.36, Definition 7.3, with the adjoint inequality, rather than covariance. -/
def BSEChannel (U : G → Mat (R × S)) (V : G → Mat (R2 × S2))
    (N : Superop S S2) : Prop :=
  IsChannel N ∧ ∃ M, ChannelExtension N M ∧
    (hsChannelAdjoint M (symmetryControlAverage V) - symmetryControlAverage U).PosSemidef

/-- p.33: the preparation channel from a fully trivial input. -/
def densityPreparation (rho : Mat S) : Superop Unit S := fun X => X.trace • rho

/-- p.35: replace R with its normalized identity and retain S, also on entangled inputs. -/
def replaceReference (X : Mat (R × S)) : Mat (R × S) :=
  Matrix.kronecker ((Fintype.card R : ℂ)⁻¹ • (1 : Mat R)) (traceLeft X)

example (Q rho : Mat S) : Bose Q rho ↔
    IsDensityMatrix rho ∧ rho = Q * rho * Q := Iff.rfl

example (rho : Mat S) (X : Mat Unit) : densityPreparation rho X = X.trace • rho := rfl

example (N : Superop P T) (X : Mat (P × S)) (a b : T × S) :
    firstChannel N X a b = N (fun p q => X (p, a.2) (q, b.2)) a.1 b.1 := rfl

/-- p.5: placed gates from H,CNOT,T and the replacement T†. -/
inductive StandardStep (n : ℕ) where
  | h (q : Fin n)
  | t (q : Fin n)
  | td (q : Fin n)
  | cx (w : Fin 2 ↪ Fin n)

/-- p.5: replace T by T†; real H,CNOT are unchanged. -/
def conjugateStep {n : ℕ} : StandardStep n → StandardStep n
  | .h q => .h q
  | .t q => .td q
  | .td q => .t q
  | .cx w => .cx w

/-- p.5: actual matrices of the placed gates. -/
def standardStepOperator {n : ℕ} : StandardStep n → Mat (Qubits n)
  | .h q => embedOp (Gate.ofMatrix1 hadamard).mat
      (show Fin 1 ↪ Fin n from
        ⟨fun _ => q, fun _ _ _ => Subsingleton.elim _ _⟩)
  | .t q => embedOp (Gate.ofMatrix1 gateT).mat
      (show Fin 1 ↪ Fin n from
        ⟨fun _ => q, fun _ _ _ => Subsingleton.elim _ _⟩)
  | .td q => embedOp (Gate.ofMatrix1 gateTᴴ).mat
      (show Fin 1 ↪ Fin n from
        ⟨fun _ => q, fun _ _ _ => Subsingleton.elim _ _⟩)
  | .cx w => embedOp (Gate.ofMatrix2 cnot).mat w

/-- p.5: head is applied first, hence reverse product. -/
def standardCircuit {n : ℕ} (c : List (StandardStep n)) : Mat (Qubits n) :=
  (c.map standardStepOperator).reverse.prod

example {n : ℕ} (q : Fin n) : conjugateStep (.t q) = .td q := rfl

example (n : ℕ) : standardCircuit ([] : List (StandardStep n)) = 1 := rfl

/-- pp.9–10, (55): cyclic phase-shift family in the incoherent basis. -/
def incoherentClock (d : ℕ) (z : Fin d) : Mat (Fin d) :=
  Matrix.diagonal fun j => Complex.exp (2 * Real.pi * Complex.I * j.val * z.val / d)

/-- p.13: independent copies of a density in their computational basis. -/
def symmetryTensorCopies (rho : Mat S) (k : ℕ) : Mat (Fin k → S) :=
  QAlgorithms.Papers.Independent.Information100.P60.copies k rho

/-- p.13: the frozen tensor-permutation matrix, transported from a finite basis
labeling. Its convention sends |x> to |x composed with pi inverse>. -/
def permutation (k : ℕ) (pi : Equiv.Perm (Fin k)) : Mat (Fin k → S) :=
  (Schur.tensorPermutation (Fintype.card S) k pi).submatrix
    (fun x i => Fintype.equivFin S (x i)) (fun x i => Fintype.equivFin S (x i))

/-- p.13, (15): symmetric-subspace projection. -/
def tensorSymmetrizer (S : Type*) [Fintype S] [DecidableEq S] (k : ℕ) :
    Mat (Fin k → S) := symmetryControlAverage (permutation (S := S) k)

/-- p.13, (79)–(80): permute only the B shares of k copies of AB. -/
def pureBipFamily (k : ℕ) (pi : Equiv.Perm (Fin k)) : Mat (Fin k → A × B) :=
  Matrix.of fun y x =>
    if (∀ i, (y i).1 = (x i).1) ∧ (∀ i, (y i).2 = (x (pi.symm i)).2) then 1 else 0

/-- p.13: actual control-return acceptance on k pure AB copies. -/
def bipartiteAcceptance (psi : EuclideanSpace ℂ (A × B)) (k : ℕ) : ℝ :=
  controlReturnProbability (symmetryControlAverage (pureBipFamily (A := A) (B := B) k)) (symmetryTensorCopies (pureDensity psi) k)

example (rho : Mat S) (x y : Fin 1 → S) : symmetryTensorCopies rho 1 x y = rho (x 0) (y 0) := by
  simp [symmetryTensorCopies, QAlgorithms.Papers.Independent.Information100.P60.copies]

/-- pp.4,14: full extension basis is (remaining B copies, retained AB). -/
def kFamily (n : ℕ) (pi : Equiv.Perm (Fin (n + 1))) :
    Mat ((Fin n → B) × (A × B)) :=
  Matrix.of fun y x =>
    if y.2.1 = x.2.1 ∧ Fin.cases y.2.2 y.1 = (Fin.cases x.2.2 x.1) ∘ pi.symm
      then 1 else 0

/-- p.14, (94): the extension computed from the pure-product mixture. -/
def separableExtension {X : Type*} [Fintype X] (p : X → ℝ)
    (a : X → EuclideanSpace ℂ A) (b : X → EuclideanSpace ℂ B) (n : ℕ) :
    Mat ((Fin n → B) × (A × B)) :=
  Matrix.of fun y z => ∑ x, (p x : ℂ) * pureDensity (a x) y.2.1 z.2.1 *
    ∏ i : Fin (n + 1), pureDensity (b x) (Fin.cases y.2.2 y.1 i) (Fin.cases z.2.2 z.1 i)

/-- p.14, (89): independent permutations of each party's k copies. -/
def multiPureFamily {m : ℕ} (d : Fin m → ℕ) (k : ℕ)
    (pi : Fin m → Equiv.Perm (Fin k)) : Mat ((i : Fin m) → Fin k → Fin (d i)) :=
  Matrix.of fun y x => if ∀ i, y i = x i ∘ (pi i).symm then 1 else 0

/-- p.14: regroup k copies so each party's copies are adjacent. -/
def multiCopies {m : ℕ} {d : Fin m → ℕ} (rho : Mat ((i : Fin m) → Fin (d i)))
    (k : ℕ) : Mat ((i : Fin m) → Fin k → Fin (d i)) :=
  Matrix.of fun x y => ∏ t, rho (fun i => x i t) (fun i => y i t)

/-- p.14: tensor product of the local symmetric projections. -/
def multiProjector {m : ℕ} (d : Fin m → ℕ) (k : ℕ) :
    Mat ((i : Fin m) → Fin k → Fin (d i)) :=
  Matrix.of fun x y => ∏ i, tensorSymmetrizer (Fin (d i)) k (x i) (y i)

/-- p.15, (97)–(107): remaining copies first, first copy of every party retained. -/
def multiFamily {m : ℕ} (d n : Fin m → ℕ)
    (pi : (i : Fin m) → Equiv.Perm (Fin (n i + 1))) :
    Mat (((i : Fin m) → Fin (n i) → Fin (d i)) × ((i : Fin m) → Fin (d i))) :=
  Matrix.of fun y x =>
    if ∀ i, Fin.cases (y.2 i) (y.1 i) = (Fin.cases (x.2 i) (x.1 i)) ∘ (pi i).symm
      then 1 else 0

/-- p.16, (121): conjugate input representation tensor output representation. -/
def choiFamily (U : G → Mat A) (V : G → Mat B) (g : G) : Mat (A × B) :=
  Matrix.kronecker ((U g).map conj) (V g)

/-- p.16: the supplied outcome-label permutation representation. -/
def outcomeMatrix {X : Type*} [DecidableEq X] (pi : Equiv.Perm X) : Mat X :=
  Matrix.of fun y x => if y = pi x then 1 else 0

/-- p.16, (124): the quantum-to-classical measurement channel. -/
def povmOutcomeChannel {X : Type*} [Fintype X] [DecidableEq X]
    (L : X → Mat S) : Superop S X :=
  fun rho => Matrix.diagonal fun x => (L x * rho).trace

/-- p.17: quantum-classical blocks are subnormalized; only their sum has trace one. -/
def qcBlockMatrix {X : Type*} [DecidableEq X] (b : X → Mat S) : Mat (S × X) :=
  Matrix.of fun x y => if x.2 = y.2 then b x.2 x.1 y.1 else 0

/-- p.18: root-fidelity values, distinct from the squared operational values. -/
def rootValues (rho : Mat S) (Q : Mat S → Prop) : Set ℝ :=
  {v | ∃ sigma, Q sigma ∧ v = rootFidelity rho sigma}

/-- p.18, (142)–(143): every SDP block and constraint, including the orientation of X†. -/
def stateSDP (rho : Mat S) (Q : Mat S → Prop) : Set ℝ :=
  {v | ∃ (X sigma : Mat S), sigma.PosSemidef ∧ sigma.trace = 1 ∧ Q sigma ∧
    (Matrix.fromBlocks rho Xᴴ X sigma).PosSemidef ∧ v = X.trace.re}

/-- p.18, (144)–(145): X,rho act on S, omega on RS, with Tr_R omega in the block. -/
def extensionSDP (rho : Mat S) (Q : Mat (R × S) → Prop) : Set ℝ :=
  {v | ∃ (X : Mat S) (omega : Mat (R × S)), omega.PosSemidef ∧ omega.trace = 1 ∧
    Q omega ∧ (Matrix.fromBlocks rho Xᴴ X (traceLeft omega)).PosSemidef ∧ v = X.trace.re}

example (rho : Mat S) (Q : Mat S → Prop) (v : ℝ) : v ∈ stateSDP rho Q ↔
    ∃ X sigma, sigma.PosSemidef ∧ sigma.trace = 1 ∧ Q sigma ∧
      (Matrix.fromBlocks rho Xᴴ X sigma).PosSemidef ∧ v = X.trace.re := Iff.rfl

/-- pp.18–19: irreducibility means no nontrivial invariant subspace, expressed
by its orthogonal projector. No scalar-commutant conclusion is assumed. -/
def IsIrreducibleUnitaryLift {d : ℕ} (U : G → Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  ∀ Q : Mat (Fin d), Qᴴ = Q → Q * Q = Q →
    (∀ g, Q * (U g : Mat (Fin d)) = (U g : Mat (Fin d)) * Q) → Q = 0 ∨ Q = 1

/-- pp.18–19: inequivalent irreducible unitary families have no unitary intertwiner. -/
def InequivalentFamilies {d e : ℕ}
    (U : G → Matrix.unitaryGroup (Fin d) ℂ) (V : G → Matrix.unitaryGroup (Fin e) ℂ) : Prop :=
  ¬ ∃ X : Matrix (Fin d) (Fin e) ℂ, Xᴴ * X = 1 ∧ X * Xᴴ = 1 ∧
    ∀ g, (U g : Mat (Fin d)) * X = X * (V g : Mat (Fin e))

/-- pp.18–19, (146)–(148): isotypic data defined through unitary intertwining
and inequivalent irreducibility, rather than the desired state parameterization.
The block families inherit the actual project's multiplier through intertwining. -/
structure IsotypicData (U : G → Mat S) where
  count : ℕ
  mult : Fin count → ℕ
  dim : Fin count → ℕ
  mult_pos : ∀ l, 0 < mult l
  dim_pos : ∀ l, 0 < dim l
  rep : (l : Fin count) → G → Matrix.unitaryGroup (Fin (dim l)) ℂ
  irreducible : ∀ l, IsIrreducibleUnitaryLift (rep l)
  inequivalent : ∀ l k, l ≠ k → InequivalentFamilies (rep l) (rep k)
  W : Matrix S (Σ l : Fin count, Fin (mult l) × Fin (dim l)) ℂ
  left_unitary : Wᴴ * W = 1
  right_unitary : W * Wᴴ = 1
  intertwines : ∀ g, U g = W *
    (Matrix.blockDiagonal' fun l => Matrix.kronecker (1 : Mat (Fin (mult l)))
      (rep l g : Mat (Fin (dim l)))) * Wᴴ

/-- p.18, (154): the state computed from multiplicity blocks. -/
def isotypicDensity {U : G → Mat S} (E : IsotypicData U)
    (b : (l : Fin E.count) → Mat (Fin (E.mult l))) : Mat S :=
  E.W * (Matrix.blockDiagonal' fun l => Matrix.kronecker (b l)
    ((E.dim l : ℂ)⁻¹ • (1 : Mat (Fin (E.dim l))))) * E.Wᴴ

/-- p.18, (153): trace out the irrep factor, retaining the multiplicity factor. -/
def schurBlocks {U : G → Mat S} (E : IsotypicData U) (rho : Mat S)
    (l : Fin E.count) : Mat (Fin (E.mult l)) :=
  traceRight ((E.Wᴴ * rho * E.W).submatrix (fun x => ⟨l, x⟩) (fun x => ⟨l, x⟩))

/-- p.19, (155)–(157): a multiplicity block is Bose-allowed only for the trivial irrep. -/
def TrivialBlock {U : G → Mat S} (E : IsotypicData U) (l : Fin E.count) : Prop :=
  ∀ g, (E.rep l g : Mat (Fin (E.dim l))) = 1

/-- p.23: normalized two-qubit singlet in the computational basis. -/
def booleanSinglet : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun p => if p = (false, true) then ((Real.sqrt 2)⁻¹ : ℂ)
    else if p = (true, false) then -((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.23, (160): SU(2) Haar integration uses the Borel sigma-algebra. -/
local instance su2MeasurableSpace : MeasurableSpace (Matrix.specialUnitaryGroup Bool ℂ) :=
  borel (Matrix.specialUnitaryGroup Bool ℂ)

/-- PDF p.23, (160): the chosen SU(2) sigma-algebra is Borel by construction. -/
local instance su2BorelSpace : BorelSpace (Matrix.specialUnitaryGroup Bool ℂ) :=
  ⟨rfl⟩

/-- PDF p.24, (171): U(2) Haar integration uses the Borel sigma-algebra. -/
local instance u2MeasurableSpace : MeasurableSpace (Matrix.unitaryGroup Bool ℂ) :=
  borel (Matrix.unitaryGroup Bool ℂ)

/-- PDF p.24, (171): the chosen U(2) sigma-algebra is Borel by construction. -/
local instance u2BorelSpace : BorelSpace (Matrix.unitaryGroup Bool ℂ) :=
  ⟨rfl⟩

example : su2MeasurableSpace = borel (Matrix.specialUnitaryGroup Bool ℂ) := rfl

example : u2MeasurableSpace = borel (Matrix.unitaryGroup Bool ℂ) := rfl

/-- p.23, (160): normalized Haar average of the collective SU(2) action. -/
def collectiveSU2Average (mu : Measure (Matrix.specialUnitaryGroup Bool ℂ)) : Mat (Bool × Bool) :=
  ∫ U, Matrix.kronecker (U : Mat Bool) (U : Mat Bool) ∂mu

/-- p.23, (165): rotation about the Pauli axis a by theta. -/
def pauliAxisRotation (a : Mat Bool) (theta : ℝ) : Mat Bool :=
  (Real.cos (theta / 2) : ℂ) • 1 - (Complex.I * Real.sin (theta / 2)) • a

/-- p.23, (163): bilateral rotation at the paper's sign convention. -/
def bilateral (a : Mat Bool) : Mat (Bool × Bool) :=
  Matrix.kronecker (pauliAxisRotation a (-Real.pi / 2)) (pauliAxisRotation a (-Real.pi / 2))

/-- p.23, (166): literal list of twelve products, retaining their matrix phases. -/
def twelveRotations : List (Mat (Bool × Bool)) :=
  let x := bilateral pauliX
  let y := bilateral pauliY
  let z := bilateral pauliZ
  [1, x*x, y*y, z*z, x*y, y*z, z*x, y*x,
    x*y*x*y, y*z*y*z, z*x*z*x, y*x*y*x]

example : twelveRotations.length = 12 := rfl

/-- pp.26–28: the number of one bits. -/
def bitHammingWeight {n : ℕ} (x : Qubits n) : ℕ := (Finset.univ.filter fun i => x i = true).card

/-- pp.26–28: projector onto the entire weight-k sector. -/
def weightProjector (n k : ℕ) : Mat (Qubits n) :=
  Matrix.diagonal fun x => if bitHammingWeight x = k then 1 else 0

/-- p.26, (175)–(178): collective phase; subtraction takes place in the reals. -/
def collectiveZRotation (n : ℕ) (phi : ℝ) : Mat (Qubits n) :=
  Matrix.diagonal fun x => Complex.exp
    (Complex.I * (((2 * (bitHammingWeight x : ℝ) - (n : ℝ)) * phi / 2 : ℝ) : ℂ))

/-- p.26, (174): normalized integral over the complete 4pi period. -/
def collectiveZAverage (n : ℕ) : Mat (Qubits n) :=
  (4 * Real.pi : ℂ)⁻¹ • ∫ phi in (0 : ℝ)..(4 * Real.pi), collectiveZRotation n phi

/-- p.26, (183): the literal finite unitary family; no odd-n group law is asserted. -/
def finitePhase (n : ℕ) (y : Fin (n + 1)) : Mat (Qubits n) :=
  Matrix.diagonal fun x => Complex.exp (Complex.I *
    ((Real.pi * (2 * (y.val : ℝ) - (n : ℝ)) *
      (2 * (bitHammingWeight x : ℝ) - (n : ℝ)) / ((n : ℝ) + 1) : ℝ) : ℂ))

/-- p.27, (197): continuous collective dephasing. -/
def collectiveZTwirl (n : ℕ) (rho : Mat (Qubits n)) : Mat (Qubits n) :=
  (4 * Real.pi : ℂ)⁻¹ • ∫ phi in (0 : ℝ)..(4 * Real.pi),
    collectiveZRotation n phi * rho * (collectiveZRotation n phi)ᴴ

example : bitHammingWeight (fun _ : Fin 0 => false) = 0 := rfl

example (n k : ℕ) (x : Qubits n) : weightProjector n k x x =
    (if bitHammingWeight x = k then 1 else 0) := by simp [weightProjector]

/-- p.35, (244)–(245): k-extendible channels through their actual copy permutations. -/
def KChannel (n : ℕ) (N : Superop (A × B) (C × D)) : Prop :=
  IsChannel N ∧ ∃ M : Superop ((Fin n → B) × (A × B)) ((Fin n → D) × (C × D)),
    IsChannel M ∧ (∀ X, traceLeft (M X) = N (traceLeft X)) ∧
    ∀ pi X, M (kFamily (A := A) (B := B) n pi * X * (kFamily (A := A) (B := B) n pi)ᴴ) =
      kFamily (A := C) (B := D) n pi * M X * (kFamily (A := C) (B := D) n pi)ᴴ

/-- p.36, (255)–(258): k-Bose channels use symmetric support, not covariance. -/
def KBoseChannel (n : ℕ) (N : Superop (A × B) (C × D)) : Prop :=
  IsChannel N ∧ ∃ M : Superop ((Fin n → B) × (A × B)) ((Fin n → D) × (C × D)),
    IsChannel M ∧ (∀ X, traceLeft (M X) = N (traceLeft X)) ∧
    (hsChannelAdjoint M (symmetryControlAverage (kFamily (A := C) (B := D) n)) -
      symmetryControlAverage (kFamily (A := A) (B := B) n)).PosSemidef

/-- Small definition checks, separate from the admitted source statements. -/

example : symmetryControlAverage (fun _ : Unit => (1 : Mat Bool)) = 1 := by simp [symmetryControlAverage]

example (rho : Mat S) : controlReturnProbability (1 : Mat S) rho = rho.trace.re := by
  simp [controlReturnProbability, effectProb]

example (X : Mat (P × S)) : firstChannel (fun Y : Mat P => Y) X = X := by
  ext a b
  rfl

example (Y : Mat Bool) : hsChannelAdjoint (fun X : Mat Bool => X) Y false true = Y false true := by
  simp [hsChannelAdjoint, Matrix.single_apply]

example : normalizedChoi (fun X : Mat Unit => X) ((), ()) ((), ()) = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P56.normalizedChoi]

example {X : Type*} [Fintype X] [DecidableEq X] (L : X → Mat S) (rho : Mat S) (x : X) :
    povmOutcomeChannel L rho x x = (L x * rho).trace := by
  simp [povmOutcomeChannel]

example (b : Bool → Mat S) (i j : S) : qcBlockMatrix b (i, false) (j, true) = 0 := rfl

example (rho : Mat S) (x y : Fin 0 → S) : symmetryTensorCopies rho 0 x y = 1 := by simp [symmetryTensorCopies, QAlgorithms.Papers.Independent.Information100.P60.copies]

example : booleanSinglet (false, false) = 0 := by simp [booleanSinglet]

example (a : Mat Bool) : pauliAxisRotation a 0 = 1 := by simp [pauliAxisRotation]

example (phi : ℝ) : collectiveZRotation 0 phi = 1 := by
  ext x y
  have h : x = y := Subsingleton.elim _ _
  subst y
  simp [collectiveZRotation, bitHammingWeight]

example : finitePhase 0 0 = 1 := by
  ext x y
  have h : x = y := Subsingleton.elim _ _
  subst y
  simp [finitePhase, bitHammingWeight]

end QAlgorithms.Papers.Independent.Extend50.P47


