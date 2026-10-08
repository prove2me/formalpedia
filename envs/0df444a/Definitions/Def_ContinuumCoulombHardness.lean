-- Prove2me | Definitions.Def_ContinuumCoulombHardness
-- name    : ContinuumCoulombHardness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.24832+00:00
-- url     : https://prove2.me/theorems/e643b5f3-9785-4e88-b12e-afb5538f54d7
-- statement:
--   The block formalizes continuum electronic Coulomb energy, encoded decision problems, and QMA hardness. A binary codec encodes an object as a finite Boolean list and decodes an encoded object followed by any tail back to that object and the untouched tail. Explicit codecs, with this recovery property, handle binary and unary natural numbers, signed integers, pairs, lists, tagged alternatives, and transport along bijections. For n spin-½ electrons, configurations lie in ℝ³ⁿ and spin assignments in {0,1}ⁿ. An H¹ state consists of complex wavefunctions for every spin assignment and square-integrable weak first derivatives, with the derivative identity tested against smooth compactly supported real functions. Antisymmetry requires simultaneous permutation of particle positions and spins to multiply the wavefunction by the permutation sign almost everywhere. The squared norm is the sum of integrals of |ψ|² over spins. For distinct nuclear positions Rⱼ and charges Zⱼ≥1, the energy form is the spin-summed integral of ½∑ᵢ|∇ᵢψ|²−(∑ᵢ,ⱼZⱼ/|xᵢ−Rⱼ|)|ψ|²+(∑ᵢ<ₖ1/|xᵢ−xₖ|)|ψ|²; it contains no nucleus–nucleus term, and the formal reciprocal kernel takes value zero at zero. Ground energy is the extended-real infimum of this form over antisymmetric states of squared norm one. Nuclear input data require positive numbers of nuclei and electrons, distinct rational positions, and positive integer charges; a second version assigns every charge one, and the embedding of rational positions into real space is shown injective. Encoded instances store nuclear positions as triples of signed-numerator/natural-denominator fractions, the electron count in unary, and rational thresholds a,b. Validity requires positive denominators, the preceding positivity and distinctness conditions, and b−a≥1. The general-charge and unit-charge promise problems declare valid instances yes when ground energy is at most a and no when it is at least b; the gap proves these sets disjoint. Separately, quantum circuits use Hadamard, T, and controlled-NOT gates on work+1 qubits, with at most work witness qubits and valid, distinct controlled-NOT indices. Tensor-product gate matrices and ordered matrix multiplication specify circuit evolution; the witness occupies the initial qubits, all others start at zero, and acceptance is the probability that the last qubit is one. A verifier assumes polynomial-time classical circuit generation under the explicit encoding and a polynomial bound on work plus gate count. InQMA is the defined proposition that some such verifier accepts some normalized witness with probability at least 2/3 on every yes instance and accepts every normalized witness with probability at most 1/3 on every no instance. Polynomial many-one reductions preserve yes and no instances and are polynomial-time Turing-machine computable under the specified encodings. QMAHard is the defined proposition that every bit-string promise problem in QMA admits such a reduction to the target problem; the block does not assert that either Coulomb problem has this property.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContinuumCoulombHardness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContinuumCoulombHardness.lean; bytes 16..20468
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb.BinaryEncoding

abbrev BitString := List Bool

structure Codec (α : Type*) where
  encode : α → BitString
  read : BitString → α × BitString
  read_encode : ∀ x tail, read (encode x ++ tail) = (x, tail)

def encodeDigits : BitString → BitString
  | [] => [false]
  | b :: bs => true :: b :: encodeDigits bs

def readDigits : BitString → BitString × BitString
  | true :: b :: bs => let (digits, tail) := readDigits bs; (b :: digits, tail)
  | false :: bs => ([], bs)
  | _ => ([], [])

theorem readDigits_encode (digits tail : BitString) :
    readDigits (encodeDigits digits ++ tail) = (digits, tail) := by
  induction digits with
  | nil => rfl
  | cons b digits ih => simp only [encodeDigits, List.cons_append, readDigits, ih]

def decodeDigits : BitString → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (decodeDigits bs)

theorem decodeDigits_bits (n : ℕ) : decodeDigits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => simp only [Nat.bits_append_bit n b h, decodeDigits, ih]

def natural : Codec ℕ where
  encode n := encodeDigits n.bits
  read s := let (digits, tail) := readDigits s; (decodeDigits digits, tail)
  read_encode n tail := by simp only [readDigits_encode, decodeDigits_bits]

def encodeUnary : ℕ → BitString
  | 0 => [false]
  | n + 1 => true :: encodeUnary n

def readUnary : BitString → ℕ × BitString
  | true :: s => let (n, tail) := readUnary s; (n + 1, tail)
  | false :: s => (0, s)
  | [] => (0, [])

theorem readUnary_encode (n : ℕ) (tail : BitString) :
    readUnary (encodeUnary n ++ tail) = (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encodeUnary, List.cons_append, readUnary, ih]

def unary : Codec ℕ where
  encode := encodeUnary
  read := readUnary
  read_encode := readUnary_encode

def integer : Codec ℤ where
  encode
    | Int.ofNat n => false :: natural.encode n
    | Int.negSucc n => true :: natural.encode n
  read
    | false :: s => let (n, tail) := natural.read s; (Int.ofNat n, tail)
    | true :: s => let (n, tail) := natural.read s; (Int.negSucc n, tail)
    | [] => (0, [])
  read_encode z tail := by
    cases z <;> simp only [List.cons_append, natural.read_encode]

def pair {α β : Type*} (a : Codec α) (b : Codec β) : Codec (α × β) where
  encode x := a.encode x.1 ++ b.encode x.2
  read s := let (x, t) := a.read s; let (y, u) := b.read t; ((x, y), u)
  read_encode x tail := by
    rcases x with ⟨x, y⟩
    simp only [List.append_assoc, a.read_encode, b.read_encode]

def readCount {α : Type*} (a : Codec α) : ℕ → BitString → List α × BitString
  | 0, s => ([], s)
  | n + 1, s => let (x, t) := a.read s; let (xs, u) := readCount a n t; (x :: xs, u)

theorem readCount_encode {α : Type*} (a : Codec α) (xs : List α) (tail : BitString) :
    readCount a xs.length (xs.flatMap a.encode ++ tail) = (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readCount, a.read_encode, ih]

def list {α : Type*} (a : Codec α) : Codec (List α) where
  encode xs := natural.encode xs.length ++ xs.flatMap a.encode
  read s := let (n, t) := natural.read s; readCount a n t
  read_encode xs tail := by
    simp only [List.append_assoc, natural.read_encode, readCount_encode]

def equiv {α β : Type*} (a : Codec α) (e : β ≃ α) : Codec β where
  encode x := a.encode (e x)
  read s := let (x, t) := a.read s; (e.symm x, t)
  read_encode x tail := by simp only [a.read_encode, e.symm_apply_apply]

def sum {α β : Type*} (a : Codec α) (b : Codec β) : Codec (α ⊕ β) where
  encode
    | Sum.inl x => false :: a.encode x
    | Sum.inr y => true :: b.encode y
  read
    | false :: s => let (x, t) := a.read s; (Sum.inl x, t)
    | true :: s => let (y, t) := b.read s; (Sum.inr y, t)
    | [] => let (x, t) := a.read []; (Sum.inl x, t)
  read_encode x tail := by
    cases x <;> simp only [List.cons_append, a.read_encode, b.read_encode]

end ContinuumCoulomb.BinaryEncoding

namespace Coulomb

open scoped ENNReal Classical NNReal ComplexConjugate

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 3)
abbrev Spins (n : ℕ) := Fin n → Fin 2

structure Nuclei (M : ℕ) where
  nonempty : 0 < M
  position : Fin M → Space
  distinct : Function.Injective position
  charge : Fin M → ℝ
  charge_ge_one : ∀ j, 1 ≤ charge j

noncomputable def position {n : ℕ} (x : Configuration n) (i : Fin n) : Space :=
  WithLp.toLp 2 (fun b => x (i, b))

noncomputable def coulombKernel (x : Space) : ℝ := ‖x‖⁻¹

noncomputable def attraction {M : ℕ} (S : Nuclei M) (x : Space) : ℝ :=
  ∑ j, S.charge j * coulombKernel (x - S.position j)

noncomputable def permute {n : ℕ} (p : Equiv.Perm (Fin n))
    (x : Configuration n) : Configuration n :=
  WithLp.toLp 2 (fun ib => x (p ib.1, ib.2))

structure H1Vector (n : ℕ) where
  value : Spins n → Configuration n → ℂ
  gradient : Spins n → (Fin n × Fin 3) → Configuration n → ℂ
  value_L2 : ∀ s, MemLp (value s) 2 volume
  partial_L2 : ∀ s a, MemLp (gradient s a) 2 volume
  weak_partial : ∀ s a (φ : Configuration n → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, value s x * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ x, gradient s a x * (φ x : ℂ))

def Antisymmetric {n : ℕ} (ψ : H1Vector n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (s : Spins n),
    ∀ᵐ x ∂volume,
      ψ.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ) * ψ.value s x

noncomputable def mass {n : ℕ} (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, ‖ψ.value s x‖ ^ 2

noncomputable def kinetic {n : ℕ} (ψ : H1Vector n) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x, ‖ψ.gradient s a x‖ ^ 2

noncomputable def nuclearEnergy {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, (∑ i, attraction S (position x i)) * ‖ψ.value s x‖ ^ 2

noncomputable def pairEnergy {n : ℕ} (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, (∑ i : Fin n, ∑ j : Fin n,
    if i < j then coulombKernel (position x i - position x j) else 0) *
      ‖ψ.value s x‖ ^ 2

noncomputable def form {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : ℝ :=
  kinetic ψ - nuclearEnergy S ψ + pairEnergy ψ

end Coulomb

namespace ContinuumCoulomb

open BinaryEncoding Matrix
open scoped Kronecker

abbrev SourceSpinBasis (n : ℕ) := Fin n → Fin 2

def sourceTensor (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ := fun s t => ∏ i, M i (s i) (t i)

section

theorem bellScale_atLeastTwo : Nat.AtLeastTwo (1 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

attribute [local instance] bellScale_atLeastTwo

def bellScale : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

end

inductive QMAGate where
  | hadamard (qubit : ℕ)
  | phaseT (qubit : ℕ)
  | controlledNot (control target : ℕ)
  deriving DecidableEq, Repr

def qmaGateEquiv : QMAGate ≃ ((ℕ ⊕ ℕ) ⊕ (ℕ × ℕ)) where
  toFun
    | .hadamard i => Sum.inl (Sum.inl i)
    | .phaseT i => Sum.inl (Sum.inr i)
    | .controlledNot i j => Sum.inr (i, j)
  invFun
    | Sum.inl (Sum.inl i) => .hadamard i
    | Sum.inl (Sum.inr i) => .phaseT i
    | Sum.inr (i, j) => .controlledNot i j
  left_inv g := by cases g <;> rfl
  right_inv g := by rcases g with (i | i) | ⟨i, j⟩ <;> rfl

def qmaGateCodec : Codec QMAGate := BinaryEncoding.equiv
  (BinaryEncoding.sum (BinaryEncoding.sum natural natural) (pair natural natural)) qmaGateEquiv

structure QMACircuit where
  work : ℕ
  witness : ℕ
  gates : List QMAGate
  deriving DecidableEq, Repr

def qmaCircuitEquiv : QMACircuit ≃ (ℕ × (ℕ × List QMAGate)) where
  toFun c := (c.work, c.witness, c.gates)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨n, w, gs⟩; rfl

def qmaCircuitCodec : Codec QMACircuit := BinaryEncoding.equiv
  (pair natural (pair natural (BinaryEncoding.list qmaGateCodec))) qmaCircuitEquiv

def QMAGate.WellFormed (n : ℕ) : QMAGate → Prop
  | .hadamard i => i < n
  | .phaseT i => i < n
  | .controlledNot i j => i < n ∧ j < n ∧ i ≠ j

def QMACircuit.WellFormed (c : QMACircuit) : Prop :=
  c.witness ≤ c.work ∧ ∀ g ∈ c.gates, g.WellFormed (c.work + 1)

def qmaHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  bellScale • !![1, 1; 1, -1]

def qmaPhaseT : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, bellScale * (1 + Complex.I)]

def qmaQubit (work index : ℕ) : Fin (work + 1) :=
  ⟨index % (work + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def qmaControlledNot (work : ℕ) (control target : Fin (work + 1))
    (s : SourceSpinBasis (work + 1)) : SourceSpinBasis (work + 1) :=
  fun i => if i = target ∧ s control = 1 then Equiv.swap (0 : Fin 2) 1 (s i) else s i

def qmaGateMatrix (work : ℕ) : QMAGate →
    Matrix (SourceSpinBasis (work + 1)) (SourceSpinBasis (work + 1)) ℂ
  | .hadamard i => sourceTensor (work + 1)
      (fun k => if k = qmaQubit work i then qmaHadamard else 1)
  | .phaseT i => sourceTensor (work + 1)
      (fun k => if k = qmaQubit work i then qmaPhaseT else 1)
  | .controlledNot i j => fun s t =>
      if s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j) t then 1 else 0

def qmaCircuitMatrix (c : QMACircuit) :
    Matrix (SourceSpinBasis (c.work + 1)) (SourceSpinBasis (c.work + 1)) ℂ :=
  c.gates.foldl (fun M g => qmaGateMatrix c.work g * M) 1

def qmaInitialState (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    SourceSpinBasis (c.work + 1) → ℂ :=
  fun s => if ∀ i : Fin (c.work + 1), c.witness ≤ i.val → s i = 0 then
    psi (fun i => s ⟨i.val, lt_of_lt_of_le i.isLt (hc.1.trans (Nat.le_succ _))⟩)
  else 0

def qmaAcceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) : ℝ :=
  ∑ s : SourceSpinBasis (c.work + 1),
    if s (Fin.last c.work) = 1 then
      Complex.normSq ((qmaCircuitMatrix c).mulVec (qmaInitialState c hc psi) s) else 0

structure QuantumVerifier where
  generate : BitString → QMACircuit
  uniform : Turing.TM2ComputableInPolyTime id qmaCircuitCodec.encode generate
  size : Polynomial ℕ
  size_bound : ∀ x, (generate x).work + (generate x).gates.length ≤ size.eval x.length
  wellFormed : ∀ x, (generate x).WellFormed

structure PromiseProblem (α : Type) where
  yes : Set α
  no : Set α
  disjoint : @Disjoint (Set α)
    (@ChainCompletePartialOrder.toPartialOrder (Set α)
      (@ChainCompletePartialOrder.instOfCompleteLattice (Set α)
        (@CompleteBooleanAlgebra.toCompleteLattice (Set α)
          (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set α)
            (@Set.instCompleteAtomicBooleanAlgebra α)))))
    (@HeytingAlgebra.toOrderBot (Set α)
      (@Order.Frame.toHeytingAlgebra (Set α)
        (@CompleteDistribLattice.toFrame (Set α)
          (@CompleteBooleanAlgebra.toCompleteDistribLattice (Set α)
            (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set α)
              (@Set.instCompleteAtomicBooleanAlgebra α))))))
    yes no

section

theorem inQMA_two_atLeastTwo : Nat.AtLeastTwo (1 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

theorem inQMA_three_atLeastTwo : Nat.AtLeastTwo (2 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 2 (@Nat.instNeZeroSucc 1)

attribute [local instance] inQMA_two_atLeastTwo inQMA_three_atLeastTwo

def InQMA (P : PromiseProblem BitString) : Prop :=
  ∃ V : QuantumVerifier,
    (∀ x ∈ P.yes, ∃ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖ = 1 ∧ 2 / 3 ≤ qmaAcceptance (V.generate x) (V.wellFormed x) psi) ∧
    (∀ x ∈ P.no, ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖ = 1 → qmaAcceptance (V.generate x) (V.wellFormed x) psi ≤ 1 / 3)

end

structure PolynomialManyOne {α β : Type} (ea : α → BitString) (eb : β → BitString)
    (P : PromiseProblem α) (Q : PromiseProblem β) where
  map : α → β
  polynomialTime : Turing.TM2ComputableInPolyTime ea eb map
  maps_yes : ∀ x ∈ P.yes, map x ∈ Q.yes
  maps_no : ∀ x ∈ P.no, map x ∈ Q.no

def QMAHard {α : Type} (encoding : α → BitString) (Q : PromiseProblem α) : Prop :=
  ∀ P : PromiseProblem BitString, InQMA P → Nonempty (PolynomialManyOne id encoding P Q)

structure BinaryRational where
  numerator : ℤ
  denominator : ℕ
  deriving DecidableEq, Repr

def BinaryRational.value (q : BinaryRational) : ℚ :=
  (q.numerator : ℚ) / q.denominator

def binaryRationalEquiv : BinaryRational ≃ (ℤ × ℕ) where
  toFun q := (q.numerator, q.denominator)
  invFun q := ⟨q.1, q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

def binaryRationalCodec : Codec BinaryRational := BinaryEncoding.equiv (pair integer natural) binaryRationalEquiv

abbrev Position := Coulomb.Space
abbrev Configuration := Coulomb.Configuration
abbrev SpinConfiguration := Coulomb.Spins

structure NuclearData where
  nuclei : ℕ
  nuclei_pos : 0 < nuclei
  position : Fin nuclei → Fin 3 → ℚ
  distinct : Function.Injective position
  charge : Fin nuclei → ℕ
  charge_pos : ∀ a, 0 < charge a
  electrons : ℕ
  electrons_pos : 0 < electrons

structure UnitNuclearData where
  nuclei : ℕ
  nuclei_pos : 0 < nuclei
  position : Fin nuclei → Fin 3 → ℚ
  distinct : Function.Injective position
  electrons : ℕ
  electrons_pos : 0 < electrons

def UnitNuclearData.toNuclearData (d : UnitNuclearData) : NuclearData where
  nuclei := d.nuclei
  nuclei_pos := d.nuclei_pos
  position := d.position
  distinct := d.distinct
  charge := fun _ => 1
  charge_pos := fun _ => Nat.zero_lt_one
  electrons := d.electrons
  electrons_pos := d.electrons_pos

section

theorem realPosition_atLeastTwo : Nat.AtLeastTwo (1 + 1) :=
  @Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)

attribute [local instance] realPosition_atLeastTwo

def realPosition (r : Fin 3 → ℚ) : Position :=
  WithLp.toLp 2 (fun a => (r a : ℝ))

end

theorem realPosition_injective : Function.Injective realPosition := by
  intro r s hrs
  funext a
  have h := congrArg (fun p : Position => p a) hrs
  change (r a : ℝ) = (s a : ℝ) at h
  exact_mod_cast h

def NuclearData.toNuclei (d : NuclearData) : Coulomb.Nuclei d.nuclei where
  nonempty := d.nuclei_pos
  position := fun a => realPosition (d.position a)
  distinct := realPosition_injective.comp d.distinct
  charge := fun a => (d.charge a : ℝ)
  charge_ge_one := by
    intro a
    exact_mod_cast d.charge_pos a

abbrev FormState (n : ℕ) := {state : Coulomb.H1Vector n // Coulomb.Antisymmetric state}

abbrev normSq {n : ℕ} (state : FormState n) := Coulomb.mass state.val
abbrev kineticEnergy {n : ℕ} (state : FormState n) := Coulomb.kinetic state.val

def coulombForm (d : NuclearData) (state : FormState d.electrons) : ℝ :=
  Coulomb.form d.toNuclei state.val

def unitCoulombForm (d : UnitNuclearData) (state : FormState d.electrons) : ℝ :=
  coulombForm d.toNuclearData state

def groundEnergy (d : NuclearData) : EReal :=
  sInf {e | ∃ state : FormState d.electrons,
    normSq state = 1 ∧ e = (coulombForm d state : EReal)}

def unitGroundEnergy (d : UnitNuclearData) : EReal :=
  sInf {e | ∃ state : FormState d.electrons,
    normSq state = 1 ∧ e = (unitCoulombForm d state : EReal)}

structure BinaryPosition where
  x : BinaryRational
  y : BinaryRational
  z : BinaryRational
  deriving DecidableEq, Repr

def BinaryPosition.value (p : BinaryPosition) : Fin 3 → ℚ := ![p.x.value, p.y.value, p.z.value]

def BinaryPosition.Valid (p : BinaryPosition) : Prop :=
  0 < p.x.denominator ∧ 0 < p.y.denominator ∧ 0 < p.z.denominator

def binaryPositionEquiv : BinaryPosition ≃ (BinaryRational × (BinaryRational × BinaryRational)) where
  toFun p := (p.x, p.y, p.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

def binaryPositionCodec : Codec BinaryPosition := BinaryEncoding.equiv
  (pair binaryRationalCodec (pair binaryRationalCodec binaryRationalCodec)) binaryPositionEquiv

structure BinaryCoulomb where
  nuclei : List (BinaryPosition × ℕ)
  electrons : ℕ
  lower : BinaryRational
  upper : BinaryRational
  deriving DecidableEq, Repr

def binaryCoulombEquiv : BinaryCoulomb ≃
    (List (BinaryPosition × ℕ) × (ℕ × (BinaryRational × BinaryRational))) where
  toFun d := (d.nuclei, d.electrons, d.lower, d.upper)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨ns, n, a, b⟩; rfl

def binaryCoulombCodec : Codec BinaryCoulomb := BinaryEncoding.equiv
  (pair (BinaryEncoding.list (pair binaryPositionCodec natural))
    (pair unary (pair binaryRationalCodec binaryRationalCodec))) binaryCoulombEquiv

structure BinaryCoulomb.Valid (d : BinaryCoulomb) : Prop where
  nuclei_pos : 0 < d.nuclei.length
  electrons_pos : 0 < d.electrons
  positions : ∀ a : Fin d.nuclei.length, (d.nuclei.get a).1.Valid
  distinct : Function.Injective (fun a : Fin d.nuclei.length => (d.nuclei.get a).1.value)
  charge_pos : ∀ a : Fin d.nuclei.length, 0 < (d.nuclei.get a).2
  lower_denominator : 0 < d.lower.denominator
  upper_denominator : 0 < d.upper.denominator
  gap : 1 ≤ d.upper.value - d.lower.value

def BinaryCoulomb.toData (d : BinaryCoulomb) (h : d.Valid) : NuclearData where
  nuclei := d.nuclei.length
  nuclei_pos := h.nuclei_pos
  position a := (d.nuclei.get a).1.value
  distinct := h.distinct
  charge a := (d.nuclei.get a).2
  charge_pos := h.charge_pos
  electrons := d.electrons
  electrons_pos := h.electrons_pos

structure UnitCoulomb where
  nuclei : List BinaryPosition
  electrons : ℕ
  lower : BinaryRational
  upper : BinaryRational
  deriving DecidableEq, Repr

def unitCoulombEquiv : UnitCoulomb ≃ (List BinaryPosition × (ℕ × (BinaryRational × BinaryRational))) where
  toFun d := (d.nuclei, d.electrons, d.lower, d.upper)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨ns, n, a, b⟩; rfl

def unitCoulombCodec : Codec UnitCoulomb := BinaryEncoding.equiv
  (pair (BinaryEncoding.list binaryPositionCodec)
    (pair unary (pair binaryRationalCodec binaryRationalCodec))) unitCoulombEquiv

structure UnitCoulomb.Valid (d : UnitCoulomb) : Prop where
  nuclei_pos : 0 < d.nuclei.length
  electrons_pos : 0 < d.electrons
  positions : ∀ a : Fin d.nuclei.length, (d.nuclei.get a).Valid
  distinct : Function.Injective (fun a : Fin d.nuclei.length => (d.nuclei.get a).value)
  lower_denominator : 0 < d.lower.denominator
  upper_denominator : 0 < d.upper.denominator
  gap : 1 ≤ d.upper.value - d.lower.value

def UnitCoulomb.toData (d : UnitCoulomb) (h : d.Valid) : UnitNuclearData where
  nuclei := d.nuclei.length
  nuclei_pos := h.nuclei_pos
  position a := (d.nuclei.get a).value
  distinct := h.distinct
  electrons := d.electrons
  electrons_pos := h.electrons_pos

def binaryCoulombPromise : PromiseProblem BinaryCoulomb where
  yes := {d | ∃ h : d.Valid, groundEnergy (d.toData h) ≤ ((d.lower.value : ℝ) : EReal)}
  no := {d | ∃ h : d.Valid, ((d.upper.value : ℝ) : EReal) ≤ groundEnergy (d.toData h)}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro d ⟨h, hyes⟩ ⟨h', hno⟩
    have hgap : d.lower.value < d.upper.value := by linarith [h.gap]
    have hgap' : ((d.lower.value : ℝ) : EReal) < ((d.upper.value : ℝ) : EReal) := by exact_mod_cast hgap
    exact (not_le_of_gt hgap') (hno.trans hyes)

def unitCoulombPromise : PromiseProblem UnitCoulomb where
  yes := {d | ∃ h : d.Valid, unitGroundEnergy (d.toData h) ≤ ((d.lower.value : ℝ) : EReal)}
  no := {d | ∃ h : d.Valid, ((d.upper.value : ℝ) : EReal) ≤ unitGroundEnergy (d.toData h)}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro d ⟨h, hyes⟩ ⟨h', hno⟩
    have hgap : d.lower.value < d.upper.value := by linarith [h.gap]
    have hgap' : ((d.lower.value : ℝ) : EReal) < ((d.upper.value : ℝ) : EReal) := by exact_mod_cast hgap
    exact (not_le_of_gt hgap') (hno.trans hyes)



end ContinuumCoulomb
end
end OAI


