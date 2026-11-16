-- Prove2me | Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Operations
-- name    : SuperactivatedCheating_StateConversion_Supplement_Operations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:18:24.99486+00:00
-- url     : https://prove2.me/theorems/3e9da007-7669-4c44-a29b-c519666446ca
-- title:
--   Exact zero-error codes, capacities and finite channel operations
-- statement:
--   Registers are finite sets, with complex matrices representing operators. The channel predicate and its finite normalized Kraus representation, and the density-operator predicate (positive semidefinite, trace one), are imported published objects. Tensor operations act on every matrix unit, including entangled inputs; a tensor word permits different input registers for its two branches.
--
--   For each positive message count $M$, a classical zero-error code has $M$ density operators with pairwise orthogonal channel outputs. An assisted classical code additionally chooses arbitrary finite private registers, a unit shared pure state, and an encoding channel for each message. A quantum code has fixed encoding and recovery channels that recover every density operator on $\mathbb C^M$ exactly. Its assisted counterpart encodes the input together with Alice’s share and recovers from the channel output and Bob’s share, without any initial communication.
--
--   For each task, its one-shot capacity is
--   $$X_0^{(1)}(N)=\sup\{\log_2 M:M\ge1\text{ is achievable}\}.$$
--   The classical, assisted classical, and quantum operational regularizations are $\sup_{k\ge1}X_0^{(1)}(N^{\otimes k})/k$. All capacities take values in $[0,\infty]$, avoiding empty or unbounded real-supremum defaults. The trivial one-message code is included. Finite-dimensional channel coding bounds and agreement with the assisted-capacity limit are conclusions to establish, never fields of a channel.
--
--   For a finite nonempty unitary 1-design $(U_j)_{j\in J}$ on a common output register, the OTP direct sum discards the off-diagonal input blocks and outputs
--   $$\frac1{|J|}\sum_j\bigl(E_0(\rho_{00})+U_jE_1(\rho_{11})U_j^\dagger\bigr)\otimes|j\rangle\langle j|.$$
--   The 1-design identity is imposed on every operator. Distinct input dimensions are permitted. These operations and operational coding notions form reusable finite-dimensional infrastructure.
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), §2 pp. 9–13, Definition 25 and Remark 26 p. 22, §§5.1–5.2 pp. 21, 25.

import Mathlib
import Definitions.Def_SuperactivatedCheating_StateConversion_QuantumGames
import Definitions.Def_WildeQIT_IsDensityOperator

noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement
open scoped Matrix ComplexConjugate ENNReal NNReal
open Matrix

/-! Finite-dimensional operations used in §§2, 4–6. Channels and states reuse the
published QAlgorithms.IsChannel and WildeQIT.IsDensityOperator without extra conditions. -/
abbrev Op (A : Type) := Matrix A A ℂ
abbrev Map (A B : Type) := QAlgorithms.Superop A B
abbrev Density {A : Type} [Fintype A] := @WildeQIT.IsDensityOperator A _

def tensor {A B : Type} (X : Op A) (Y : Op B) : Op (A × B) :=
  fun a b => X a.1 b.1 * Y a.2 b.2

def relabel {A B : Type} (f : B → A) (X : Op A) : Op B := fun i j => X (f i) (f j)

def tensorMap {A B C D : Type} [Fintype A] [Fintype C] [DecidableEq A]
    [DecidableEq C] (N : Map A B) (L : Map C D) : Map (A × C) (B × D) :=
  fun X o o' => ∑ i, ∑ j, ∑ k, ∑ l,
    X (i,k) (j,l) * N (Matrix.single i j 1) o.1 o'.1 * L (Matrix.single k l 1) o.2 o'.2

def tensorId {A B E : Type} (N : Map A B) : Map (A × E) (B × E) :=
  fun X o o' => N (fun i j => X (i,o.2) (j,o'.2)) o.1 o'.1

def piMap {I : Type} [Fintype I] [DecidableEq I] {A B : I → Type} [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] (N : ∀ i, Map (A i) (B i)) : Map (∀ i, A i) (∀ i, B i) :=
  fun X o o' => ∑ x, ∑ y, X x y * ∏ i, N i (Matrix.single (x i) (y i) 1) (o i) (o' i)

def power {A B : Type} [Fintype A] [DecidableEq A] (N : Map A B) (n : ℕ) :
    Map (Fin n → A) (Fin n → B) := piMap (fun _ => N)

def piOp {I : Type} [Fintype I] {A : I → Type} (X : ∀ i, Op (A i)) : Op (∀ i, A i) :=
  fun x y => ∏ i, X i (x i) (y i)

def unitVector {A : Type} [Fintype A] (v : A → ℂ) : Prop := ∑ i, ‖v i‖ ^ 2 = 1

def IsProjection {A : Type} [Fintype A] (P : Op A) : Prop := Pᴴ = P ∧ P * P = P

def bits (m : ℕ) : ℝ := Real.log m / Real.log 2

def bitValue (m : ℕ) : ℝ≥0∞ := ENNReal.ofReal (bits m)

/-- Supremum over positive message counts, in a complete lattice. M=1 is included. -/
def codingCapacity (achievable : ℕ → Prop) : ℝ≥0∞ :=
  ⨆ m : {m : ℕ // 0 < m ∧ achievable m}, bitValue m.val

/-- Local resources are product pure states; shared randomization cannot improve a supremum. -/
structure Shared where
  eA : ℕ
  eB : ℕ
  ψ : Fin eA × Fin eB → ℂ
  unit : unitVector ψ

def Shared.product (S : Shared) : Prop :=
  ∃ u : Fin S.eA → ℂ, ∃ v : Fin S.eB → ℂ,
    unitVector u ∧ unitVector v ∧ ∀ i j, S.ψ (i,j) = u i * v j

/-- Orthogonality of positive operators: disjoint supports, without approximate fidelity. -/
def orthogonal {B : Type} [Fintype B] (X Y : Op B) : Prop := X * Y = 0

/-- Definition 6 without assistance, §2.2 p.13. -/
def classicalCode {A B : Type} [Fintype A] [Fintype B] (N : Map A B) (m : ℕ) : Prop :=
  ∃ ρ : Fin m → Op A, (∀ i, Density (ρ i)) ∧
    ∀ i j, i ≠ j → orthogonal (N (ρ i)) (N (ρ j))

/-- Definition 6, eq. (2.1), p.13: no initial communication or bounded-entanglement restriction. -/
def assistedClassicalCode {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : Map A B) (m : ℕ) : Prop :=
  ∃ S : Shared, ∃ E : Fin m → Map (Fin S.eA) A,
    (∀ i, QAlgorithms.IsChannel (E i)) ∧
    ∀ i j, i ≠ j → orthogonal
      (tensorId (N ∘ E i) (pureState S.ψ)) (tensorId (N ∘ E j) (pureState S.ψ))

/-- Definition 7 without assistance: exact identity on every density, arbitrary dimension m. -/
def quantumCode {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Map A B) (m : ℕ) : Prop :=
  ∃ E : Map (Fin m) A, ∃ D : Map B (Fin m),
    QAlgorithms.IsChannel E ∧ QAlgorithms.IsChannel D ∧
      ∀ ρ, Density ρ → D (N (E ρ)) = ρ

/-- The actual encoded state before the channel, retaining Bob's prior share. -/
def encoded {A : Type} (S : Shared) {m : ℕ} (E : Map (Fin m × Fin S.eA) A)
    (ρ : Op (Fin m)) : Op (A × Fin S.eB) :=
  tensorId E (relabel (fun x : (Fin m × Fin S.eA) × Fin S.eB =>
    (x.1.1,(x.1.2,x.2))) (tensor ρ (pureState S.ψ)))

/-- Definition 7, eq. (2.2), p.13; fixed encoder and decoder, independent of the input state. -/
def assistedQuantumCode {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (N : Map A B) (m : ℕ) : Prop :=
  ∃ S : Shared, ∃ E : Map (Fin m × Fin S.eA) A, ∃ D : Map (B × Fin S.eB) (Fin m),
    QAlgorithms.IsChannel E ∧ QAlgorithms.IsChannel D ∧
      ∀ ρ, Density ρ → D (tensorId N (encoded S E ρ)) = ρ

def C1 {A B : Type} [Fintype A] [Fintype B] (N : Map A B) := codingCapacity (classicalCode N)
def CE1 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Map A B) :=
  codingCapacity (assistedClassicalCode N)
def Q1 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (N : Map A B) :=
  codingCapacity (quantumCode N)
def QE1 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (N : Map A B) :=
  codingCapacity (assistedQuantumCode N)

/-- Operational zero-error regularization, pp.21,25; k is positive, never division by zero. -/
def C0 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Map A B) : ℝ≥0∞ :=
  ⨆ k : ℕ+, C1 (power N k) / (k.val : ℝ≥0∞)
def CE0 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (N : Map A B) : ℝ≥0∞ :=
  ⨆ k : ℕ+, CE1 (power N k) / (k.val : ℝ≥0∞)
def Q0 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (N : Map A B) : ℝ≥0∞ :=
  ⨆ k : ℕ+, Q1 (power N k) / (k.val : ℝ≥0∞)

/-- Definition 25 and Remark 26, p.22. -/
def IsOneDesign {K J : Type} [Fintype K] [Fintype J] [DecidableEq K]
    (U : J → Op K) : Prop :=
  (∀ j, (U j)ᴴ * U j = 1 ∧ U j * (U j)ᴴ = 1) ∧
  ∀ X : Op K, (1 / (Fintype.card J : ℂ)) • (∑ j, U j * X * (U j)ᴴ) =
    (X.trace / (Fintype.card K : ℂ)) • (1 : Op K)

def otp {A B K J : Type} [Fintype K] [Fintype J] [DecidableEq J]
    (N : Map A K) (L : Map B K) (U : J → Op K) : Map (A ⊕ B) (K × J) :=
  fun X o o' => if o.2 = o'.2 then
    (1 / (Fintype.card J : ℂ)) *
      (N (fun i j => X (.inl i) (.inl j)) o.1 o'.1 +
       (U o.2 * L (fun i j => X (.inr i) (.inr j)) * (U o.2)ᴴ) o.1 o'.1)
    else 0

/-- Tensor word permits distinct input spaces. -/
def wordInput {A B : Type} {n : ℕ} (s : Fin n → Bool) (i : Fin n) : Type :=
  if s i then B else A

instance wordInputFintype {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (s : Fin n → Bool) (i : Fin n) : Fintype (wordInput (A := A) (B := B) s i) := by
  unfold wordInput
  split <;> infer_instance

instance wordInputDecidableEq {A B : Type} [DecidableEq A] [DecidableEq B] {n : ℕ}
    (s : Fin n → Bool) (i : Fin n) : DecidableEq (wordInput (A := A) (B := B) s i) := by
  unfold wordInput
  split <;> infer_instance

def wordMap {A B K : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Map A K) (L : Map B K) {n : ℕ} (s : Fin n → Bool) :
    Map (∀ i, wordInput (A := A) (B := B) s i) (Fin n → K) := by
  classical
  exact @piMap (Fin n) _ _ (wordInput (A := A) (B := B) s) (fun _ => K)
    (fun i => by unfold wordInput; split <;> infer_instance)
    (fun i => by unfold wordInput; split <;> infer_instance)
    (fun i => by
      cases h : s i
      · simpa [wordInput, h] using N
      · simpa [wordInput, h] using L)

end SuperactivatedCheating.StateConversion.Supplement


