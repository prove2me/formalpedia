-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P24
-- name    : QAlgorithms_Papers_Independent_Support50_P24
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T20:55:00.378991+00:00
-- url     : https://prove2.me/theorems/61292a59-1d0c-485b-a19f-70c096b2706c
-- title:
--   Definitions for Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly
-- statement:
--   The objects the formalized statements of *Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly* (arXiv:2209.02907) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Seven`: PDF pp.7,9: seven computational-basis wires, in printed order 1 through 7.
--   - `SevenMatrix`: PDF pp.7,9: operators in the computational basis of the seven wires.
--   - `QubitSU`: PDF p.7: the unknown forward qubit operation, with determinant one.
--   - `rotationY`: PDF p.9, S18: the source's real y rotation.
--   - `bitFlip`: PDF p.9, Fig.S2: Pauli X on a computational qubit.
--   - `controlledGate`: PDF pp.9-10, Figs.S2-S3: a known controlled gate; false is an open control. All wires other than the target retain their computational-basis labels.
--   - `sevenControlledSwap`: PDF pp.9-10: a swap, possibly with fixed computational-basis controls.
--   - `chronological`: PDF pp.9-10: chronological products act on column vectors from the right.
--   - `cgTwo`: PDF p.9, top of Fig.S2: complete three-wire CG circuit, including its padding. The arguments are i1,i2,0 in this order.
--   - `cgThree`: PDF p.9, bottom of Fig.S2: complete four-wire CG circuit. The arguments are j1,m1,m2,i3, and theta=2 arccos(sqrt(2/3)).
--   - `firstKnown`: PDF p.10, upper Fig.S3: the specified fixed V^(1), including every swap.
--   - `secondKnown`: PDF p.10, lower Fig.S3: the specified fixed V^(2), including every swap.
--   - `CallGate`: PDF pp.2,7: fixed known gates and forward unknown calls are distinct syntax. There is no constructor for an unknown adjoint or a controlled unknown operation.
--   - `PhysicalCalls`: PDF pp.2,7: physicality of the fixed inserted matrices, independent of U.
--   - `calls`: PDF pp.2,7: the query count counts exactly the forward-call constructors.
--   - `evaluateCalls`: PDF p.9, S19: evaluateCalls a circuit with the same U substituted at every call.
--   - `iteration`: PDF p.9, S19: one iteration f_U has two forward calls on printed wire 2.
--   - `fourCircuit`: PDF pp.7,9, S1,S21: the actual Fig.S1 circuit consists of two iterations.
--   - `catalyticCircuit`: PDF p.2, Eq.(1): remove only the first call, replacing its output by advice.
--   - `cleanCircuit`: PDF p.4: erase the U dependence of the returned catalyst with one more call.
--   - `sourceSinglet`: PDF p.7: the normalized singlet (|01>-|10>)/sqrt(2).
--   - `catalyst`: PDF p.2: the supplied catalyst is exactly (U tensor I)|singlet>.
--   - `inputEmbedding`: PDF p.9, S20,S24: input on wire 1, singlet on wires 2,3, zeros on 4,...,7.
--   - `swappedEmbedding`: PDF p.9, S25: singlet on wires 1,2, input on wire 3, zeros on 4,...,7.
--   - `catalyticInput`: PDF p.2, Eq.(1): catalyst on input wires 2,3 for that same U.
--   - `outputEmbedding`: PDF p.7, S1: returned catalyst on wires 1,2; the output qubit is wire 3.
--   - `discardExcept`: PDF pp.2,7: trace out all wires except q. The environment is enumerated once, by setting its unused q coordinate to false.
--   - `ExactInverter`: PDF p.2, Theorem 1: exact equality of the induced channel on every operator.
--   - `SequentialProtocol`: PDF pp.4,14, S58: an arbitrary fixed finite-memory causal circuit. Every stage is CPTP, hence includes measurements and classically controlled gates. The memory and all stages are chosen before the unknown U.
--   - `protocolOutput`: PDF p.14, S58: exactly n sequential forward calls, followed by memory discard. The n=0 case is just the fixed preparation channel and discard.
--   - `TensorCoordinates`: PDF pp.15-16: k input-side coordinates and k output-side coordinates.
--   - `CombCoordinates`: PDF pp.16,22: grouping (I1,...,In,F) and (P,O1,...,On).
--   - `GroupedComb`: PDF pp.15-16: operators on both groups of physical comb wires.
--   - `appendCoordinate`: PDF pp.15-16: append the last tensor coordinate, with the displayed wire order.
--   - `prependCoordinate`: PDF p.16: split off P, which is the first output-side coordinate.
--   - `causalMarginal`: PDF p.15, S64: C_(i-1)=Tr_(I_i O_(i-1))(C_i)/d; it is computed, not supplied.
--   - `SequentialFeasible`: PDF p.15, S63-S65: positivity and every causal equality, down to C_0=1. Level zero has one empty tensor word.
--   - `ParallelFeasible`: PDF p.16, S79-S81: one-slot comb for the n parallel calls, in explicit coordinates. B is the marginal Tr_F(C)/identity_(O^n), with Tr_(I^n)(B)=identity_P. These constraints are equivalent to the source's two partial-trace equalities.
--   - `groupAction`: PDF pp.3,22, S128: independent tensor-power actions on the two wire groups.
--   - `averagingKernel`: PDF p.22, S130: conjugation kernel for the concrete two-group Haar average.
--   - `averageComb`: PDF p.22, S130: Haar probability averaging, without a symmetry hypothesis on C.
--   - `performanceVector`: PDF p.16, S77: Choi vector U on (I_j,O_j) and on (F,P), with reference first. The factors are unnormalized; cyclic wire regrouping is explicit in the indices.
--   - `performanceKernel`: PDF p.16, S77: the unnormalized-Choi Haar kernel, with its 1/d^2 factor.
--   - `performanceOperator`: PDF p.16, S77: the actual performance operator, not an arbitrary invariant matrix.
--   - `inversionObjective`: PDF pp.3,16: real scalar average-fidelity objective Tr(C Omega).
--   - `refocusingNorm`: PDF p.26: the paper-specific Hilbert-Schmidt convention sqrt(Tr A†A)/2.
--   - `qubitChannelFidelity`: PDF pp.15,26, S66: squared normalized-Choi fidelity of two qubit unitary channels.
-- source:
--   Reversing Unknown Qubit-Unitary Operation, Deterministically and Exactly, arXiv:2209.02907v5, https://arxiv.org/abs/2209.02907v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

/-!
arXiv:2209.02907v5. Fixed forward-call circuits and inversion symmetry.
The reviewed, pinned Next46.P24 module supplies SU(d) Haar probability measure
and the physical one-call projectors. Its use is accepted-library reuse under
the independent-paper workflow. No unreviewed chunk is imported.
Wires in the local seven-qubit definitions are zero based: 0 means printed wire 1.
All channel equalities are equalities on matrices, hence include reference systems.
The general-f exactness assertion and four Young-coordinate results are deferred.
Compilation is pending the separately requested mechanical handoff.
-/

noncomputable section

open QAlgorithms MeasureTheory
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Support50.P24

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.7,9: seven computational-basis wires, in printed order 1 through 7. -/
abbrev Seven := Qubits 7

/-- PDF pp.7,9: operators in the computational basis of the seven wires. -/
abbrev SevenMatrix := Matrix Seven Seven ℂ

/-- PDF p.7: the unknown forward qubit operation, with determinant one. -/
abbrev QubitSU := Matrix.specialUnitaryGroup Bool ℂ

/-- PDF p.9, S18: the source's real y rotation. -/
def rotationY (angle : ℝ) : Matrix Bool Bool ℂ :=
  fun a b => if a = b then (Real.cos (angle / 2) : ℂ)
    else if a then (Real.sin (angle / 2) : ℂ) else -(Real.sin (angle / 2) : ℂ)

/-- PDF p.9, Fig.S2: Pauli X on a computational qubit. -/
def bitFlip : Matrix Bool Bool ℂ := fun a b => if a = !b then 1 else 0

/-- PDF pp.9-10, Figs.S2-S3: a known controlled gate; false is an open control.
All wires other than the target retain their computational-basis labels. -/
def controlledGate (controls : List (Fin 7 × Bool)) (target : Fin 7)
    (A : Matrix Bool Bool ℂ) : SevenMatrix :=
  fun x y => if ∀ i, i ≠ target → x i = y i then
    if ∀ c ∈ controls, y c.1 = c.2 then A (x target) (y target)
    else if x target = y target then 1 else 0
  else 0

/-- PDF pp.9-10: a swap, possibly with fixed computational-basis controls. -/
def sevenControlledSwap (controls : List (Fin 7 × Bool)) (a b : Fin 7) : SevenMatrix :=
  fun x y => if x = (if ∀ c ∈ controls, y c.1 = c.2 then
    Function.update (Function.update y a (y b)) b (y a) else y) then 1 else 0

/-- PDF pp.9-10: chronological products act on column vectors from the right. -/
def chronological (gates : List SevenMatrix) : SevenMatrix :=
  gates.foldl (fun accumulated gate => gate * accumulated) 1

/-- PDF p.9, top of Fig.S2: complete three-wire CG circuit, including its padding.
The arguments are i1,i2,0 in this order. -/
def cgTwo (a b c : Fin 7) : SevenMatrix :=
  chronological [
    controlledGate [(a,true),(b,true)] c bitFlip,
    controlledGate [(b,true)] a bitFlip,
    controlledGate [(c,false)] b (rotationY (Real.pi / 2)),
    controlledGate [(a,false),(c,false)] b (rotationY (Real.pi / 2)),
    controlledGate [(b,false)] a bitFlip,
    sevenControlledSwap [] a b,
    sevenControlledSwap [] b c]

/-- PDF p.9, bottom of Fig.S2: complete four-wire CG circuit.
The arguments are j1,m1,m2,i3, and theta=2 arccos(sqrt(2/3)). -/
def cgThree (a b c d : Fin 7) : SevenMatrix :=
  let theta := 2 * Real.arccos (Real.sqrt (2 / 3 : ℝ))
  chronological [
    controlledGate [(a,false)] c bitFlip,
    controlledGate [(c,true),(d,true)] b bitFlip,
    controlledGate [(d,true)] c bitFlip,
    controlledGate [(b,true)] c bitFlip,
    controlledGate [(b,false)] d (rotationY Real.pi),
    controlledGate [(a,true),(b,false),(c,true)] d (rotationY (-theta)),
    controlledGate [(a,true),(b,true),(c,true)] d (rotationY theta),
    controlledGate [(d,true)] a bitFlip,
    controlledGate [] a bitFlip,
    sevenControlledSwap [] b c,
    controlledGate [] b bitFlip,
    controlledGate [(a,true)] b bitFlip,
    sevenControlledSwap [(a,true)] b c,
    controlledGate [(a,true),(b,true)] c bitFlip]

/-- PDF p.10, upper Fig.S3: the specified fixed V^(1), including every swap. -/
def firstKnown : SevenMatrix :=
  chronological [sevenControlledSwap [] 2 5, cgTwo 0 1 2,
    controlledGate [(0,true)] 6 bitFlip, (cgThree 3 4 5 6)ᴴ,
    sevenControlledSwap [] 3 6, sevenControlledSwap [] 1 3]

/-- PDF p.10, lower Fig.S3: the specified fixed V^(2), including every swap. -/
def secondKnown : SevenMatrix :=
  chronological [sevenControlledSwap [] 1 3, cgThree 0 1 2 3,
    sevenControlledSwap [] 4 6, controlledGate [(4,true)] 3 bitFlip,
    sevenControlledSwap [] 5 6, (cgTwo 4 5 6)ᴴ,
    sevenControlledSwap [] 2 4, sevenControlledSwap [] 1 5, sevenControlledSwap [] 0 4]

/-- PDF pp.2,7: fixed known gates and forward unknown calls are distinct syntax.
There is no constructor for an unknown adjoint or a controlled unknown operation. -/
inductive CallGate where
  | known : SevenMatrix → CallGate
  | call : Fin 7 → CallGate

/-- PDF pp.2,7: physicality of the fixed inserted matrices, independent of U. -/
def PhysicalCalls (gates : List CallGate) : Prop :=
  ∀ gate ∈ gates, match gate with
    | .known A => A ∈ Matrix.unitaryGroup Seven ℂ
    | .call _ => True

/-- PDF pp.2,7: the query count counts exactly the forward-call constructors. -/
def calls (gates : List CallGate) : ℕ :=
  (gates.map fun gate => match gate with | .known _ => 0 | .call _ => 1).sum

/-- PDF p.9, S19: evaluateCalls a circuit with the same U substituted at every call. -/
def evaluateCalls (gates : List CallGate) (U : QubitSU) : SevenMatrix :=
  chronological (gates.map fun gate => match gate with
    | .known A => A
    | .call q => controlledGate [] q U.val)

/-- PDF p.9, S19: one iteration f_U has two forward calls on printed wire 2. -/
def iteration : List CallGate :=
  [.call 1, .known firstKnown, .call 1, .known secondKnown]

/-- PDF pp.7,9, S1,S21: the actual Fig.S1 circuit consists of two iterations. -/
def fourCircuit : List CallGate := iteration ++ iteration

/-- PDF p.2, Eq.(1): remove only the first call, replacing its output by advice. -/
def catalyticCircuit : List CallGate :=
  [.known firstKnown, .call 1, .known secondKnown] ++ iteration

/-- PDF p.4: erase the U dependence of the returned catalyst with one more call. -/
def cleanCircuit : List CallGate := fourCircuit ++ [.call 1]

/-- PDF p.7: the normalized singlet (|01>-|10>)/sqrt(2). -/
def sourceSinglet (a b : Bool) : ℂ :=
  QAlgorithms.Papers.Independent.Frontier18.P14.singlet
    ((if a then 1 else 0), (if b then 1 else 0))

/-- PDF p.2: the supplied catalyst is exactly (U tensor I)|singlet>. -/
def catalyst (U : QubitSU) (a b : Bool) : ℂ := ∑ c, U.val a c * sourceSinglet c b

/-- PDF p.9, S20,S24: input on wire 1, singlet on wires 2,3, zeros on 4,...,7. -/
def inputEmbedding : Matrix Seven Bool ℂ := fun x b =>
  if x 0 = b ∧ ∀ i : Fin 7, 3 ≤ i.val → x i = false then sourceSinglet (x 1) (x 2) else 0

/-- PDF p.9, S25: singlet on wires 1,2, input on wire 3, zeros on 4,...,7. -/
def swappedEmbedding : Matrix Seven Bool ℂ := fun x b =>
  if x 2 = b ∧ ∀ i : Fin 7, 3 ≤ i.val → x i = false then sourceSinglet (x 0) (x 1) else 0

/-- PDF p.2, Eq.(1): catalyst on input wires 2,3 for that same U. -/
def catalyticInput (U : QubitSU) : Matrix Seven Bool ℂ := fun x b =>
  if x 0 = b ∧ ∀ i : Fin 7, 3 ≤ i.val → x i = false then catalyst U (x 1) (x 2) else 0

/-- PDF p.7, S1: returned catalyst on wires 1,2; the output qubit is wire 3. -/
def outputEmbedding (U : QubitSU) : Matrix Seven Bool ℂ := fun x b =>
  if x 2 = b ∧ ∀ i : Fin 7, 3 ≤ i.val → x i = false then catalyst U (x 0) (x 1) else 0

/-- PDF pp.2,7: trace out all wires except q. The environment is enumerated once,
by setting its unused q coordinate to false. -/
def discardExcept (q : Fin 7) : Superop Seven Bool := fun X a b =>
  ∑ environment : Seven, if environment q = false then
    X (Function.update environment q a) (Function.update environment q b) else 0

/-- PDF p.2, Theorem 1: exact equality of the induced channel on every operator. -/
def ExactInverter (gates : List CallGate) : Prop :=
  ∀ U : QubitSU, ∀ A : Matrix Bool Bool ℂ,
    discardExcept 2 (conjSuperop (evaluateCalls gates U * inputEmbedding) A) =
      conjSuperop U.valᴴ A

/-- PDF pp.4,14, S58: an arbitrary fixed finite-memory causal circuit.
Every stage is CPTP, hence includes measurements and classically controlled gates.
The memory and all stages are chosen before the unknown U. -/
structure SequentialProtocol (n : ℕ) where
  memory : ℕ
  memoryPositive : 0 < memory
  prepare : Superop Bool (Bool × Fin memory)
  prepareChannel : IsChannel prepare
  afterCall : Fin n → Superop (Bool × Fin memory) (Bool × Fin memory)
  afterCallChannel : ∀ i, IsChannel (afterCall i)

/-- PDF p.14, S58: exactly n sequential forward calls, followed by memory discard.
The n=0 case is just the fixed preparation channel and discard. -/
def protocolOutput {n : ℕ} (A : SequentialProtocol n) (U : QubitSU) : Superop Bool Bool :=
  fun rho =>
    let query := Matrix.kronecker U.val (1 : Matrix (Fin A.memory) (Fin A.memory) ℂ)
    let joint := (List.finRange n).foldl
      (fun state i => A.afterCall i (conjSuperop query state)) (A.prepare rho)
    fun a b => ∑ m : Fin A.memory, joint (a,m) (b,m)

/-- PDF pp.15-16: k input-side coordinates and k output-side coordinates. -/
abbrev TensorCoordinates (d k : ℕ) := Fin k → Fin d

/-- PDF pp.16,22: grouping (I1,...,In,F) and (P,O1,...,On). -/
abbrev CombCoordinates (d k : ℕ) := TensorCoordinates d k × TensorCoordinates d k

/-- PDF pp.15-16: operators on both groups of physical comb wires. -/
abbrev GroupedComb (d k : ℕ) := Matrix (CombCoordinates d k) (CombCoordinates d k) ℂ

/-- PDF p.22: matrix Haar integrals use the finite entrywise topology. -/
local instance groupedContinuousENorm (d k : ℕ) : ContinuousENorm (GroupedComb d k) :=
  inferInstanceAs (ContinuousENorm (CombCoordinates d k → CombCoordinates d k → ℂ))

/-- PDF pp.15-16: append the last tensor coordinate, with the displayed wire order. -/
def appendCoordinate {d k : ℕ} (x : TensorCoordinates d k) (a : Fin d) :
    TensorCoordinates d (k+1) := Fin.lastCases a x

/-- PDF p.16: split off P, which is the first output-side coordinate. -/
def prependCoordinate {d k : ℕ} (a : Fin d) (x : TensorCoordinates d k) :
    TensorCoordinates d (k+1) := Fin.cases a x

/-- PDF p.15, S64: C_(i-1)=Tr_(I_i O_(i-1))(C_i)/d; it is computed, not supplied. -/
def causalMarginal {d k : ℕ} (C : GroupedComb d (k+1)) : GroupedComb d k :=
  fun x y => (∑ a : Fin d, ∑ b : Fin d,
    C (appendCoordinate x.1 a, appendCoordinate x.2 b)
      (appendCoordinate y.1 a, appendCoordinate y.2 b)) / (d : ℂ)

/-- PDF p.15, S63-S65: positivity and every causal equality, down to C_0=1.
Level zero has one empty tensor word. -/
def SequentialFeasible (d : ℕ) : (k : ℕ) → GroupedComb d k → Prop
  | 0, C => C = 1
  | k+1, C => C.PosSemidef ∧ SequentialFeasible d k (causalMarginal C) ∧
    ∀ (x y : TensorCoordinates d k) (s t : TensorCoordinates d (k+1)),
      (∑ a : Fin d, C (appendCoordinate x a,s) (appendCoordinate y a,t)) =
        causalMarginal C (x, fun i => s i.castSucc) (y, fun i => t i.castSucc) *
          (if s (Fin.last k) = t (Fin.last k) then 1 else 0)

/-- PDF p.16, S79-S81: one-slot comb for the n parallel calls, in explicit coordinates.
B is the marginal Tr_F(C)/identity_(O^n), with Tr_(I^n)(B)=identity_P.
These constraints are equivalent to the source's two partial-trace equalities. -/
def ParallelFeasible {d n : ℕ} (C : GroupedComb d (n+1)) : Prop :=
  C.PosSemidef ∧ ∃ B : Matrix (TensorCoordinates d n × Fin d)
      (TensorCoordinates d n × Fin d) ℂ, B.PosSemidef ∧
    (∀ (x y s t : TensorCoordinates d n) (p q : Fin d),
      (∑ a : Fin d, C (appendCoordinate x a,prependCoordinate p s)
        (appendCoordinate y a,prependCoordinate q t)) =
          B (x,p) (y,q) * (if s = t then 1 else 0)) ∧
    (∀ p q : Fin d, (∑ x : TensorCoordinates d n, B (x,p) (x,q)) =
      if p = q then 1 else 0)

/-- PDF pp.3,22, S128: independent tensor-power actions on the two wire groups. -/
def groupAction {d k : ℕ}
    (V W : Matrix.specialUnitaryGroup (Fin d) ℂ) : GroupedComb d k :=
  fun x y => (∏ i, V.val (x.1 i) (y.1 i)) * (∏ i, W.val (x.2 i) (y.2 i))

/-- PDF p.22, S130: conjugation kernel for the concrete two-group Haar average. -/
def averagingKernel {d k : ℕ} (C : GroupedComb d k)
    (z : Matrix.specialUnitaryGroup (Fin d) ℂ × Matrix.specialUnitaryGroup (Fin d) ℂ) :
    GroupedComb d k := groupAction z.1 z.2 * C * (groupAction z.1 z.2)ᴴ

/-- PDF p.22, S130: Haar probability averaging, without a symmetry hypothesis on C. -/
def averageComb {d k : ℕ} (C : GroupedComb d k) : GroupedComb d k :=
  ∫ z, averagingKernel C z ∂
    (QAlgorithms.Papers.Independent.Next46.P24.haar d).prod
      (QAlgorithms.Papers.Independent.Next46.P24.haar d)

/-- PDF p.16, S77: Choi vector U on (I_j,O_j) and on (F,P), with reference first.
The factors are unnormalized; cyclic wire regrouping is explicit in the indices. -/
def performanceVector {d n : ℕ} (U : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    CombCoordinates d (n+1) → ℂ := fun x =>
  U.val (x.2 0) (x.1 (Fin.last n)) *
    ∏ i : Fin n, U.val (x.2 i.succ) (x.1 i.castSucc)

/-- PDF p.16, S77: the unnormalized-Choi Haar kernel, with its 1/d^2 factor. -/
def performanceKernel {d n : ℕ} (U : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    GroupedComb d (n+1) :=
  fun x y => performanceVector U x * conj (performanceVector U y) / (d : ℂ)^2

/-- PDF p.16, S77: the actual performance operator, not an arbitrary invariant matrix. -/
def performanceOperator (d n : ℕ) : GroupedComb d (n+1) :=
  ∫ U, performanceKernel U ∂QAlgorithms.Papers.Independent.Next46.P24.haar d

/-- PDF pp.3,16: real scalar average-fidelity objective Tr(C Omega). -/
def inversionObjective {d n : ℕ} (C : GroupedComb d (n+1)) : ℝ :=
  (C * performanceOperator d n).trace.re

/-- PDF p.26: the paper-specific Hilbert-Schmidt convention sqrt(Tr A†A)/2. -/
def refocusingNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt ((Aᴴ * A).trace.re) / 2

/-- PDF pp.15,26, S66: squared normalized-Choi fidelity of two qubit unitary channels. -/
def qubitChannelFidelity (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq ((Aᴴ * B).trace) / 4

example : rotationY 0 = 1 := by
  ext a b
  by_cases h : a = b <;> simp [rotationY, Matrix.one_apply, h]

example : sourceSinglet false false = 0 := by simp [sourceSinglet, QAlgorithms.Papers.Independent.Frontier18.P14.singlet]

example : calls fourCircuit = 4 ∧ calls catalyticCircuit = 3 ∧ calls cleanCircuit = 5 := by
  norm_num [calls, fourCircuit, catalyticCircuit, cleanCircuit, iteration]

example (A : SequentialProtocol 0) (U V : QubitSU) : protocolOutput A U = protocolOutput A V := by
  rfl

example (d : ℕ) (x : TensorCoordinates d 0) (a : Fin d) :
    appendCoordinate x a (Fin.last 0) = a := by
  change Fin.lastCases a x (Fin.last 0) = a
  exact Fin.lastCases_last

end QAlgorithms.Papers.Independent.Support50.P24


