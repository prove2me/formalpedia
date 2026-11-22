-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_GCodedMachine
-- name    : QuantumKtSoI_Supplement_GCodedMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:36:14.839799+00:00
-- url     : https://prove2.me/theorems/06fe371d-2a22-4462-bc64-803419dd89b2
-- title:
--   Coded $\mathcal G'$-machines, the standard structural record, and the encoding hypothesis (Enc)
-- statement:
--   A **coded $\mathcal G'$-machine** is the complete finite structural description of a $\mathcal G'$-machine: the tape and state declarations and their kinds, the tape alphabets, the initial state and final states, and every classical transition row or gate, ordered active-tape tuple and move tuple. The valid coded $\mathcal G'$-machines are the $\mathcal G'$-machines that encodings encode.
--
--   An injective binary encoding $\ulcorner\cdot\urcorner'$ of the $\mathcal G'$-machines satisfies the **encoding hypothesis (Enc)** if
--
--   1. code validity is decidable in polynomial time;
--   2. a polynomial-time parser recovers the complete finite structural description from every code;
--   3. a code of length $m$ lists at most $m$ tapes;
--   4. all state and symbol labels have length polynomial in $m$.
--
--   The parser reads the names of gates from the fixed finite library; it need not approximate their matrix entries.
--
--   The measure $\mathrm{qKt}_{\mathcal G'}$ depends on such an encoding, and Theorems 9.6, D.45, D.47 and D.55 are stated for encodings satisfying (Enc).
--
--   **Formalization Note** The paper lists what the parser must recover without fixing an output format. The format is pinned to the **standard structural record**: the layout of the published encoding $\ulcorner\cdot\urcorner$ with gate names from the fixed enumeration of $\mathcal G'$, which contains exactly the listed data. The parser is a deterministic polynomial-time function mapping every code to that record. State and symbol labels are the state numbers and alphabet indices of the coded machine. Companions are the least-indexed valid choices, as on p.23.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 9.3 (Enc), p.118; machine encoding, p.23 and p.119

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QuantumKtSoI_Supplement_GMachine_outputProb
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- The code of one state of a coded `G′`-machine with `n` tapes and `s` states (p.23; Definition
9.3, p.118 of Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027
submission, held version sha256 6616571c…): as the published `StateCode`, with the gate of a gate
state taken from the library `L`. -/
inductive GStateCode (L : GateLib) (n s : ℕ)
  | final
  | classical (act : List (Fin n)) (rows : List (Fin s × List ℕ × (Fin n → Move)))
  | gate (g : L.ι) (tapes : Fin (L.arity g) → Fin n) (next : Fin s) (moves : Fin n → Move)

/-- A **coded `G′`-machine** (p.23; Definition 9.3, p.118): the complete finite structural
description of a `G′`-machine with tapes `0, …, k+1` (tape `0` the input tape, tape `1` the output
tape): a kind and an alphabet size for every tape, `s` states with an initial state, and the code
of every state (final; or its active tapes and transition table; or its gate, ordered active-tape
tuple, next state and move tuple). It is the published `CodedMachine` with gates from `L`. -/
structure GCodedMachine (L : GateLib) where
  k : ℕ
  qubit : Fin (k + 2) → Bool
  asize : Fin (k + 2) → ℕ
  s : ℕ
  init : Fin s
  states : Fin s → GStateCode L (k + 2) s

namespace GCodedMachine

variable {L : GateLib} (A : GCodedMachine L)

/-- The alphabet size of a tape (`3` for a qubit tape). -/
def asz (t : Fin (A.k + 2)) : ℕ := if A.qubit t then 3 else A.asize t

/-- The lexicographic index of the scanned active tuple, first active tape most significant. -/
def rowIndex (act : List (Fin (A.k + 2))) (σ : Fin (A.k + 2) → Sym) : ℕ :=
  act.foldl (fun acc t => acc * A.asz t + CodedMachine.symIdx (A.qubit t) (σ t)) 0

/-- The active tapes of a state code. -/
def actOf : GStateCode L (A.k + 2) A.s → List (Fin (A.k + 2))
  | .classical act _ => act
  | _ => []

/-- The transition of a state code on a scanned tuple (symbols are alphabet indices, read with the
published `CodedMachine.symOf`). -/
def δOf (p : Fin A.s) (σ : Fin (A.k + 2) → Sym) :
    Fin A.s × (Fin (A.k + 2) → Sym) × (Fin (A.k + 2) → Move) :=
  match A.states p with
  | .classical act rows =>
      let row := rows.getD (A.rowIndex act σ) (A.init, [], fun _ => Move.N)
      (row.1, fun t => CodedMachine.symOf (A.qubit t) (row.2.1.getD (act.idxOf t) 0), row.2.2)
  | _ => (p, σ, fun _ => Move.N)

/-- The `G′`-machine described by the code, before companions are fixed. -/
def preMachine : GMachine L where
  Q := Fin A.s
  T := Fin (A.k + 2)
  kind := fun t => if A.qubit t then TapeKind.qubit else TapeKind.classical
  alph := fun t => (Finset.range (A.asz t)).image (CodedMachine.symOf (A.qubit t))
  inT := 0
  outT := 1
  companion := id
  init := A.init
  isFinal := fun p => match A.states p with | .final => true | _ => false
  act := fun p => (A.actOf (A.states p)).toFinset
  δ := A.δOf
  gdata := fun p => match A.states p with | .gate g tp _ _ => some ⟨g, tp⟩ | _ => none
  gnext := fun p => match A.states p with | .gate _ _ nx _ => nx | _ => A.init
  gmove := fun p => match A.states p with | .gate _ _ _ mv => mv | _ => fun _ => Move.N

/-- The companion of a qubit tape (p.23): the least-indexed classical tape whose head makes the
same move as the head of the qubit tape in every transition row (the tape itself if there is
none, which `Valid` rules out). -/
def companionOf (t : Fin (A.k + 2)) : Fin (A.k + 2) :=
  if h : (Finset.univ.filter fun c : Fin (A.k + 2) => A.preMachine.IsCompanion c t).Nonempty then
    (Finset.univ.filter fun c : Fin (A.k + 2) => A.preMachine.IsCompanion c t).min' h
  else t

/-- The `G′`-machine `A` denotes, with the least-index companions of p.23. -/
def toMachine : GMachine L := { A.preMachine with companion := A.companionOf }

/-- Well-formedness of the code, as for the published `CodedMachine`: every qubit tape has the
alphabet-size field `3`, active tapes are listed in increasing order, and a classical table has
exactly one row per scanned active tuple, each row writing one symbol per active tape. -/
def WellFormed : Prop :=
  (∀ t, A.qubit t = true → A.asize t = 3) ∧
    ∀ p, match A.states p with
      | .classical act rows =>
          act.Pairwise (· < ·) ∧ rows.length = (act.map A.asz).prod ∧
            ∀ row ∈ rows, row.2.1.length = act.length
      | _ => True

/-- A **valid** code: well formed, and its machine is a `G′`-machine of Definition 9.3 with the
least-index companions. The valid coded `G′`-machines are "the `G′`-machines" that encodings
encode. -/
def Valid : Prop := A.WellFormed ∧ A.toMachine.Valid

/-- The binary code of one state code in the standard layout: the published
`CodedMachine.encState` with the gate name `L.idx g` in place of the native gate code. -/
def encState {n s : ℕ} : GStateCode L n s → List Bool
  | .final => sdNat 0
  | .classical act rows =>
      sdNat 1 ++ sdNat act.length ++ act.flatMap (fun t => sdNat t.val) ++ sdNat rows.length ++
        rows.flatMap fun r =>
          sdNat r.1.val ++ sdNat r.2.1.length ++ r.2.1.flatMap sdNat ++
            (List.finRange n).flatMap fun t => sdNat (CodedMachine.moveCode (r.2.2 t))
  | .gate g tp nx mv =>
      sdNat 2 ++ sdNat (L.idx g) ++ (List.finRange (L.arity g)).flatMap (fun i => sdNat (tp i).val) ++
        sdNat nx.val ++ (List.finRange n).flatMap fun t => sdNat (CodedMachine.moveCode (mv t))

/-- The **standard structural record** of a coded `G′`-machine: the layout of the published
encoding `CodedMachine.encode` (p.23) with gate names replaced by the names `L.idx` of the fixed
enumeration of `G′`: the number of tapes, the number of states, the kind and alphabet size of
every tape, the initial state, and the code of every state (finality; or active tapes and every
transition row; or gate name, ordered active-tape tuple, next state and move tuple). -/
def encodeStd : List Bool :=
  sdNat A.k ++ sdNat A.s ++
    (List.finRange (A.k + 2)).flatMap (fun t => sdNat (A.qubit t).toNat ++ sdNat (A.asize t)) ++
    sdNat A.init.val ++ (List.finRange A.s).flatMap fun p => encState (A.states p)

end GCodedMachine

/-- The **encoding hypothesis (Enc)** of Definition 9.3 (p.118) for an encoding `⌜·⌝′ = enc` of the
`G′`-machines (the valid coded `G′`-machines):
* `inj`: the encoding is injective;
* `valid_dec`: code validity is decidable in polynomial time (the indicator of the set of codes is
  computable in deterministic polynomial time);
* `parser`: a polynomial-time parser recovers the complete finite structural description: some
  deterministic polynomial-time computable `f` maps every code `⌜A⌝′` to the standard structural
  record `A.encodeStd`;
* `tapes`: a code of length `m` lists at most `m` tapes;
* `labels`: all state and symbol labels have length polynomial in `m`.

**Formalization Note** The paper lists what the parser must recover (tape and state declarations
and kinds, alphabets with blank and endmarker, initial and final states, every classical row or
gate index, ordered active-tape tuple and move tuple) without fixing an output format; the format
is pinned to `encodeStd`, the published encoding's layout with gate names from the fixed
enumeration, which contains exactly these data. Deterministic polynomial time is `PolyTimeFn`
(a valid native coded machine without gate states, `c(|z|+2)^k` steps). State labels are the
numbers below `A.s` and symbol labels the alphabet indices below `A.asize t`; their lengths are
`Nat.size`. Nothing is required of the parser on strings that are not codes. -/
structure EncHyp (L : GateLib) (enc : {A : GCodedMachine L // A.Valid} → List Bool) : Prop where
  inj : Function.Injective enc
  valid_dec : PolyTimeFn fun z => [decide (∃ A, enc A = z)]
  parser : ∃ f : List Bool → List Bool, PolyTimeFn f ∧ ∀ A, f (enc A) = A.1.encodeStd
  tapes : ∀ A, A.1.k + 2 ≤ (enc A).length
  labels : ∃ c k : ℕ, ∀ A, Nat.size A.1.s ≤ c * ((enc A).length + 2) ^ k ∧
    ∀ t, Nat.size (A.1.asize t) ≤ c * ((enc A).length + 2) ^ k

end QuantumKtSoI.Supplement


