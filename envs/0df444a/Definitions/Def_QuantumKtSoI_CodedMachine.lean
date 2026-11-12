-- Prove2me | Definitions.Def_QuantumKtSoI_CodedMachine
-- name    : QuantumKtSoI_CodedMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:36:50.090772+00:00
-- url     : https://prove2.me/theorems/923bd493-c4d7-4cc4-b22a-e58d2e851a3e
-- title:
--   Coded machines and the encoding $\ulcorner A\urcorner$
-- statement:
--   A **coded machine** is a concrete machine of Definition 3.1 given by finite data: tapes $0,\dots,k+1$ (tape $0$ the input tape, tape $1$ the output tape) with a kind and an alphabet size each, states $0,\dots,s-1$ with an initial state, and for every state its code: final; classical, with its active tapes in increasing order and its full transition table (one row per tuple of scanned active symbols, in lexicographic order, giving the next state, the symbols written on the active tapes and the move of every head); or a gate state, with its gate, its ordered tuple of active tapes, its next state and its move tuple. The companion of a qubit tape is the least-indexed classical tape whose head makes the same move in every transition row (p.23). A code is **valid** when it is well formed (one row per scanned tuple, alphabet field $3$ on qubit tapes) and its machine satisfies Definition 3.1.
--
--   The **encoding** $\ulcorner A\urcorner$ lists, in a fixed order, the numbers of tapes and states, the kind and alphabet size of every tape, the initial state, and the code of every state, each number written as its self-delimiting code $\bar m$.
--
--   Coded machines are the leaves $\mathrm{BASE}(A)$ of descriptions and the fixed machines of the lemmas (the universal machine, the exhaustive estimator, deterministic post-processors).
--
--   **Formalization Note** The paper fixes "a standard injective binary encoding" only by its contents (p.23); this is one such encoding, injective because every field is self-delimiting and its layout is determined by the earlier fields. By Corollary 9.5 (p.119) another admissible encoding changes $\mathrm{qKt}$ by at most $D\log(|x|+|y|+2)+D$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §3.2, pp.23–24; (Enc), p.118

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Machine_outputProb

open Classical

noncomputable section

namespace QuantumKtSoI

/-- The code of one state of a coded machine with `n` tapes and `s` states (p.23): a final state;
a classical state with its active tapes (an increasing list) and its full transition table, one
row `(next state, symbols written on the active tapes, move of every tape)` per tuple of scanned
active symbols in lexicographic order; or a gate state with its gate, its ordered tuple of active
tapes, its next state and its move tuple. Symbols are alphabet indices (see `CodedMachine.symOf`). -/
inductive StateCode (n s : ℕ)
  | final
  | classical (act : List (Fin n)) (rows : List (Fin s × List ℕ × (Fin n → Move)))
  | gate (g : Gate) (tapes : Fin g.arity → Fin n) (next : Fin s) (moves : Fin n → Move)

/-- A **coded machine** (p.23): a concrete machine of Definition 3.1 with tapes `0, …, k+1`
(tape `0` the input tape, tape `1` the output tape), a kind and an alphabet size for every tape,
`s` states with an initial state, and the code of every state. -/
structure CodedMachine where
  k : ℕ
  qubit : Fin (k + 2) → Bool
  asize : Fin (k + 2) → ℕ
  s : ℕ
  init : Fin s
  states : Fin s → StateCode (k + 2) s

namespace CodedMachine

/-- The symbol with alphabet index `j`: on a qubit tape `0 ↦ ⊢, 1 ↦ 0, 2 ↦ 1`; on a classical
tape `0 ↦ ⊢, 1 ↦ #, 2 ↦ 0, 3 ↦ 1, j+4 ↦ other j`. -/
def symOf (qb : Bool) (j : ℕ) : Sym :=
  if qb then (match j with | 0 => Sym.mark | 1 => Sym.b0 | _ => Sym.b1)
  else (match j with
    | 0 => Sym.mark | 1 => Sym.blank | 2 => Sym.b0 | 3 => Sym.b1 | j + 4 => Sym.other j)

/-- The alphabet index of a symbol (inverse of `symOf` on the alphabet). -/
def symIdx (qb : Bool) (a : Sym) : ℕ :=
  if qb then (match a with | Sym.b0 => 1 | Sym.b1 => 2 | _ => 0)
  else (match a with
    | Sym.mark => 0 | Sym.blank => 1 | Sym.b0 => 2 | Sym.b1 => 3 | Sym.other j => j + 4)

variable (A : CodedMachine)

/-- The alphabet size of a tape (`3` for a qubit tape). -/
def asz (t : Fin (A.k + 2)) : ℕ := if A.qubit t then 3 else A.asize t

/-- The lexicographic index of the scanned active tuple, first active tape most significant. -/
def rowIndex (act : List (Fin (A.k + 2))) (σ : Fin (A.k + 2) → Sym) : ℕ :=
  act.foldl (fun acc t => acc * A.asz t + symIdx (A.qubit t) (σ t)) 0

/-- The gate data of a state code (defaults for non-gate states). -/
def gateData (c : StateCode (A.k + 2) A.s) :
    (g : Gate) × (Fin g.arity → Fin (A.k + 2)) × Fin A.s × (Fin (A.k + 2) → Move) :=
  match c with
  | .gate g tp nx mv => ⟨g, tp, nx, mv⟩
  | _ => ⟨Gate.X, fun _ => 0, A.init, fun _ => Move.N⟩

/-- The active tapes of a state code. -/
def actOf : StateCode (A.k + 2) A.s → List (Fin (A.k + 2))
  | .classical act _ => act
  | _ => []

/-- The transition of a state code on a scanned tuple. -/
def δOf (p : Fin A.s) (σ : Fin (A.k + 2) → Sym) :
    Fin A.s × (Fin (A.k + 2) → Sym) × (Fin (A.k + 2) → Move) :=
  match A.states p with
  | .classical act rows =>
      let row := rows.getD (A.rowIndex act σ) (A.init, [], fun _ => Move.N)
      (row.1, fun t => symOf (A.qubit t) (row.2.1.getD (act.idxOf t) 0), row.2.2)
  | _ => (p, σ, fun _ => Move.N)

/-- The machine described by the code, before companions are fixed. -/
def preMachine : Machine where
  Q := Fin A.s
  T := Fin (A.k + 2)
  kind := fun t => if A.qubit t then TapeKind.qubit else TapeKind.classical
  alph := fun t => (Finset.range (A.asz t)).image (symOf (A.qubit t))
  inT := 0
  outT := 1
  companion := id
  init := A.init
  isFinal := fun p => match A.states p with | .final => true | _ => false
  isGate := fun p => match A.states p with | .gate .. => true | _ => false
  act := fun p => (A.actOf (A.states p)).toFinset
  δ := A.δOf
  gate := fun p => (A.gateData (A.states p)).1
  gtapes := fun p => (A.gateData (A.states p)).2.1
  gnext := fun p => (A.gateData (A.states p)).2.2.1
  gmove := fun p => (A.gateData (A.states p)).2.2.2

/-- The companion of a qubit tape (p.23): the least-indexed classical tape whose head makes the
same move as the head of the qubit tape in every transition row (the tape itself if there is
none, which `Valid` rules out). -/
def companionOf (t : Fin (A.k + 2)) : Fin (A.k + 2) :=
  if h : (Finset.univ.filter fun c : Fin (A.k + 2) => A.preMachine.IsCompanion c t).Nonempty then
    (Finset.univ.filter fun c : Fin (A.k + 2) => A.preMachine.IsCompanion c t).min' h
  else t

/-- The machine `A` denotes, with the least-index companions of p.23. -/
def toMachine : Machine := { A.preMachine with companion := A.companionOf }

/-- Well-formedness of the code: every qubit tape has the alphabet-size field `3`, active tapes are
listed in increasing order, and a classical table has exactly one row per scanned active tuple,
each row writing one symbol per active tape. -/
def WellFormed : Prop :=
  (∀ t, A.qubit t = true → A.asize t = 3) ∧
    ∀ p, match A.states p with
      | .classical act rows =>
          act.Pairwise (· < ·) ∧ rows.length = (act.map A.asz).prod ∧
            ∀ row ∈ rows, row.2.1.length = act.length
      | _ => True

/-- A **valid** code: well formed, and its machine satisfies Definition 3.1 with the least-index
companions (p.23–24: a code whose qubit tape has no companion is rejected). -/
def Valid : Prop := A.WellFormed ∧ A.toMachine.Valid

/-- A coded machine **without gate states**. -/
def GateFree : Prop := ∀ p, A.toMachine.isGate p = false

/-- The code of a move. -/
def moveCode : Move → ℕ
  | .L => 0
  | .N => 1
  | .R => 2

/-- The code of a gate. -/
def gateCode : Gate → ℕ
  | .H => 0
  | .X => 1
  | .CNOT => 2
  | .SWAP => 3
  | .Toff => 4

/-- The binary code of one state code: every number written as its self-delimiting code `m̄`. -/
def encState {n s : ℕ} : StateCode n s → List Bool
  | .final => sdNat 0
  | .classical act rows =>
      sdNat 1 ++ sdNat act.length ++ act.flatMap (fun t => sdNat t.val) ++ sdNat rows.length ++
        rows.flatMap fun r =>
          sdNat r.1.val ++ sdNat r.2.1.length ++ r.2.1.flatMap sdNat ++
            (List.finRange n).flatMap fun t => sdNat (moveCode (r.2.2 t))
  | .gate g tp nx mv =>
      sdNat 2 ++ sdNat (gateCode g) ++ (List.finRange g.arity).flatMap (fun i => sdNat (tp i).val) ++
        sdNat nx.val ++ (List.finRange n).flatMap fun t => sdNat (moveCode (mv t))

/-- The **encoding** `⌜A⌝` (p.23): in this fixed field order, the number of tapes, the number of
states, the kind and alphabet size of every tape, the initial state, and the code of every state
(its kind; its active tapes and transition table, or its gate, gate tapes, next state and moves),
every number written as its self-delimiting code `m̄`.

**Formalization Note** The paper fixes "a standard injective binary encoding" only by its
contents; this is one such encoding (every field is self-delimiting and the layout of each field
is determined by the fields before it). By Corollary 9.5 (p.119) any two admissible encodings
change `qKt` by at most `D·log(|x|+|y|+2) + D`. -/
def encode : List Bool :=
  sdNat A.k ++ sdNat A.s ++
    (List.finRange (A.k + 2)).flatMap (fun t => sdNat (A.qubit t).toNat ++ sdNat (A.asize t)) ++
    sdNat A.init.val ++ (List.finRange A.s).flatMap fun p => encState (A.states p)

end CodedMachine

end QuantumKtSoI


