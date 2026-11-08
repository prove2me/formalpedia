-- Prove2me | Definitions.Def_EntangledPIR_ServerImpl
-- name    : EntangledPIR_ServerImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:36.643494+00:00
-- url     : https://prove2.me/theorems/d3ccb488-a105-46e3-90a2-929170a49c50
-- title:
--   An implementation of the honest servers by elementary operations
-- statement:
--   An implementation for parameters $n,m,\lambda$ consists of a list of classical bit operations that computes all values of all tables from the truth table of $F$, and for each round a list of elementary operations of honest A and of honest B, on the qubits of the Bell pairs and ancillas. It is correct if the first list computes the tables for every $F$, and in each round, for every $F$, classical history and current message, the list implements the prescribed instrument: with ancillas initially zero, summing over the measurement outcomes with a given outgoing message gives the image under that outcome of the instrument, with ancillas returned to zero.
--
--   The count of operations is the length of the first list plus the lengths of the lists of the rounds.
--
--   **Formalization Note** The lists do not depend on the database, which is read-only classical control. Memory holds the tables, the messages of the history, the current message, and the outgoing message in a fixed slot, so the classical handling of messages is counted too.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 5.4(iii), p.27; proof pp.57–58; A.1, p.53

import Definitions.Def_EntangledPIR_ElemOp
import Definitions.Def_EntangledPIR_honest

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Lemma 5.4(iii),
p.27, and its proof, pp.57–58: an implementation of the honest servers by elementary operations.
-/

open Matrix

namespace EntangledPIR

/-- The cells of the classical memory of an honest server: the truth table of `F`, the tables `F_i`, the
messages of the rounds, and work bits. Slot `2s` holds the message received in round `s`, slot `2s + 1`
the message sent in round `s`; a message is stored as data bits with valid bits. -/
inductive Cell (n m lam : ℕ)
  | truth (b : Bits n) (c : Fin m)
  | tableBit (i : Fin (shareCount n lam)) (y : Bits (queryLen n lam)) (c : Fin m)
  | msgBit (slot pos : ℕ)
  | msgValid (slot pos : ℕ)
  | work (a : ℕ)

noncomputable instance (n m lam : ℕ) : DecidableEq (Cell n m lam) := Classical.decEq _

/-- The memory that holds the truth table of `F`, and is otherwise zero. -/
def truthMem {n m : ℕ} (lam : ℕ) (F : Bits n → Bits m) : Cell n m lam → Bool
  | .truth b c => F b c
  | _ => false

/-- The content of a message slot, for history `h` and current message `cur`. -/
def slotContent (h : ServerHistory) (cur : List Bool) (slot : ℕ) : List Bool :=
  if slot = 2 * h.length then cur
  else if slot % 2 = 0 then (h.getD (slot / 2) ([], [])).1
  else (h.getD (slot / 2) ([], [])).2

/-- The memory `mem` with the messages of history `h` and the current message `cur` written in. -/
def withMessages {n m lam : ℕ} (mem : Cell n m lam → Bool) (h : ServerHistory) (cur : List Bool) :
    Cell n m lam → Bool
  | .msgBit slot pos => (slotContent h cur slot).getD pos false
  | .msgValid slot pos => decide (pos < (slotContent h cur slot).length)
  | c => mem c

/-- The message that the memory holds in `slot`. -/
def readSlot {n m lam : ℕ} (L : ℕ) (mem : Cell n m lam → Bool) (slot : ℕ) : List Bool :=
  ((List.range L).takeWhile fun p => mem (.msgValid slot p)).map fun p => mem (.msgBit slot p)

/-- The qubits of an honest server: its halves of the Bell pairs and `a` ancilla qubits. **Formalization
Note.** A and B use one label type, as the paper identifies `P` with `P′` and `Y_z` with `Y′_z`, p.21. -/
abbrev ServerQubit (n m lam a : ℕ) : Type := BellIdx n m lam ⊕ Fin a

noncomputable instance (n m lam a : ℕ) : DecidableEq (ServerQubit n m lam a) := Classical.decEq _

/-- The isometry from the registers of an honest server to its qubits, with all ancillas zero. -/
noncomputable def ancillaEmbed (n m lam a : ℕ) :
    Matrix (ServerQubit n m lam a → Bool) (Copies n m lam × Unit) ℂ :=
  Matrix.of fun u s =>
    if u = Sum.elim (fun p => qubitsOf (s.1 p.1) p.2) (fun _ => false) then 1 else 0

/-- The list of operations `prog`, started from the memory `mem₀`, implements the instrument `I`: for
every operator `ρ` and message `o`, with ancillas starting in zero, summing over the measurement outcomes
of `prog` for which the slot `outSlot` holds `o` gives the image of `ρ` under outcome `o` of `I`, with the
ancillas returned to zero. -/
def ImplementsInstr {n m lam a L : ℕ} (prog : List (ElemOp (ServerQubit n m lam a) (Cell n m lam)))
    (mem₀ : Cell n m lam → Bool) (outSlot : ℕ)
    (I : Instrument (Copies n m lam × Unit) (Copies n m lam × Unit) (BitStr L)) : Prop :=
  ∀ (o : BitStr L) (ρ : Matrix (Copies n m lam × Unit) (Copies n m lam × Unit) ℂ),
    (∑ ω : Fin prog.length → Bool,
      if BitStr.ofList L (readSlot L (runProg prog (List.ofFn ω) mem₀).2 outSlot) = o then
        (runProg prog (List.ofFn ω) mem₀).1 * ancillaEmbed n m lam a * ρ *
          (ancillaEmbed n m lam a)ᴴ * ((runProg prog (List.ofFn ω) mem₀).1)ᴴ
      else 0) =
      ancillaEmbed n m lam a * (∑ c, I.K o c * ρ * (I.K o c)ᴴ) * (ancillaEmbed n m lam a)ᴴ

/-- **An implementation of the honest servers by elementary operations**, Lemma 5.4(iii), for fixed `n`,
`m`, `λ`, and independent of the database.

* `tableProg`, classical bit operations that compute all values of all tables `F_i` from the truth table
  of `F`, "before the protocol", p.57;
* `progA r`, `progB r`, the operations of the honest servers in round `r`. They read the tables, the classical
  history and the current message from the memory, write the outgoing message to the memory, and may use
  any memory cell as classical control.

**Formalization Note.** The database is read-only classical control (A.1, p.53), so the programs do not
depend on `F`, only the memory does. If they could, the table computation would be empty. -/
structure ServerImpl (n m lam : ℕ) where
  /-- the number of ancilla qubits -/
  anc : ℕ
  /-- the table computation -/
  tableProg : List (BitOp (Cell n m lam))
  /-- the operations of A per round -/
  progA : ℕ → List (ElemOp (ServerQubit n m lam anc) (Cell n m lam))
  /-- the operations of B per round -/
  progB : ℕ → List (ElemOp (ServerQubit n m lam anc) (Cell n m lam))

/-- The total number of elementary operations of the honest A in the implementation, Lemma 5.4(iii). -/
def ServerImpl.opsA {n m lam : ℕ} (P : ServerImpl n m lam) : ℕ :=
  P.tableProg.length + ∑ r ∈ Finset.range numRounds, (P.progA r).length

/-- The total number of elementary operations of the honest B in the implementation, Lemma 5.4(iii). -/
def ServerImpl.opsB {n m lam : ℕ} (P : ServerImpl n m lam) : ℕ :=
  P.tableProg.length + ∑ r ∈ Finset.range numRounds, (P.progB r).length

/-- An implementation is correct: `tableProg` computes the tables of every database, and in every round of
the schedule, for every database, classical history and current message, the operations implement the
prescribed instrument. -/
def ServerImpl.Correct {n m lam : ℕ} (P : ServerImpl n m lam) : Prop :=
  (∀ (F : Bits n → Bits m) i y c,
    runBits P.tableProg (truthMem lam F) (.tableBit i y c) = table lam F i y c) ∧
  ∀ (F : Bits n → Bits m) (r : ℕ) (h : ServerHistory) (cur : List Bool),
    r < numRounds → h.length = r →
    (∀ p ∈ h, p.1.length ≤ msgBound n m lam ∧ p.2.length ≤ msgBound n m lam) →
    cur.length ≤ msgBound n m lam →
    ImplementsInstr (P.progA r) (withMessages (runBits P.tableProg (truthMem lam F)) h cur)
        (2 * r + 1) (honestAInstr lam F Unit r cur) ∧
      ImplementsInstr (P.progB r) (withMessages (runBits P.tableProg (truthMem lam F)) h cur)
        (2 * r + 1) (honestBInstr lam F Unit r h cur)

end EntangledPIR


