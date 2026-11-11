-- Prove2me | Definitions.Def_QuantumAdviceAmplification_Separation_machine
-- name    : QuantumAdviceAmplification_Separation_machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:01:18.536201+00:00
-- url     : https://prove2.me/theorems/49478399-dd18-48f9-bb04-ec1d026ca1e9
-- title:
--   Operational deterministic machines with random access to advice
-- statement:
--   A finite transition table controls a read-only input tape, a read-only advice tape, finitely many ordinary work tapes, and a designated index work tape. The work alphabet is finite and contains blank and both bits. Heads move one cell per transition; a jump reads the binary index actually stored on the index tape and places the advice head at that cell, or the first blank if the index exceeds the advice length. Work tapes start blank.
--   $$\operatorname{run}(M,x,a,t+1)=\operatorname{step}(M,x,a,\operatorname{run}(M,x,a,t)).$$
--   Halting and output predicates refer to this trace, and time counts transitions. There is no arithmetic primitive or assigned time function. A separate printing predicate reads a bit string on an ordinary work tape when the machine halts. It supplies finite-program circuit generation. Indices on tapes are stored one based; internal list offsets are zero based. One-sided tapes stay at their left endpoint under a left move.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.6, Definition 2.5

import Definitions.Def_QuantumAdviceAmplification_Separation_entropy
set_option autoImplicit false

namespace QuantumAdviceAmplification.Separation

/-- One ordinary head move. Left at the left end stays there. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq

def moveHead (h : ℕ) : Move → ℕ
  | .left => h - 1
  | .stay => h
  | .right => h + 1

inductive AdviceMove where
  | move (dir : Move)
  | jump

/-- Finite control; all work symbols and states range over finite types.
Work tape 0 is the index tape and work tape 1 is used for string output.
Symbols 0,1,2 denote blank, bit 0, bit 1. There are no arithmetic instructions. -/
structure Machine where
  states : ℕ
  start : Fin states
  extraSymbols : ℕ
  extraTapes : ℕ
  transition : Fin states → Option Bool → Option Bool →
    (Fin (extraTapes + 2) → Fin (extraSymbols + 3)) →
    (Bool ⊕ (Fin states × Move × AdviceMove ×
      (Fin (extraTapes + 2) → Fin (extraSymbols + 3) × Move)))

structure Configuration (M : Machine) where
  control : Fin M.states
  inputHead : ℕ
  adviceHead : ℕ
  heads : Fin (M.extraTapes + 2) → ℕ
  tapes : Fin (M.extraTapes + 2) → List (Fin (M.extraSymbols + 3))
  answer : Option Bool

def initial (M : Machine) : Configuration M :=
  ⟨M.start, 0, 0, fun _ => 0, fun _ => [], none⟩

def tapeWrite {s : ℕ} (l : List (Fin (s + 3))) (p : ℕ) (v : Fin (s + 3)) :
    List (Fin (s + 3)) :=
  (l ++ List.replicate (p + 1 - l.length) 0).set p v

def tapeBits {s : ℕ} (l : List (Fin (s + 3))) : List Bool :=
  (l.takeWhile fun c => c.val == 1 || c.val == 2).map fun c => c.val == 2

/-- A jump reads the binary integer actually written on the index tape.
Indices are one based; invalid zero is assigned the first cell. -/
def step (M : Machine) (x a : List Bool) (c : Configuration M) : Configuration M :=
  match c.answer with
  | some _ => c
  | none =>
    match M.transition c.control x[c.inputHead]? a[c.adviceHead]?
      (fun i => (c.tapes i).getD (c.heads i) 0) with
    | .inl b => { c with answer := some b }
    | .inr (q, im, am, writes) =>
      { control := q
        inputHead := moveHead c.inputHead im
        adviceHead := match am with
          | .move dir => moveHead c.adviceHead dir
          | .jump => min a.length (value (tapeBits (c.tapes 0)) - 1)
        heads := fun i => moveHead (c.heads i) (writes i).2
        tapes := fun i => tapeWrite (c.tapes i) (c.heads i) (writes i).1
        answer := none }

def run (M : Machine) (x a : List Bool) : ℕ → Configuration M
  | 0 => initial M
  | t + 1 => step M x a (run M x a t)

def Outputs (M : Machine) (x a : List Bool) (b : Bool) : Prop :=
  ∃ t : ℕ, (run M x a t).answer = some b

def ComputesWithin (M : Machine) (x a : List Bool) (b : Bool) (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run M x a t).answer = some b

/-- Sequential finite-program string generation: the extra advice tape is empty.
Its jump instruction therefore has no effect and supplies no oracle. The string is
read from the ordinary output work tape when the machine halts. -/
def PrintsWithin (M : Machine) (x out : List Bool) (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run M x [] t).answer.isSome ∧
    tapeBits ((run M x [] t).tapes 1) = out

end QuantumAdviceAmplification.Separation


