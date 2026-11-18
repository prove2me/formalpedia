-- Prove2me | Definitions.Def_KoanaKPaths_BitStackAdapter
-- name    : KoanaKPaths_BitStackAdapter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T00:52:40.02597+00:00
-- url     : https://prove2.me/theorems/0e0ffdbb-adaa-421f-b605-0cb66fb35453
-- title:
--   Fair-bit FinTM2 implementation of finite stack programs
-- statement:
--   A concrete implementation of the finite stack-program language used for charged binary arithmetic in a fair-bit machine.
--
--   For a program with $S$ work stacks and addresses in $\{0,\ldots,L\}$, the construction supplies a Mathlib multi-stack Turing machine with finite alphabets, finite registers and finite labels. Input and output stacks use bits; work stacks use a fixed alphabet of sixteen symbols; return addresses use a finite alphabet. The random tape occupies a separate Boolean stack. The program sees the deterministic input, one separator, and then the random tape in order. A final reversal writes the output in its specified order.
--
--   This is implementation data for transferring charged stack-program executions to the fair-bit computation model used by the counting mission. The definition includes a configuration representation relation, but contains no assumption of correctness or running time; those are separate proof obligations.
-- source:
--   Supporting machine refinement for Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 9 / PDF p. 10, Section 3.2 running-time argument. Operational source: platform Definitions.Def_IntMul_SS_Defs1, NLogN.Instr/fstep/Steps (charged finite-alphabet stack programs), and Mathlib 0df444a, Mathlib/Computability/TuringMachine/Computable.lean (FinTM2), StackTuringMachine.lean (TM2.stepAux). https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/StackTuringMachine.lean

import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine

namespace KoanaKPaths.Machine
open Turing HypergraphUnreliability.FPRAS

/-- Work stacks use the finite 16-symbol alphabet of the charged item-language compiler.
The input, random tape, output and output-reversal buffer have Boolean alphabets. -/
inductive Stack (S : ℕ) where
  | input | coin | output | buffer | control | work (i : Fin S)
  deriving DecidableEq, Fintype

def Alphabet (S L : ℕ) : Stack S → Type
  | .input | .coin | .output | .buffer => Bool
  | .control => Fin (L+1)
  | .work _ => NLogN.Sym

/-- All registers hold one symbol, one return address, or a finite phase flag. -/
structure Registers (L : ℕ) where
  phase : Bool
  bit : Option Bool
  sym : Option NLogN.Sym
  ret : Option (Fin (L+1))
  deriving Fintype

abbrev Label (L : ℕ) := Fin (L+1) ⊕ Unit

def address (L e : ℕ) : Fin (L+1) := ⟨e % (L+1), Nat.mod_lt _ (by omega)⟩
def next (L e : ℕ) : Label L := .inl (address L e)
def finish (L : ℕ) : Label L := .inr ()

/-- One flat instruction is one TM2 step. The finite fragment may read one input bit or
one random bit, and all arithmetic at this layer is on fixed finite types. -/
def instruction {S L : ℕ} : NLogN.Instr S → TM2.Stmt (Alphabet S L) (Label L) (Registers L)
  | .jmp e => .goto (fun _ => next L e)
  | .push i a e => .push (.work i) (fun _ => a) (.goto (fun _ => next L e))
  | .pop i e => .pop (.work i) (fun v _ => v) (.goto (fun _ => next L e))
  | .inRd i e => .branch (fun v => v.phase)
      (.pop .input (fun v b => {v with phase := b.isSome, sym := some ((b.map NLogN.codeBit).getD NLogN.codeSep)})
        (.push (.work i) (fun v => v.sym.getD NLogN.codeEnd) (.goto (fun _ => next L e))))
      (.pop .coin (fun v b => {v with sym := some ((b.map NLogN.codeBit).getD NLogN.codeEnd)})
        (.push (.work i) (fun v => v.sym.getD NLogN.codeEnd) (.goto (fun _ => next L e))))
  | .out b e => .push .buffer (fun _ => b) (.goto (fun _ => next L e))
  | .br i f y n => .peek (.work i) (fun v a => {v with sym := a})
      (.branch (fun v => f v.sym) (.goto (fun _ => next L y)) (.goto (fun _ => next L n)))
  | .call t e => .push .control (fun _ => address L e) (.goto (fun _ => next L t))
  | .ret => .pop .control (fun v a => {v with ret := a})
      (.branch (fun v => v.ret.isSome)
        (.goto (fun v => .inl (v.ret.getD 0))) (.goto (fun _ => finish L)))

/-- Restore the forward output order after the flat program returns. -/
def reverseOutput {S L : ℕ} : TM2.Stmt (Alphabet S L) (Label L) (Registers L) :=
  .pop .buffer (fun v b => {v with bit := b})
    (.branch (fun v => v.bit.isSome)
      (.push .output (fun v => v.bit.getD false) (.goto (fun _ => finish L))) .halt)

def flatMachine {S : ℕ} (L entry : ℕ) (code : ℕ → NLogN.Instr S) : CoinMachine where
  tm :=
    { K := Stack S
      k₀ := .input
      k₁ := .output
      Γ := Alphabet S L
      Λ := Label L
      main := next L entry
      σ := Registers L
      initialState := ⟨true,none,none,none⟩
      Γk₀Fin := inferInstanceAs (Fintype Bool)
      m := fun l => match l with
        | .inl p => instruction (code p.val)
        | .inr _ => reverseOutput }
  finiteAlphabet := by intro k; cases k <;> dsimp [Alphabet] <;> infer_instance
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  kCoin := .coin
  coin_ne_input := by simp
  coin_ne_output := by simp
  coinAlphabet := Equiv.refl Bool

/-- The deterministic input and the random tape form two sequential logical streams,
separated by the item language's fixed separator symbol. -/
def logicalInput (input tape : List Bool) : List NLogN.Sym :=
  input.map NLogN.codeBit ++ NLogN.codeSep :: tape.map NLogN.codeBit

/-- Representation invariant during the flat-program phase. The register contents other
than the input-stream phase flag are temporary and unconstrained. -/
structure Represents {S L entry : ℕ} {code : ℕ → NLogN.Instr S}
    (input tape : List Bool) (c : NLogN.Cfg S) (v : (flatMachine L entry code).tm.Cfg) : Prop where
  pc_lt : c.pc < L+1
  returns_lt : ∀ e ∈ c.ctl, e < L+1
  label : v.l = some (next L c.pc)
  phase : v.var.phase = decide (c.σ.ip ≤ input.length)
  input_stack : v.stk .input = input.drop c.σ.ip
  coin_stack : v.stk .coin = tape.drop (c.σ.ip-input.length-1)
  output_stack : v.stk .output = []
  buffer_stack : v.stk .buffer = c.σ.out.reverse
  control_stack : v.stk .control = c.ctl.map (address L)
  work_stack : ∀ i, v.stk (.work i) = c.σ.stk i

end KoanaKPaths.Machine


