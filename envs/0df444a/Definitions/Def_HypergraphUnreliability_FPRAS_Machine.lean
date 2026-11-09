-- Prove2me | Definitions.Def_HypergraphUnreliability_FPRAS_Machine
-- name    : HypergraphUnreliability_FPRAS_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:49.756432+00:00
-- url     : https://prove2.me/theorems/54a8d62d-15bd-47be-9df6-2dd0bcdbab59
-- title:
--   Written rationals, binary codes, polynomial-time bit machines and fair-bit machines
-- statement:
--   This definition fixes the computational model of the mission. A rational is **written** as a binary numerator and a positive binary denominator, not necessarily reduced. Numbers have self-delimiting binary codes, and lists have explicit length prefixes.
--
--   A **deterministic bit machine** is a Mathlib `Turing.FinTM2` with bit input and output and all stack alphabets finite. A function is **polynomial-time computable** on a domain, for a size function $s$, if one machine and one polynomial $P$, chosen before all inputs, satisfy: on each input $x$ of the domain the machine outputs the code of the value within $P(s(x))$ steps.
--
--   A **fair-bit machine** has one more stack, holding the unread random tape with the next bit on top. On an input and a tape it **runs within** $B$ if it halts within $B$ steps and its unread tape never falls more than $B$ bits below the initial tape length. The probability of an event under $T$ fair bits is the fraction of the $2^T$ tapes on which it holds.
--
--   These definitions are the interface of every polynomial-time claim of the paper. They replace unit-cost real arithmetic by actual bit operations.
--
--   **Formalization Note** The theorems quantify over every tape longer than the machine's bound, so a machine reading at most $B$ bits never observes where the tape ends, and the tape length cannot carry advice. A step of a `FinTM2` may pop a bounded number of symbols, so the bits read and the recorded height differ by a program constant at most.
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), §1.1, p. 2; §7, p. 8; §7.3, p. 10

import Mathlib

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS

/-- A rational number written as a binary numerator and a positive binary denominator. The fraction
need not be reduced (§7, p. 8), and its encoding length is the length of what was written. -/
structure Frac where
  num : ℕ
  den : ℕ

/-- The value of a written fraction. -/
def Frac.val (a : Frac) : ℚ := (a.num : ℚ) / (a.den : ℚ)

/-- Self-delimiting binary code of a natural number: the bit length in unary, a separator, then the
binary digits (`Nat.bits`, least significant first, with no leading zeros). Its length is
`2 · bitlength + 1`, so the code length is the usual binary length up to a constant factor. -/
def natCode (x : ℕ) : List Bool :=
  List.replicate (Nat.bits x).length true ++ [false] ++ Nat.bits x

/-- Code of a list: its length, then its elements. -/
def listCode {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  natCode l.length ++ l.flatMap f

/-- Code of a written fraction: numerator, then denominator. -/
def fracCode (a : Frac) : List Bool := natCode a.num ++ natCode a.den

/-- A deterministic bit machine: Mathlib's `Turing.FinTM2` (finitely many stacks, states and labels),
with bit input and output alphabets and with all stack alphabets finite (`FinTM2` itself only requires
the input alphabet to be finite). -/
structure BitMachine where
  code : Turing.TM2ComputableAux Bool Bool
  finiteAlphabet : ∀ k : code.tm.K, Finite (code.tm.Γ k)

/-- `output` is computed on the domain `dom` by one fixed machine, within a bound given by one fixed
polynomial in `size x`, chosen before all inputs. Steps of a `FinTM2` execute a bounded program
fragment on a finite alphabet, so step counts are bit operations up to a constant factor. -/
def PolyComputesIn {α : Type} (dom : α → Prop) (input output : α → List Bool) (size : α → ℕ) : Prop :=
  ∃ M : BitMachine, ∃ P : Polynomial ℕ, ∀ x, dom x →
    Nonempty (Turing.TM2OutputsInTime M.code.tm
      ((input x).map M.code.inputAlphabet.symm)
      (some ((output x).map M.code.outputAlphabet.symm))
      (P.eval (size x)))

/-- A fair-bit machine: a bit machine with one further stack holding the unread random tape, whose
top is the next tape bit. The tape stack is distinct from the input and output stacks. -/
structure CoinMachine where
  tm : Turing.FinTM2
  finiteAlphabet : ∀ k : tm.K, Finite (tm.Γ k)
  inputAlphabet : tm.Γ tm.k₀ ≃ Bool
  outputAlphabet : tm.Γ tm.k₁ ≃ Bool
  kCoin : tm.K
  coin_ne_input : kCoin ≠ tm.k₀
  coin_ne_output : kCoin ≠ tm.k₁
  coinAlphabet : tm.Γ kCoin ≃ Bool

namespace CoinMachine

/-- The initial configuration on an input and a random tape, the first tape bit on top. -/
def initCfg (M : CoinMachine) (input tape : List Bool) : M.tm.Cfg where
  l := some M.tm.main
  var := M.tm.initialState
  stk k :=
    if h₀ : k = M.tm.k₀ then h₀ ▸ input.map M.inputAlphabet.symm
    else if hc : k = M.kCoin then hc ▸ tape.map M.coinAlphabet.symm
    else []

/-- The configuration after `s` steps, if the machine has not halted before then. -/
def cfgAt (M : CoinMachine) (input tape : List Bool) (s : ℕ) : Option M.tm.Cfg :=
  (fun o => o.bind M.tm.step)^[s] (some (M.initCfg input tape))

/-- On this input and random tape the machine halts within `B` steps, with `out` on its output stack,
and its unread tape never falls more than `B` bits below the initial tape length (it has used at most
`B` random bits, up to the bounded lookahead of a single step). -/
def RunsWithin (M : CoinMachine) (input tape : List Bool) (B : ℕ) (out : List Bool) : Prop :=
  ∃ (s : ℕ) (c : M.tm.Cfg), s ≤ B ∧ M.cfgAt input tape s = some c ∧ c.l = none ∧
    (c.stk M.tm.k₁).map M.outputAlphabet = out ∧
    ∀ s' ≤ s, ∀ c', M.cfgAt input tape s' = some c' →
      tape.length ≤ (c'.stk M.kCoin).length + B

end CoinMachine

/-- The tape of length `T` given by a bit vector. -/
def tapeList {T : ℕ} (ω : Fin T → Bool) : List Bool := List.ofFn ω

/-- The probability of an event under `T` independent fair bits. -/
def fairProb (T : ℕ) (A : (Fin T → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter A).card : ℝ) / 2 ^ T

/-- The expectation of a function of `T` independent fair bits. -/
def fairExpect (T : ℕ) (f : (Fin T → Bool) → ℝ) : ℝ :=
  (∑ ω, f ω) / 2 ^ T

/-- Read a tape of length `T` as a bit stream; a position beyond the tape reads `false`, and no such
position is used by an algorithm whose bit budget is at most `T`. -/
def tapeBit {T : ℕ} (ω : Fin T → Bool) (i : ℕ) : Bool :=
  if h : i < T then ω ⟨i, h⟩ else false

end HypergraphUnreliability.FPRAS


