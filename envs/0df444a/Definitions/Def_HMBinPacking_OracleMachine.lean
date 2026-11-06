-- Prove2me | Definitions.Def_HMBinPacking_OracleMachine
-- name    : HMBinPacking_OracleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:29.501364+00:00
-- url     : https://prove2.me/theorems/4518a106-d0b6-4e39-abc8-389f2b3891ac
-- title:
--   Oracle Turing machines with unit-cost calls and bounded query lengths
-- statement:
--   An **oracle machine** is a multi-stack Turing machine with Boolean input and output, a Boolean query stack, a label *ask* and a label *resume*. Run with an oracle $O$ (a function from words to words), it computes as follows: at a configuration whose label is *ask*, the contents $q$ of the query stack are replaced by $O(q)$ and the run continues at *resume*, with the internal state and all other stacks unchanged; at any other configuration it makes an ordinary machine step.
--
--   The machine **outputs $w$ within $t$ steps with queries of length at most $m$** if its run with oracle $O$ halts with output $w$ after at most $t$ steps, and the query stack holds at most $m$ bits at every oracle call of the run.
--
--   This is the model of the statements "using at most $T$ calls to strong separation and additional bit operations, with query lengths at most $m$" in Lemmas 5 and 6.
--
--   **Formalization Note** Built on Mathlib's `Turing.FinTM2`, with Mathlib's `initList`/`haltList` start and halt configurations. Every step, including each oracle call, costs one unit, which counts calls and bit operations together as the paper does. The program at the label *ask* is never executed. No published platform model charges for the computation between calls, which is why this layer is new.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, §3, p.5 (Lemmas 5 and 6: calls to an oracle, additional bit operations, query lengths)

import Mathlib

namespace HMBinPacking

/-- **An oracle Turing machine.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5, Lemmas 5 and 6: algorithms that use "calls to strong
separation [optimization] and additional bit operations, with query lengths …".

An oracle machine is a bundled multi-stack Turing machine `M` with Boolean input and output, a
Boolean query stack `qs`, and two labels: `ask` (call the oracle) and `resume` (where the run
continues after the call).

**Formalization Note.** No published platform model charges for the local computation between
oracle calls, so this is a minimal layer on Mathlib's `Turing.FinTM2`. `decEqΛ` only makes the test
"is the current label `ask`?" decidable. The program at `ask` is never executed. -/
structure OracleMachine where
  /-- the underlying machine -/
  M : Turing.TM2ComputableAux Bool Bool
  /-- the query (and answer) stack -/
  qs : M.tm.K
  /-- the query stack holds bits -/
  qsAlphabet : M.tm.Γ qs ≃ Bool
  /-- the label that calls the oracle -/
  ask : M.tm.Λ
  /-- the label the run continues at after a call -/
  resume : M.tm.Λ
  /-- decidable equality of labels -/
  decEqΛ : DecidableEq M.tm.Λ

/-- **Configurations of an oracle machine** (those of its underlying `FinTM2`).
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5.

**Formalization Note.** `Turing.TM2.Cfg`: the current label (`none` once halted), the internal
state, and the contents of every stack. -/
abbrev OCfg (OM : OracleMachine) : Type :=
  Turing.TM2.Cfg OM.M.tm.Γ OM.M.tm.Λ OM.M.tm.σ

/-- **One step of an oracle machine with oracle `O`.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5: "calls to strong separation and additional bit
operations".

At a configuration with label `ask`, the contents `q` of the query stack are replaced by the
oracle's answer `O q`, the label becomes `resume`, and the internal state and every other stack are
kept. At any other configuration the machine makes an ordinary step of `M`.

**Formalization Note.** An oracle is any function `O : List Bool → List Bool`. Each step, including
each oracle call, costs one unit; this is the paper's count of "calls … and additional bit
operations". -/
def oStep (OM : OracleMachine) (O : List Bool → List Bool) (c : OCfg OM) : Option (OCfg OM) :=
  letI := OM.decEqΛ
  if c.l = some OM.ask then
    some ⟨some OM.resume, c.var,
      Function.update c.stk OM.qs ((O ((c.stk OM.qs).map OM.qsAlphabet)).map OM.qsAlphabet.symm)⟩
  else
    OM.M.tm.step c

/-- **The configuration after `j` steps of an oracle machine on an input.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5.

**Formalization Note.** The run starts at Mathlib's `Turing.initList` of the input and iterates
`oStep`; `none` means the run halted earlier. -/
def oRun (OM : OracleMachine) (O : List Bool → List Bool) (input : List Bool) (j : ℕ) :
    Option (OCfg OM) :=
  (flip bind (oStep OM O))^[j] (some (Turing.initList OM.M.tm (input.map OM.M.inputAlphabet.symm)))

/-- **An oracle machine outputs a word within `t` steps, with queries of length at most `q`.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5, Lemmas 5 and 6: "using at most … calls to strong
separation and additional bit operations, with query lengths at most …".

`ORunsWithin OM O input output t q` holds when the run of `OM` with oracle `O` on `input` reaches the
halting configuration with `output` after at most `t` steps, and at every oracle call made before
that the query stack holds at most `q` bits.

**Formalization Note.** The halting configuration is Mathlib's `Turing.haltList` (no label, initial
state, `output` on the output stack, every other stack empty), as in `Turing.TM2OutputsInTime`. -/
def ORunsWithin (OM : OracleMachine) (O : List Bool → List Bool) (input output : List Bool)
    (t q : ℕ) : Prop :=
  ∃ steps ≤ t,
    oRun OM O input steps = some (Turing.haltList OM.M.tm (output.map OM.M.outputAlphabet.symm)) ∧
      ∀ j < steps, ∀ c : OCfg OM, oRun OM O input j = some c → c.l = some OM.ask →
        (c.stk OM.qs).length ≤ q

end HMBinPacking


