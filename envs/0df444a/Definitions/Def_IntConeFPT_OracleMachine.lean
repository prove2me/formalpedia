-- Prove2me | Definitions.Def_IntConeFPT_OracleMachine
-- name    : IntConeFPT_OracleMachine
-- status  : Definition
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:50:45.588716+00:00
-- url     : https://prove2.me/theorems/79f48cc8-6f27-4880-a5bf-49324f18cadf
-- title:
--   Oracle Turing machines over $\{0,1,2,3\}$ with unit-cost calls and constrained queries
-- statement:
--   An **oracle machine** is a multi-stack Turing machine (Mathlib's `Turing.TM2ComputableAux`) whose input and output alphabet is $\{0,1,2,3\}$. It has a distinguished query stack over the same alphabet and two distinguished labels, *ask* and *resume*. Given an oracle $O:\{0,1,2,3\}^*\to\{0,1,2,3\}^*$, a step at the label *ask* replaces the word $q$ on the query stack by the answer $O(q)$ and continues at *resume*. The internal state and all other stacks are unchanged. Every other step is an ordinary step of the machine.
--
--   $\mathrm{ORunsWithin}(OM,O,G,x,y,t)$ says that, started on input $x$, the machine halts with output $y$ after at most $t$ steps, where each oracle call counts as one step, and that every query $q$ it asks along the way satisfies the predicate $G(q)$. Bounds on the query length, and restrictions on the form of the queries, are expressed through $G$.
--
--   This is the oracle-algorithm model of Grötschel–Lovász–Schrijver (each call costs one step). It is used for the ellipsoid method with a separation oracle in the proof of Lemma 5 of Jansen–Ohnesorge–Schumacher. It adapts the published `HMBinPacking_OracleMachine` (Boolean alphabet) to the alphabet of the mission's `Machine`.
-- source:
--   Grötschel–Lovász–Schrijver, Geometric Algorithms and Combinatorial Optimization (1988), §1.2 (oracle algorithms); Jansen–Ohnesorge–Schumacher, arXiv:2609.31328 (preprint), proof of Lemma 5, p.35; adapted from the platform definition HMBinPacking_OracleMachine

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym

namespace IntConeFPT

open OnlineCRS.Combine

/-- **An oracle Turing machine over the alphabet `Sym = Fin 4`.**
Grötschel–Lovász–Schrijver, *Geometric Algorithms and Combinatorial Optimization* (1988), §1.2:
oracle algorithms, in which each oracle call counts as one step; used in Jansen–Ohnesorge–
Schumacher, arXiv:2609.31328 (preprint), proof of Lemma 5, p.35 ("uses polynomially many separation
queries of polynomial encoding length").

An oracle machine is a bundled multi-stack Turing machine `M` with input and output over `Sym`, a
query (and answer) stack `qs` over `Sym`, and two labels: `ask` (call the oracle) and `resume`
(where the run continues after the call).

**Formalization Note.** Adapted from the published `HMBinPacking_OracleMachine` (Boolean alphabet)
to the alphabet `Sym` of the mission's `Machine`. `decEqΛ` only makes the test "is the current label
`ask`?" decidable. The program at `ask` is never executed. -/
structure OracleMachine where
  /-- the underlying machine -/
  M : Turing.TM2ComputableAux Sym Sym
  /-- the query (and answer) stack -/
  qs : M.tm.K
  /-- the query stack holds symbols of `Sym` -/
  qsAlphabet : M.tm.Γ qs ≃ Sym
  /-- the label that calls the oracle -/
  ask : M.tm.Λ
  /-- the label the run continues at after a call -/
  resume : M.tm.Λ
  /-- decidable equality of labels -/
  decEqΛ : DecidableEq M.tm.Λ

/-- Configurations of an oracle machine (those of its underlying `FinTM2`). -/
abbrev OCfg (OM : OracleMachine) : Type :=
  Turing.TM2.Cfg OM.M.tm.Γ OM.M.tm.Λ OM.M.tm.σ

/-- **One step of an oracle machine with oracle `O`.** At a configuration with label `ask`, the
contents `q` of the query stack are replaced by the answer `O q`, the label becomes `resume`, and
the internal state and every other stack are kept. Otherwise the machine makes an ordinary step. -/
def oStep (OM : OracleMachine) (O : List Sym → List Sym) (c : OCfg OM) : Option (OCfg OM) :=
  letI := OM.decEqΛ
  if c.l = some OM.ask then
    some ⟨some OM.resume, c.var,
      Function.update c.stk OM.qs ((O ((c.stk OM.qs).map OM.qsAlphabet)).map OM.qsAlphabet.symm)⟩
  else
    OM.M.tm.step c

/-- The configuration after `j` steps of an oracle machine on an input (`none`: halted earlier). -/
def oRun (OM : OracleMachine) (O : List Sym → List Sym) (input : List Sym) (j : ℕ) :
    Option (OCfg OM) :=
  (flip bind (oStep OM O))^[j]
    (some (Turing.initList OM.M.tm (input.map OM.M.inputAlphabet.symm)))

/-- **`OM` with oracle `O` outputs `output` on `input` within `t` steps, asking only queries
satisfying `G`.** The run reaches the halting configuration with `output` (Mathlib's
`Turing.haltList`, as in `Turing.TM2OutputsInTime`) after at most `t` steps, each oracle call
counting as one step, and at every oracle call before that the query stack holds a word `q` with
`G q`. Bounds on query lengths are expressed through `G`. -/
def ORunsWithin (OM : OracleMachine) (O : List Sym → List Sym) (G : List Sym → Prop)
    (input output : List Sym) (t : ℕ) : Prop :=
  ∃ steps ≤ t,
    oRun OM O input steps = some (Turing.haltList OM.M.tm (output.map OM.M.outputAlphabet.symm)) ∧
      ∀ j < steps, ∀ c : OCfg OM, oRun OM O input j = some c → c.l = some OM.ask →
        G ((c.stk OM.qs).map OM.qsAlphabet)

end IntConeFPT


