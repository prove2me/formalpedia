-- Prove2me | Definitions.Def_NKtLB_Supplement_runV
-- name    : NKtLB_Supplement_runV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:50.005023+00:00
-- url     : https://prove2.me/theorems/63c88554-7097-4f9a-9832-13367191a16e
-- title:
--   Runs with a time-dependent oracle, and the queries made in a time window
-- statement:
--   An auxiliary notion for oracle access with bounded adaptivity. For a machine $M$, read-only tape contents and a sequence of oracles $(O_i)_{i\in\mathbb N}$, $\mathrm{runV}$ is the run of $M$ in which the oracle query made at step $i$ is answered according to $O_i$. When every $O_i$ equals one oracle $O$, this is the ordinary run of $M$ with oracle $O$. $\mathrm{queriesIn}(a,b)$ is the list of query strings that the run makes at steps $a,\dots,b-1$, in order.
--
--   These notions are used only to define **levels of adaptivity**: the queries of a round may not depend on the answers to that round.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.3, p.22 and Appendix A, p.96 (auxiliary)

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **A run with a time-dependent oracle** (auxiliary to "non-adaptive access" and "`d` levels of
adaptivity", Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), p.22, p.96): the configuration of `M` after `j` steps when the oracle query
made at step `i` is answered by the oracle `Os i`. With a constant `Os` this is the base
`Machine.run`.

**Formalization Note.** Used only to state that the queries of a phase do not depend on the
answers given in that phase (`AdaptRounds`). -/
noncomputable def runV (M : Machine) (Os : ℕ → Set (List Bool)) (inp : Inputs) :
    ℕ → Machine.Cfg M
  | 0 => M.init
  | j + 1 => M.step (Os j) inp (runV M Os inp j)

/-- The list of oracle queries made at steps `a, a + 1, …, b - 1` of `runV M Os inp`: the query
string at each step at which the machine is in its query state (and not halted), in order. -/
noncomputable def queriesIn (M : Machine) (Os : ℕ → Set (List Bool)) (inp : Inputs) (a b : ℕ) :
    List (List Bool) :=
  ((List.range' a (b - a)).filter (fun j =>
      decide ((runV M Os inp j).state = M.query ∧ (runV M Os inp j).state ≠ M.halt))).map
    (fun j => (runV M Os inp j).queryString)

end NKtLB.Supplement


