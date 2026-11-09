-- Prove2me | Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel
-- name    : GraphIsoTesting_FixedGraph_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:24:07.213621+00:00
-- url     : https://prove2.me/theorems/0c6e1675-55e5-41d9-b268-5b82539cb13b
-- title:
--   Adaptive randomized oracle algorithms and transcripts
-- statement:
--   Let $Q$ and $R$ be query and answer alphabets, and let $q$ be a natural query cap. A deterministic strategy is a response tree that either halts with a Boolean output or asks one query and continues with the subtree selected by its answer. Execution returns the ordered list of actual query/answer pairs and the final Boolean decision. A randomized strategy is an arbitrary probability mass function on these trees, sampled independently of the unknown input.
--
--   $$\Pr[T^o=\mathrm{accept}]=\Pr_{t\sim T}[\mathrm{execute}(t,o).\mathrm{out}=\mathrm{true}].$$
--
--   The depth cap bounds every execution by $q$ queries. Early halts add no transcript entries. Repeated queries and arbitrary real mixing weights are allowed. For the finite alphabets used here, there are finitely many such trees: fixing an algorithm's randomness and unfolding each possible answer history gives this normal form. Trees may depend on known parameters and the complete target, while the unknown input enters only through oracle answers. The transcript law additionally samples a supplied input distribution independently of the tree.
--
--   This is the shared access model for coordinate queries and graph incidence queries. It imposes no computation-time or randomness-length limit.
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), pp. 1–2, bounded-degree model and testers; p. 5, Claim 2.1 proof

import Mathlib

namespace GraphIsoTesting.FixedGraph

/-- Boolean-output adaptive trees with at most q actual queries, including early halts. -/
def QueryTree (Q R : Type) : ℕ → Type
  | 0 => Bool
  | q + 1 => Bool ⊕ (Q × (R → QueryTree Q R q))

/-- The ordered query/answer transcript and the final decision; true means accept. -/
def execute {Q R : Type} : (q : ℕ) → QueryTree Q R q → (Q → R) →
    List (Q × R) × Bool
  | 0, out, _ => ([], out)
  | _ + 1, .inl out, _ => ([], out)
  | q + 1, .inr (query, next), oracle =>
      let answer := oracle query
      let rest := execute q (next answer) oracle
      ((query, answer) :: rest.1, rest.2)

/-- An input-independent arbitrary probability law on adaptive trees. -/
abbrev RandomizedTester (Q R : Type) (q : ℕ) := PMF (QueryTree Q R q)

noncomputable def outputProbability {Q R : Type} {q : ℕ}
    (T : RandomizedTester Q R q) (oracle : Q → R) (out : Bool) : ENNReal :=
  (T.map (fun tree => (execute q tree oracle).2)) out

/-- Sample the input independently of the tester, then execute; no uncharged input access. -/
noncomputable def transcriptLaw {Q R B : Type} {q : ℕ}
    (T : RandomizedTester Q R q) (inputs : PMF B) (oracle : B → Q → R) :
    PMF (List (Q × R)) :=
  inputs.bind fun b => T.map fun tree => (execute q tree (oracle b)).1

end GraphIsoTesting.FixedGraph


