-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Algorithm
-- name    : GreedyColoringLCA969_LowerBound_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:44:43.011635+00:00
-- url     : https://prove2.me/theorems/0d569bd0-4bde-45db-975e-9881a0c92932
-- title:
--   Unbounded adaptive local-query rules and shared-tape seed fixings
-- statement:
--   A local-query rule receives $n$, the questioned vertex $v$, and a finite transcript of replies. It chooses one of four actions: return a positive integer color, issue an allowed graph query, read bit $j$ of the shared tape for any $j\in\mathbb N$, or take an internal computation step. The tape is an infinite binary sequence $r$:
--
--   $$A(n,v,h)\in\{\operatorname{return}(c),\operatorname{query}(q),\operatorname{readBit}(j),\operatorname{tick}\}.$$
--
--   The rule itself has no graph or tape argument. The interpreter alone supplies replies. Requests are reconstructible from the rule and the preceding transcript. The rule may use arbitrary local computation and there is no bound on transcript length, depth, or bit positions. A deterministic seed fixing is a pair of a rule and one fixed tape, both chosen before the input graph.
--
--   This interface includes every source algorithm: suppress internal computation until the next observable action and record its reply, or retain individual internal steps as ticks. It also admits noncomputable decision rules and partial runs, a declared enlargement of the source machine class. No correctness or efficiency requirement is built into the rule.
--
--   Differences from the source:
--   - generalization: algorithms that output positive integer labels using finite observable operations → arbitrary next-action rules, also admitting partial or noncomputable runs; reason: every source algorithm embeds by its successive actions; nontermination is failure with infinite cost, and no new graph information is available
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Definition 2.6, p.8 (PDF 9); Appendix A.2, pp.36–37 (PDF 37–38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Oracle

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- One infinite shared random-access tape. -/
abbrev Tape := ℕ → Bool

/-- A transcript records graph replies, random-bit replies, or an internal tick.
The corresponding request is reconstructed from the preceding transcript and next-action rule. -/
abbrev History := List (List ℕ ⊕ (Bool ⊕ Unit))

inductive Action (m : OracleMode) (n : ℕ) where
  | halt (color : ℕ+)
  | query (q : GraphQuery m n)
  | readBit (j : ℕ)
  | tick

/-- Definition 2.6, as unrestricted next-action rules. Only the interpreter sees the graph
and tape. The rule receives n, the original question, and a finite transcript. There is
no fuel/depth bound, adjacency ordering constraint, or locality restriction. Arbitrary
local computation may be collapsed into the rule; ticks can also record internal steps. -/
abbrev Algorithm (m : OracleMode) := (n : ℕ) → Fin n → History → Action m n

/-- A deterministic seed fixing: both rule and tape are fixed before the input is drawn.
This includes every tape-free deterministic rule and every A_r used in Appendix A.2. -/
abbrev DeterministicLCA (m : OracleMode) := Algorithm m × Tape

end GreedyColoringLCA969.LowerBound


