-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_rank
-- name    : SeqPostedPricing_MatroidSPM_rank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:35.352863+00:00
-- url     : https://prove2.me/theorems/23887c24-b446-4225-b536-a17363ead4c3
-- title:
--   Rank $\mathrm{rank}(S)=\max_{S'\subseteq S,\,S'\in\mathcal J}|S'|$
-- statement:
--   The **rank** of a set $S\subseteq[n]$ of agents is the size of the largest feasible subset of $S$:
--
--   $$
--   \mathrm{rank}(S)=\max_{S'\subseteq S,\ S'\in\mathcal J}|S'| .
--   $$
--
--   No feasible mechanism serves more than $\mathrm{rank}(S)$ agents of $S$; this bounds the allocation probabilities in the proof of Theorem 5.
--
--   **Formalization Note** The paper's "$S'\subset S$" is read as $S'\subseteq S$. The maximum is $0$ when no subset of $S$ is feasible.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, unnumbered, p. 6

import Mathlib
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Rank of a set of agents.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4, unnumbered, p. 6 (PDF p. 8): "let the rank of a subset S of agents, rank(S), denote the
size of the largest feasible subset in S, that is, rank(S) = max_{S′⊂S,S′∈J} |S′|."

`rank Feas S` is the largest cardinality of a feasible subset of `S`.

**Formalization Note.** "S′ ⊂ S" is read as `S′ ⊆ S`, as the words "the largest feasible subset
in S" require. The maximum is a `Finset.sup` over the feasible subsets, which is `0` when no
subset of `S` is feasible (then nothing in `S` can be served). -/
noncomputable def rank {n : ℕ} (Feas : Finset (Fin n) → Prop) (S : Finset (Fin n)) : ℕ :=
  (S.powerset.filter Feas).sup Finset.card

end SeqPostedPricing.MatroidSPM


