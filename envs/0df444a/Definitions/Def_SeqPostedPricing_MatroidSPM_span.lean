-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_span
-- name    : SeqPostedPricing_MatroidSPM_span
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:36:02.738054+00:00
-- url     : https://prove2.me/theorems/7e6d1269-0de2-47f6-9989-001fee6ca3c7
-- title:
--   Span $\mathrm{span}(S)=\{e:\mathrm{rank}(S\cup\{e\})=\mathrm{rank}(S)\}$
-- statement:
--   The **span** of a set $S\subseteq[n]$ is
--
--   $$
--   \mathrm{span}(S)=\{e\in[n]:\ \mathrm{rank}(S\cup\{e\})=\mathrm{rank}(S)\}.
--   $$
--
--   The paper defines $\mathrm{span}(S)$ as the maximal set $T\supseteq S$ with $\mathrm{rank}(T)=\mathrm{rank}(S)$; for a matroid the two definitions agree (milestone *span*). The agents blocked by a set $S$ of served agents lie in its span.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.1, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_rank
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **Span of a set of agents.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, unnumbered, p. 6 (PDF p. 8): "The span of a set S ⊆ [n], span(S), is the maximal set
T ⊇ S with rank(T) = rank(S)."

`span Feas S` is the set of agents `e` with `rank(S ∪ {e}) = rank(S)`.

**Formalization Note.** Defined by this element-wise test rather than as a maximal set (whose
existence and uniqueness is a theorem). For a matroid the two agree: that is milestone
`span_isGreatest`. -/
noncomputable def span {n : ℕ} (Feas : Finset (Fin n) → Prop) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun e => rank Feas (insert e S) = rank Feas S)

end SeqPostedPricing.MatroidSPM


