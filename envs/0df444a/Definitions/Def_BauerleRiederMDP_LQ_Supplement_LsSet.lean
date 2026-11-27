-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_LsSet
-- name    : BauerleRiederMDP_LQ_Supplement_LsSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:21:26.433809+00:00
-- url     : https://prove2.me/theorems/037b84d7-f92e-5763-8945-d23d8b145816
-- title:
--   upper limit of a set sequence
-- statement:
--   The **upper limit of a set sequence** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Appendix A.1, p.349, PDF 355): `LsA_n := {a ∈ M | a is an accumulation point of a sequence (a_n) with a_n ∈ A_n for all n ∈ ℕ}`.
--
--   **Formalization Note.** "Accumulation point of the sequence $(a_n)$" is Mathlib's `MapClusterPt a atTop an` (every neighbourhood of $a$ contains $a_n$ for infinitely many $n$), which in a metric space is the limit of a subsequence. The same set appears as the published `MDPFinance.Contracting.LsSeq`, which also requires a measurable structure on the space; Appendix A.1 works on a bare metric space, so the definition is restated here without it.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Appendix A.1, p.349, PDF 355

import Mathlib

open Filter Topology

namespace BauerleRiederMDP.LQ.Supplement

/-- The **upper limit of a set sequence** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Appendix A.1, p.349, PDF 355):
`LsA_n := {a ∈ M | a is an accumulation point of a sequence (a_n) with a_n ∈ A_n for all n ∈ ℕ}`.

**Formalization Note.** "Accumulation point of the sequence `(a_n)`" is Mathlib's
`MapClusterPt a atTop an` (every neighbourhood of `a` contains `a_n` for infinitely many `n`),
which in a metric space is the limit of a subsequence. The same set appears as the published
`MDPFinance.Contracting.LsSeq`, which also requires a measurable structure on the space; Appendix A.1
works on a bare metric space, so the definition is restated here without it. -/
def LsSet {M : Type*} [TopologicalSpace M] (A : ℕ → Set M) : Set M :=
  {a | ∃ an : ℕ → M, (∀ n, an n ∈ A n) ∧ MapClusterPt a atTop an}

end BauerleRiederMDP.LQ.Supplement


