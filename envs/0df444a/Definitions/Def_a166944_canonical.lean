-- Prove2me | Definitions.Def_a166944_canonical
-- name    : a166944_canonical
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-14T23:11:04.270199+00:00
-- url     : https://prove2.me/theorems/dc2e20b2-da46-46dc-a67f-454a455af1b9
-- title:
--   OEIS A166944 — the offset coordinate B, attained previous maxima, and the last nontrivial increment
-- statement:
--   This bundle adds the three derived predicates used by the record-index and canonical-return statements about OEIS A166944.
--
--   The sequence $a$ is the Rowland-type recursion of A166944, with first differences $d_n=a_n-a_{n-1}$.
--
--   1. The **offset coordinate** is
--
--   $$
--   B_n=a_n-(2n-2),
--   $$
--
--   the distance of $a_n$ from the linear comparison sequence $2n-2$. A return $B_m=2$ marks the point at which $a_m=2m$, i.e. the sequence has caught up with its linear benchmark.
--
--   2. A pair $(P,k)$ exhibits $P$ as an **attained previous maximum** through $k$ when $d_j\le P$ for every $2\le j\le k$ and $d_r=P$ for some $2\le r\le k$: the value $P$ is a running maximum of the differences on the prefix $[2,k]$ and it actually occurs there. The occurrence is intentionally existential; the first occurrence is extracted by a separate theorem so that it can be used as a strict difference record.
--
--   3. A pair $(\rho,m)$ exhibits $\rho$ as the **last nontrivial increment before $m$** when $2\le\rho<m$, the increment at $\rho$ is nontrivial ($1<d_\rho$), and every increment strictly after $\rho$ and up to $m$ is trivial ($d_j=1$ for $\rho<j\le m$). This is a predicate only: it asserts no existence, and it is supplied to the theorems that need it as a hypothesis.
--
--   The three declarations are the vocabulary in which the record-index equivalence is stated: the difference records of A166944 are exactly the strict records whose index sits two above the record value, and that claim is equivalent to excluding a larger first hit inside the horizon of a capped canonical replay. Making $B$, `IsAttainedPreviousMaximum` and `IsLastNontrivialBefore` first-class definitions keeps that equivalence importable instead of restating it locally.
--
--   **Formalization Note** `B` uses truncated subtraction on `Nat`. All three predicates restrict their indices to $\ge 2$, the range in which the recurrence's differences are defined without truncation artifacts.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Derived coordinates and predicates as used by the A166944 record-index development: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/ResearchDefs.lean (IsAttainedPreviousMaximum, IsLastNontrivialBefore) and https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/CanonicalRecord.lean (record_index_iff_canonical_returns).

import Definitions.Def_a166944_record_core

namespace A166944Research

/-- `B n = a n - (2n - 2)`. -/
def B (n : Nat) : Nat := a n - (2 * n - 2)

/-- `P` is an attained running maximum through `k`. -/
def IsAttainedPreviousMaximum (P k : Nat) : Prop :=
  (∀ j : Nat, 2 ≤ j → j ≤ k → d j ≤ P) ∧
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P

/-- A candidate last nontrivial increment before `m` (a predicate only). -/
def IsLastNontrivialBefore (rho m : Nat) : Prop :=
  2 ≤ rho ∧ rho < m ∧ 1 < d rho ∧
    ∀ j : Nat, rho < j → j ≤ m → d j = 1

end A166944Research


