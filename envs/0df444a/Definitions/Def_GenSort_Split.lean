-- Prove2me | Definitions.Def_GenSort_Split
-- name    : GenSort_Split
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:14.297744+00:00
-- url     : https://prove2.me/theorems/210735f4-b201-4e07-8709-fc003933adcc
-- title:
--   Splitting the edges at each vertex into groups of size at most $d$
-- statement:
--   After orienting $F$ by $\sigma$, each vertex $u$ has a left degree (oriented edges leaving $u$) and a right degree (edges entering $u$). **A split** assigns to every oriented edge $(u, v)$ a group index at its left endpoint and one at its right endpoint, such that at a vertex of degree $\delta$ on a side the indices are smaller than $\lceil \delta/d \rceil$, and each group has at most $d$ edges. Each group becomes a separate copy of the vertex: "If any left or right vertex has more than $d$ incident edges, we split the edges into groups of size at most $d$, making a separate copy of the vertex for each group."
--
--   **Formalization Note** The page leaves the split arbitrary, so every statement quantifies over all splits. The number of groups is exactly $\lceil \delta/d\rceil$ (none is empty, since each holds at most $d$ edges); the bare phrase "groups of size at most $d$" would allow more copies than the count $n + f/d$ in the proof of Claim 3.2. Copy indices are elements of `Fin n`.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_GenSort_orient

namespace GenSort

/-- **A splitting of the oriented edges into groups of size at most `d`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF
p.8): "If any left or right vertex has more than `d` incident edges, we split the edges into
groups of size at most `d`, making a separate copy of the vertex for each group."

An edge `(u, v)` of `orient F σ` is attached to the left copy `(u, lc (u,v))` and to the right
copy `(v, rc (u,v))`. At a vertex of degree `δ` on one side, the group indices are `< ⌈δ/d⌉`, and
each group has at most `d` edges.

**Formalization Note.** The split is arbitrary, so every theorem quantifies over all splits. The
number of groups at a vertex of degree `δ` is exactly `⌈δ/d⌉` (the indices are `< ⌈δ/d⌉`, and
since each group holds at most `d` edges none of them is empty); "groups of size at most `d`"
alone would allow more copies than the count `n + f/d` of Claim 3.2 uses. A vertex with at most
`d` edges has one group. Copy indices live in `Fin n`, which suffices since `⌈δ/d⌉ ≤ δ < n`. -/
structure Split {n : ℕ} (F : Finset (Sym2 (Fin n))) (σ : Equiv.Perm (Fin n)) (d : ℕ) where
  /-- Group index of the edge at its left endpoint. -/
  lc : Fin n × Fin n → Fin n
  /-- Group index of the edge at its right endpoint. -/
  rc : Fin n × Fin n → Fin n
  lc_lt : ∀ p ∈ orient F σ,
    (lc p : ℕ) < ⌈(((orient F σ).filter fun q => q.1 = p.1).card : ℝ) / d⌉₊
  rc_lt : ∀ p ∈ orient F σ,
    (rc p : ℕ) < ⌈(((orient F σ).filter fun q => q.2 = p.2).card : ℝ) / d⌉₊
  lc_card : ∀ u j : Fin n, ((orient F σ).filter fun q => q.1 = u ∧ lc q = j).card ≤ d
  rc_card : ∀ v j : Fin n, ((orient F σ).filter fun q => q.2 = v ∧ rc q = j).card ≤ d

end GenSort


