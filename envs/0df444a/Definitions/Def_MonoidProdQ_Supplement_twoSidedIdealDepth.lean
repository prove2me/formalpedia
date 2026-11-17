-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_twoSidedIdealDepth
-- name    : MonoidProdQ_Supplement_twoSidedIdealDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:13:10.01921+00:00
-- url     : https://prove2.me/theorems/9eebc5c8-b72a-49ca-87c7-8f74bf9618f8
-- title:
--   Two-sided ideal depth $D_J(M)$
-- statement:
--   For a monoid $M$, $D_J(M)$ is the length of the longest chain of principal two-sided ideals
--
--   $$Mm_0M\subsetneq Mm_1M\subsetneq\cdots\subsetneq Mm_kM,$$
--
--   counted as the number $k$ of strict containments ($k\le|M|-1$ for finite $M$). It appears in the exponent of the quantitative AGS bound of Theorem 58.
--
--   **Formalization Note** A natural-number supremum over chain lengths, indexed by $\{0,\dots,k\}$; the set of lengths contains $0$ and is bounded for finite $M$, so the supremum is attained (for an infinite monoid with unbounded chains it would be the junk value $0$; every statement using $D_J$ assumes $M$ finite). $MmM$ is the set $\{amb:a,b\in M\}$.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, p.23

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, p.23: "Define D_J(M) to be the length of
the longest chain Mm₁M ⊊ Mm₂M ⊊ ⋯ ⊊ MmₖM of principal two-sided ideals, counted as the number of
strict containments k − 1 ≤ |M| − 1": the largest `k` such that there are `m₀, …, mₖ ∈ M` with
`Mm₀M ⊊ Mm₁M ⊊ ⋯ ⊊ MmₖM`.

**Formalization Note.** The two-sided ideal `MmM = {amb : a, b ∈ M}` is the set
`{s | ∃ a b, a * m * b = s}`. A chain of `k` strict containments has `k + 1` members, indexed by
`Fin (k + 1)`. The value is a natural-number supremum; the set contains `0` and, for a finite
monoid, is bounded by `|M| − 1`, so the supremum is attained. For an infinite monoid with
unbounded chains `sSup` would be the junk value `0`; every statement using `D_J` assumes `M`
finite. -/
noncomputable def twoSidedIdealDepth (M : Type*) [Monoid M] : ℕ :=
  sSup {k : ℕ | ∃ m : Fin (k + 1) → M, ∀ i : Fin k,
    {s : M | ∃ a b : M, a * m i.castSucc * b = s} ⊂ {s : M | ∃ a b : M, a * m i.succ * b = s}}

end MonoidProdQ.Supplement


