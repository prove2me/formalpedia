-- Prove2me | Definitions.Def_LinfContractionFP_lowerMedian
-- name    : LinfContractionFP_lowerMedian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:19.350202+00:00
-- url     : https://prove2.me/theorems/6d2b0bab-acc4-49a9-bd79-501e02308dd7
-- title:
--   The (lower) median of $d$ reals
-- statement:
--   For reals $w_1,\dots,w_d$, the **lower median** is the $\lceil d/2\rceil$-th smallest of them (with multiplicity). With $t$ the lower median, at most $\lfloor d/2\rfloor$ of the $w_i$ are $<t$ and at most $\lfloor d/2\rfloor$ are $>t$.
--
--   This is the median $t$ of the half side lengths in Algorithm 2.
--
--   **Formalization Note** "Median" is read as the lower median; any choice with at most $d/2$ values on each strict side serves the proof. For $d=0$ the value is $0$ and is never used.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Algorithm 2, line 2, p.9; Section 5, p.8

import Mathlib

namespace LinfContractionFP

/-- The (lower) median of the values `w_i`, `i ∈ ι`: the `⌈d/2⌉`-th smallest of them, where
`d = |ι|` (counted with multiplicity).

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Algorithm 2, line 2, p.9:
"t ← median of the {w_i}_{i=1}^d"; Section 5, p.8: "Letting m denote the median side length".

**Formalization Note.** "Median" is read as the lower median, the element at position
`⌈d/2⌉ − 1` (0-based) of the sorted list of the `w_i`. Then fewer than `⌈d/2⌉` of the `w_i` are
`< t` and at most `⌊d/2⌋` are `> t`, so both `{i : w_i < t}` and `{i : w_i > t}` have at most
`⌊d/2⌋` elements, which is what the paper uses ("Each recursive problem has dimension at most
d/2", p.8). For `d = 0` the value is `0` (never used). -/
noncomputable def lowerMedian {ι : Type} [Fintype ι] (w : ι → ℝ) : ℝ :=
  ((Finset.univ.val.map w).sort (· ≤ ·)).getD ((Fintype.card ι + 1) / 2 - 1) 0

end LinfContractionFP


