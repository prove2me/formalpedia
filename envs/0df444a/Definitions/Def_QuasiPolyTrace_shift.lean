-- Prove2me | Definitions.Def_QuasiPolyTrace_shift
-- name    : QuasiPolyTrace_shift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:01.036209+00:00
-- url     : https://prove2.me/theorems/3906fe5a-06ac-4fa5-a78c-8ca019944eed
-- title:
--   The shifted statistic $s+\ell$
-- statement:
--   For a finite set $s$ of integer positions and an integer $\ell$, the **shifted statistic** is
--
--   $$
--   s+\ell=\{\,i+\ell : i\in s\,\}.
--   $$
--
--   The sequence $j\mapsto x^{(s+j)}_p$ of all shifts of one statistic is the object the paper's induction manipulates (Lemma 36, Proposition 37).
--
--   **Formalization Note** Shifted entries may be $\le 0$; the statistic then reads $0$, the paper's convention (p.7).
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Definition 3, p.6 (s + ℓ); p.7 (invalid indices read 0)

import Mathlib

namespace QuasiPolyTrace

/-- **The shifted statistic `s + ℓ`.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Definition 3, p.6: "Treating s as a vector, if ℓ is an
integer then s + ℓ is interpreted as adding ℓ to all entries of s".

`shift s ℓ = {i + ℓ : i ∈ s}`.

**Formalization Note.** Entries may become `≤ 0`; `stat` then returns 0, which is the paper's
convention (p.7). -/
def shift (s : Finset ℤ) (ℓ : ℤ) : Finset ℤ :=
  s.map (Equiv.addRight ℓ).toEmbedding

end QuasiPolyTrace


