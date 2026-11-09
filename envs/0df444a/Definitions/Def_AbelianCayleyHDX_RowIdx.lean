-- Prove2me | Definitions.Def_AbelianCayleyHDX_RowIdx
-- name    : AbelianCayleyHDX_RowIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:18.715576+00:00
-- url     : https://prove2.me/theorems/c14f9286-b4d8-458c-a3cf-c069c26fcb91
-- title:
--   The row index set of $H_D$
-- statement:
--   The rows of $H_D$ are indexed by the triples $(b, x, \ell)$ with $b \in \hat D$, $x \in V_0$ and $\ell \in L_F$ ("for every $b \in \hat D$, $x \in V_0$ and $\ell \in L_F$, include the row …").
--
--   **Formalization Note** Indexing rows by the triples makes the row count $R$ and the claim that rows are distinct (Lemma 3.5) statements about this indexed family.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12

import Mathlib
import Definitions.Def_AbelianCayleyHDX_Dhat
import Definitions.Def_AbelianCayleyHDX_LF

namespace AbelianCayleyHDX

/-- **The row index set of `H_D`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12): "for every `b ∈ D̂`, `x ∈ V₀`, and
`ℓ ∈ L_F`, include the row …" — the triples `(b, x, ℓ) ∈ D̂ × V₀ × L_F`.

**Formalization Note** Rows are indexed by the triples themselves, so the row count `R` and the
claim that the rows are distinct (Lemma 3.5) are about this indexed family. -/
abbrev RowIdx {t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] (D : Finset (PG t F)) :
    Type _ :=
  {b // b ∈ Dhat D} × (Fin t → F) × {ℓ // ℓ ∈ LF F}

end AbelianCayleyHDX


