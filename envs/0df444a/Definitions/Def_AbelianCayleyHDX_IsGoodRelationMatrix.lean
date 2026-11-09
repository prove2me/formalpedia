-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
-- name    : AbelianCayleyHDX_IsGoodRelationMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:54.228237+00:00
-- url     : https://prove2.me/theorems/89d77e07-c48c-4c49-a69b-0082497ad2a2
-- title:
--   Relation matrix: distinct weight-three rows, column weight $\rho$, distance $\ge 3$
-- statement:
--   A binary **relation matrix** $H \in \mathbb F_2^{R \times M}$ specifies linear relations among $M$ generators. Section 2.4 focuses on relation matrices such that
--   1. the rows are distinct;
--   2. every row has weight three;
--   3. every column has the same weight $\rho$, and $\rho > 0$;
--   4. the row space $R_H$ has minimum distance at least three.
--
--   **Formalization Note** Rows are indexed by a finite type, so "distinct rows" is injectivity of $r \mapsto H_r$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9

import Mathlib
import Definitions.Def_AbelianCayleyHDX_rowspan
import Definitions.Def_AbelianCayleyHDX_MinDistAtLeast3
import Definitions.Def_AbelianCayleyHDX_rowWeight
import Definitions.Def_AbelianCayleyHDX_colWeight

namespace AbelianCayleyHDX

/-- **The relation matrices of Section 2.4** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9): "relation matrices with
distinct rows of weight three and constant positive column weight `ρ`" whose row space
"`R_H = rowspan_{𝔽₂} H` has minimum distance at least three".

**Formalization Note** Rows are indexed by a type `ι`, so "distinct rows" is injectivity of
`r ↦ H r`. -/
def IsGoodRelationMatrix {ι κ : Type*} [Fintype ι] [Fintype κ] (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) :
    Prop :=
  Function.Injective H ∧ (∀ r, rowWeight H r = 3) ∧ 0 < ρ ∧ (∀ c, colWeight H c = ρ) ∧
    MinDistAtLeast3 (rowspan H)

end AbelianCayleyHDX


