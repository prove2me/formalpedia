-- Prove2me | Definitions.Def_GoodQLTC_Cosheaf
-- name    : GoodQLTC_Cosheaf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:27.599766+00:00
-- url     : https://prove2.me/theorems/0c6ce526-5c59-44e9-9872-a80d63bbf2f4
-- title:
--   Cosheaf on a poset (Definition 4.7)
-- statement:
--   A **cosheaf** $\mathcal F$ on $X$ over a field $F$ assigns a finite-dimensional $F$-space $\mathcal F(f)$ to each face and a linear map $R_{gf}:\mathcal F(f)\to\mathcal F(g)$ to each $f\le g$, such that $R_{ff}=\mathrm{id}$ and $R_{hg}R_{gf}=R_{hf}$ for $f\le g\le h$.
--
--   **Formalization Note** Stalks are coordinate spaces $F^{d(f)}$, so a cosheaf with chosen stalk bases is exactly this data; `R f g` is the matrix of $R_{gf}$ and is unused for $f\not\le g$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Definition 4.7, p.17 (PDF p.20)

import Mathlib

namespace GoodQLTC

/-- A **cosheaf** `F` on a poset `X` over a field `F`, Gay–Jeronimo, arXiv:2609.20780 (held
version), Definition 4.7, p.17: a finite-dimensional `F`-space `F(f)` for each face `f` and a
linear map `R_{gf} : F(f) → F(g)` for each `f ≤ g`, with `R_{ff} = id` and `R_{hg} R_{gf} = R_{hf}`
for all `f ≤ g ≤ h`.

**Formalization Note.** Each stalk is the coordinate space `F^{d(f)}` (`Fin (d f) → F`), so a
cosheaf with a choice of stalk bases is exactly this data (the paper's "choose bases of all
stalks", p.18, is absorbed into the encoding). `R f g` is the matrix of `R_{gf}` (rows indexed by
`F(g)`); its value for `f ≰ g` is never used. -/
structure Cosheaf (X : Type) [PartialOrder X] (F : Type) [Field F] where
  /-- the stalk dimensions `dim_F F(f)` -/
  d : X → ℕ
  /-- `R f g` is the matrix of `R_{gf} : F(f) → F(g)` -/
  R : ∀ f g : X, Matrix (Fin (d g)) (Fin (d f)) F
  R_self : ∀ f, R f f = 1
  R_comp : ∀ f g h : X, f ≤ g → g ≤ h → R g h * R f g = R f h

end GoodQLTC


