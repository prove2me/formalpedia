-- Prove2me | Definitions.Def_MatroidEquitability_maxWeight
-- name    : MatroidEquitability_maxWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:50.24399+00:00
-- url     : https://prove2.me/theorems/cfee8257-9ee2-4d3a-a90e-0e12e213ed63
-- title:
--   Largest element weight $\max_{e\in E}w_e$, with value $0$ on $E=\emptyset$
-- statement:
--   For a matroid $M=(E,\mathcal I)$ and weights $w$, this is the largest element weight
--
--   $$
--   \max_{e\in E}w_e ,
--   $$
--
--   with the paper's convention that $\max_{e\in\emptyset}w_e=0$. It is the bound in the equitability inequality (1).
--
--   **Formalization Note** It is the real `sSup` of the image of $E$ under $w$. On a finite nonempty ground set this image is finite and nonempty, so the `sSup` is its maximum; on an empty ground set the real `sSup` is $0$, which is the convention above. Every statement using it assumes the matroid finite.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), §1.3, p.7 (PDF p.9)

import Mathlib

namespace MatroidEquitability

/-- The largest element weight `max_{e∈E} w_e` of a matroid `M = (E, I)`, with the convention
`max_{e∈∅} w_e = 0` (§1.3, printed p.7 = PDF p.9 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** This is the real `sSup` of the image `w '' M.E`. On a finite nonempty ground
set the image is finite and nonempty, so this is its maximum; on an empty ground set the real `sSup`
is `0`, which is the paper's convention. Every statement using it carries `[M.Finite]`. -/
noncomputable def maxWeight {α : Type*} (M : Matroid α) (w : α → ℝ) : ℝ :=
  sSup (w '' M.E)

end MatroidEquitability


