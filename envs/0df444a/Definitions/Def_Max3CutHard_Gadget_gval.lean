-- Prove2me | Definitions.Def_Max3CutHard_Gadget_gval
-- name    : Max3CutHard_Gadget_gval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:29.538332+00:00
-- url     : https://prove2.me/theorems/e11875eb-476b-4f91-8abf-5605928e755f
-- title:
--   The gadget value $V_I(x,y)$
-- statement:
--   For a gadget $I$, colours $x\in[k]^3$ of the primaries and $y\in[k]^k$ of the globals,
--
--   $$V_I(x,y)=\max\{\mathrm{cut}_\chi(I):\ \chi(p_j)=x_j,\ \chi(g_i)=y_i\},$$
--
--   the maximum being over the colours of the auxiliary vertices.
--
--   **Formalization Note** Defined for every $y$, without the source's normalisation $y\in Y_k$ (which the source calls a computational saving only).
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Gadgets, pp.4–5

import Mathlib
import Definitions.Def_Max3CutHard_Gadget
import Definitions.Def_Max3CutHard_cutR

namespace Max3CutHard

/-- **The gadget value `V_I(x, y)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Gadgets, pp.4–5: "For `x ∈ [k]^3` and
`y ∈ [k]^k` let `V_I(x, y) = max{cut_χ(I) : χ(p_j) = x_j, χ(g_i) = y_i}`, the maximum being over
the colours of the auxiliary vertices."

**Formalization Note.** `x : Fin 3 → Fin k` (0-based primaries), `y : Fin k → Fin k`; a finite
nonempty maximum over `z : Fin I.aux → Fin k` (`Finset.sup'`). Defined for every `y`: no
normalisation `y ∈ Y_k`. -/
noncomputable def Gadget.gval {k : ℕ} [NeZero k] (I : Gadget k) (x : Fin 3 → Fin k) (y : Fin k → Fin k) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun z : Fin I.aux → Fin k =>
    cutR (Sum.elim x (Sum.elim y z)) I.edges

end Max3CutHard


