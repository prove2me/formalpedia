-- Prove2me | Definitions.Def_Patching_CohenMacaulayOfDim
-- name    : Patching_CohenMacaulayOfDim
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/4dbfe8de-5971-5b9d-80f7-0cf63c8c00e8
-- title:
--   Cohen–Macaulay local rings of a given dimension
-- statement:
--   For a commutative local ring $R$ and a natural number $d$, this module defines the predicate [`IsLocalRing.IsCohenMacaulayOfDim R d`](../def/Patching_CohenMacaulayOfDim.html#L10), asserting the conjunction of two equalities: the Krull dimension of $R$, as measured by Mathlib's `ringKrullDim` (with values in $\mathbb{Z}\cup\{\pm\infty\}$-style extended order, here compared with the coerced $d$), equals $d$; and $\operatorname{depth}_R R = d$, where the depth is the project's [`Module.depth`](../def/Patching_SystemTypes.html#L34), defined as the supremum in $\mathbb{N}\cup\{\infty\}$ of the lengths of lists $s$ of elements of $R$ that form a weakly regular sequence on the module in question and all of whose members lie in the maximal ideal $\mathfrak m_R$. Thus the predicate is the Cohen–Macaulay condition for a local ring in the form $\dim R = \operatorname{depth}_R R = d$, with the common value pinned to a prescribed natural number; in particular finiteness of both invariants is part of the assertion, and no separate general notion of Cohen–Macaulayness (depth equal to dimension without naming the value, or for modules other than $R$ itself) is introduced here. The two accompanying lemmas are the projections of the conjunction: from `IsCohenMacaulayOfDim R d` one reads off `ringKrullDim R = d` and [`Module.depth R R = d`](../def/Patching_SystemTypes.html#L34).
--
--   **Relation to Mathlib.** The Krull dimension is Mathlib's `ringKrullDim` and the regularity condition underlying the depth is Mathlib's weak regularity of sequences; the depth itself is the project's [`Module.depth`](../def/Patching_SystemTypes.html#L34) (supremum of lengths of weakly regular sequences inside the maximal ideal), and the Cohen–Macaulay-of-fixed-dimension predicate is the project's own.
--
--   **Where it is used.** The predicate packages exactly the input required at the end of the Taylor–Wiles patching argument, where two local rings — a power series ring $\Lambda = \mathcal{O}[[y_1,\dots,y_r]]$ over the coefficient ring and the patched deformation ring $R_\infty = \mathcal{O}[[x_1,\dots,x_g]]$ — are Cohen–Macaulay of the same dimension, so that the finiteness of $\dim R_\infty$ and the equality $\operatorname{depth}\Lambda = \dim R_\infty$ needed there are available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Patching_CohenMacaulayOfDim.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

def IsCohenMacaulayOfDim (d : ℕ) : Prop :=
  ringKrullDim R = d ∧ Module.depth R R = d

namespace IsCohenMacaulayOfDim

variable {R} {d : ℕ}

lemma ringKrullDim_eq (h : IsCohenMacaulayOfDim R d) : ringKrullDim R = d := h.1

lemma depth_eq (h : IsCohenMacaulayOfDim R d) : Module.depth R R = d := h.2

end IsCohenMacaulayOfDim

end IsLocalRing


