-- Prove2me | Definitions.Def_Zeta23_RvM_BacklundDefs
-- name    : Zeta23_RvM_BacklundDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:21:52.345683+00:00
-- url     : https://prove2.me/theorems/d3717f04-bb23-4a8f-b673-c68559505761
-- title:
--   Zero set of $\operatorname{Re}\zeta(\sigma+iT)$ on $[1/2,2]$
-- statement:
--   Shared definition for Backlund's bound on the horizontal segments of the Riemann–von Mangoldt contour. For a real height $T$, `reZeroSet T` is the set of abscissae at which the real part of $\zeta$ vanishes on the closed segment $[1/2,2]$ at height $T$:
--   $$\mathrm{reZeroSet}(T) \;:=\; \{\sigma\in[1/2,2] : \operatorname{Re}\zeta(\sigma+iT)=0\}.$$
--
--   **Role.** Backlund's classical device bounds the variation of $\arg\zeta$ along a horizontal segment by the number of zeros of $\operatorname{Re}\zeta(\sigma+iT)$ on it. The cardinality bound `reZeroSet_card_le` (the Jensen half) lives in `Zeta23/RvM/ReZeroCount.lean`, and the argument-variation half together with the assembly `backlund_horizontal` (used for the $O(\log T)$ error in the Riemann–von Mangoldt count $N(T,2T)$) is in `Zeta23/RvM/Backlund.lean`; this small file provides the definition both sides refer to.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/BacklundDefs.lean

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/BacklundDefs.lean — shared definition for Backlund's bound.
The Jensen count `reZeroSet_card_le` is in Zeta23/RvM/ReZeroCount.lean; the
argument-variation half and the assembly of `backlund_horizontal` are in
Zeta23/RvM/Backlund.lean.
-/

open Complex

noncomputable section

namespace Zeta23
namespace RvM

/-- The zero set of `σ ↦ Re ζ(σ+iT)` on `[1/2, 2]` (used by
`reZeroSet_card_le` and `im_integral_logDeriv_le` / `backlund_horizontal`). -/
def reZeroSet (T : ℝ) : Set ℝ :=
  {σ | σ ∈ Set.Icc (1/2 : ℝ) 2 ∧ (riemannZeta (σ + T * I)).re = 0}


end RvM
end Zeta23

end


