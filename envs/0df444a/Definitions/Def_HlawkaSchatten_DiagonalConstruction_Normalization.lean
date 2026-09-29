-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
-- name    : HlawkaSchatten_DiagonalConstruction_Normalization
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:32:00.450402+00:00
-- url     : https://prove2.me/theorems/db77e7ef-74bb-47e0-8ab3-db4c064e23bd
-- title:
--   The Hlawka deficit of a candidate constant on a coordinate triple
-- statement:
--   `hlawkaDeficit` packages the Hlawka inequality for the finite coordinate power functional and a candidate constant as a single real number, for vectors $x,y,z$ indexed by an arbitrary finite type:
--   $$
--   \operatorname{hlawkaDeficit}(p,K,x,y,z) = (2K-1)\big(\|x\|_p+\|y\|_p+\|z\|_p\big) + \|x+y+z\|_p - K\big(\|x+y\|_p+\|x+z\|_p+\|y+z\|_p\big),
--   $$
--   using the finite coordinate power functional $\|\cdot\|_p$ (`DiagonalConstruction.lpNorm`), which is a norm for $p\ge1$. The definition itself accepts every real $p$.
--
--   Equivalently, by a theorem in the same source module, $\operatorname{hlawkaDeficit}(p,K,x,y,z)$ equals $K$ times the pair-deficit sum minus the triple deficit for $x,y,z$ (`pairGapSum`, `tripleGap`). So $\operatorname{hlawkaDeficit}(p,K,x,y,z)\ge 0$ says exactly that the triple deficit for $x,y,z$ is at most $K$ times their pair-deficit sum, and a negative value witnesses a strict failure of that bound for the constant $K$.
--
--   This single real-valued packaging is what lets the theorems that accompany it manipulate a hypothetical failure algebraically: for $K\ge1$, relabeling — permuting $x,y,z$ and, if needed, replacing $x$ by $-(x+y+z)$ — so that the total norm $\|x+y+z\|_p$ is at least as large as each of $\|x\|_p,\|y\|_p,\|z\|_p$, which can only decrease a negative deficit; and then, for $p>0$, rescaling so that $\|x\|_p+\|y\|_p+\|z\|_p=1$, which multiplies the deficit by a positive factor.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Normalization.lean#L15-L18

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Abel

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Relabeling and normalization of a strict counterexample -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

/-- The target inequality with all terms moved to the nonnegative side. -/
noncomputable def hlawkaDeficit (p K : ℝ) (x y z : ι → ℝ) : ℝ :=
  (2 * K - 1) * (lpNorm p x + lpNorm p y + lpNorm p z) + lpNorm p (x + y + z) -
    K * (lpNorm p (x + y) + lpNorm p (x + z) + lpNorm p (y + z))



















end HlawkaSchatten.DiagonalConstruction


