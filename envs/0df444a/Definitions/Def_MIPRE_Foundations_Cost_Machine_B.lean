-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Machine_B
-- name    : MIPRE_Foundations_Cost_Machine_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:20:46.713489+00:00
-- url     : https://prove2.me/theorems/6c63b731-3f46-40ad-9034-160d6391b3f6
-- title:
--   Additivity of the accumulated cost along runs of the evaluation machine
-- statement:
--   This bundle adds one declaration to the already published bundle `MIPRE_Foundations_Cost_Machine`, the small-step (CEK-style) evaluation machine of the ambient language. A configuration $c$ (`Cfg`) consists of a control, an environment and a stack of continuation frames; `step` is the one-step transition, `stepCost c` the cost charged at the configuration $c$, and `costSum c N` the cost accumulated over $N$ steps from $c$, defined by $\mathrm{costSum}\,c\,0 = 0$ and $\mathrm{costSum}\,c\,(n+1) = \mathrm{stepCost}\,c + \mathrm{costSum}\,(\mathrm{step}\,c)\,n$. The added theorem states that accumulated cost splits at any intermediate point of a run: for every configuration $c$ and naturals $m, n$,
--
--   $$\mathrm{costSum}\,c\,(m + n) \;=\; \mathrm{costSum}\,c\,m \;+\; \mathrm{costSum}\,(\mathrm{step}^{[m]}\,c)\,n.$$
--
--   It is the bookkeeping lemma behind the composition of machine runs (`Steps`), whose cost component is a `costSum`, and behind the cost sums of `Cost/MachineBound.lean`.
--
--   **Formalization Note** The statement is `costSum_add (c : Cfg) (m n : ℕ) : costSum c (m + n) = costSum c m + costSum (step^[m] c) n`, where `step^[m]` is the $m$-fold iterate `Nat.iterate`. All quantities are natural numbers; `costSum` is total.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Machine.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Machine.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Machine does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Machine

/-!
# The evaluation machine

A small-step abstract machine (CEK style) for the ambient language: a configuration is a
control (a program to evaluate, or a value being returned), an environment and a stack of
continuation frames. It is the common core of the two "universal" artifacts of the
project:

* Mathlib-computability of ambient evaluation (`Cost/Partrec.lean`): the step function,
  transported to `Data`, is primitive recursive and evaluation is its `PFun.fix`;
* the self-interpreter of the ambient model in the ambient model (route β of the
  universal-machine gate): a program implementing the step function inside a `loop`.

The machine charges the cost of each `Eval` rule at a designated step (`stepCost`), so
that the accumulated cost of a run is exactly the cost of the `Eval` derivation. The two
directions of the correspondence are `eval_steps` (a derivation yields a run of the
machine) and `eval_of_steps` (a halting run of the machine yields a derivation).
-/

namespace MIPRE.Cost

namespace Machine

theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega

namespace Steps

end Steps

/-! ## Forward: derivations give machine runs -/

/-! ## Backward: halting runs give derivations -/

end Machine

end MIPRE.Cost


