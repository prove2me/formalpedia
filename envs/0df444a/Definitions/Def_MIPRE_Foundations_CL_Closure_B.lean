-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Closure_B
-- name    : MIPRE_Foundations_CL_Closure_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:26.533515+00:00
-- url     : https://prove2.me/theorems/1e5ae226-64cb-4392-a436-57450aa339b8
-- title:
--   Definitions of Closure (addendum): Closure properties of conditionally linear functions, and CL distributions Paper `linear.tex`: concatenation…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.Closure` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Closure properties of conditionally linear functions, and CL distributions. Paper `linear.tex`: concatenation (`lem:cl-concat`) and direct sums (`lem:cl-func-prod`) of conditionally linear functions, and the conditionally linear distribution of a pair of CL functions (`def:cl-dist`); blueprint `def:cl-function` and `lem:cl-closure`, ledger node `1.1.2`. Both constructions are on presentations (`MIPRE.CL.CLFun`) and are hypothesis-free; the hypotheses of the paper's lemmas — the pieces live on disjoint register subspaces — enter only in the evaluation lemmas (`SupportedOn.eval_concat`,…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_CL_Closure` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `union_sdiff_union`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.Closure` (`MIPRE/Foundations/CL/Closure.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Closure.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Closure.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_CL_Closure does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure

/-!
# Closure properties of conditionally linear functions, and CL distributions

Paper `linear.tex`: concatenation (`lem:cl-concat`) and direct sums (`lem:cl-func-prod`) of
conditionally linear functions, and the conditionally linear distribution of a pair of CL
functions (`def:cl-dist`); blueprint `def:cl-function` and `lem:cl-closure`, ledger node
`1.1.2`.

Both constructions are on presentations (`MIPRE.CL.CLFun`) and are hypothesis-free; the
hypotheses of the paper's lemmas — the pieces live on disjoint register subspaces — enter only
in the evaluation lemmas (`SupportedOn.eval_concat`, `SupportedOn.eval_directSum`), which say
that the constructions present the functions the paper writes down, and in the support
lemmas. The paper's statements about *functions* follow as `IsCLFun.concat` and
`IsCLFun.directSum`.

* `CLFun.concat L R`: run `L` (level `k`), then the `R_u` (level `ℓ`) selected by its output;
  level `ℓ + k` — the paper's `T(x) = L(x^U) + R_{L(x^U)}(x^V)` on `U ⊕ V`, here for `L` on
  `V_U`, the `R_u` on `V_W`, `U` and `W` disjoint.
* `CLFun.directSum P Q`: stage by stage, the register subspaces are joined and the two
  continuations run side by side, each selected by its own component of the joint output;
  the paper's `⊕ⱼ L⁽ʲ⁾`, two summands at a time (`liftN` pads to a common level, the paper's
  `ℓ = maxⱼ ℓⱼ`).
* `MIPRE.CL.clDist L R`: the law of `(L x, R x)` for `x` uniform, as a real-valued probability
  mass function on pairs, the format of `MIPRE.Game`.

The paper's third closure property, downsizing to `𝔽₂` (`lem:cl-downsize`), needs the self-dual
bases of blueprint `lem:self-dual-basis` and is not here.
-/

namespace MIPRE.CL

universe u v

namespace CLFun

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}

/-! ## Concatenation (`lem:cl-concat`) -/

/-! ## Direct sums (`lem:cl-func-prod`) -/

/-- The remainders of a direct sum of presentations on disjoint `V_T`, `V_{T'}`. -/
theorem union_sdiff_union {S S' T T' : Finset ι} (hS : S ⊆ T) (hS' : S' ⊆ T')
    (hTT' : Disjoint T T') : (T ∪ T') \ (S ∪ S') = (T \ S) ∪ (T' \ S') := by
  ext i
  have hTS' : i ∈ T → i ∉ S' := fun hi hi' => Finset.disjoint_left.mp hTT' hi (hS' hi')
  have hT'S : i ∈ T' → i ∉ S := fun hi hi' => Finset.disjoint_left.mp hTT' (hS hi') hi
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
  tauto

/-! ## Evaluation -/

variable [Fintype ι]

end CLFun

/-! ## The paper's statements -/

section Statements

variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] [Fintype ι] {k ℓ : ℕ}

end Statements

/-! ## Conditionally linear distributions (`def:cl-dist`) -/

section Distribution

variable {F : Type u} [Fintype F] [DecidableEq F] {ι : Type v} [DecidableEq ι] [Fintype ι]

end Distribution

end MIPRE.CL


