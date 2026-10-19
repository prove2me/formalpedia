-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
-- name    : MIPRE_Background_LIDT_PresentationQueries
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:36.910837+00:00
-- url     : https://prove2.me/theorems/20daa735-b0bb-4426-b0a7-398bf299cf79
-- title:
--   Definitions of PresentationQueries: The queries of the three-level presentation of the seeded test What a sampler program must compute for `Regs.pres`…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.PresentationQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The queries of the three-level presentation of the seeded test. What a sampler program must compute for `Regs.pres` (`MIPRE/Background/LIDT/Presentation`), level by level: its marginals (`eval_truncate_one`, `eval_truncate_two`, `eval_pres`), its stage maps read off a prefix (`mapOfPrefix_zero`, `mapOfPrefix_one`, `mapOfPrefix_two`) and its factor spaces (`factorOfPrefix_zero`, `factorOfPrefix_one`, `factorOfPrefix_two`); from the fourth level on there is nothing (`mapOfPrefix_three_le`, `factorOfPrefix_three_le`). The seed a stage map reads is the prefix's seed coordinate, and the diagonal…
--
--   **Definitions** (1): `MIPRE.LIDT.CL.Regs.ptMap` (The linear map of the point register applied at the third stage.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.PresentationQueries` (`MIPRE/Background/LIDT/PresentationQueries.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/PresentationQueries.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/PresentationQueries.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler

/-!
# The queries of the three-level presentation of the seeded test

What a sampler program must compute for `Regs.pres` (`MIPRE/Background/LIDT/Presentation`), level
by level: its marginals (`eval_truncate_one`, `eval_truncate_two`, `eval_pres`), its stage maps
read off a prefix (`mapOfPrefix_zero`, `mapOfPrefix_one`, `mapOfPrefix_two`) and its factor
spaces (`factorOfPrefix_zero`, `factorOfPrefix_one`, `factorOfPrefix_two`); from the fourth level
on there is nothing (`mapOfPrefix_three_le`, `factorOfPrefix_three_le`).

The seed a stage map reads is the prefix's seed coordinate, and the diagonal line's direction is
the prefix's direction register, already cut down by the selector.
-/

noncomputable section

namespace MIPRE.LIDT.CL.Regs

open Finset MIPRE.CL MIPRE.CL.CLFun

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

/-- The linear map of the point register applied at the third stage. -/
def ptMap : Ty → F → Point F n → (Point F n →ₗ[F] Point F n)
  | .point, _, _ => LinearMap.id
  | .aline, s, _ => MIPRE.CL.canonLin (Submodule.span F {Pi.single (S.χ s) 1})
  | .dline, _, v => MIPRE.CL.canonLin (Submodule.span F {v})

/-! ## The marginals -/

/-! ## The stage maps and factor spaces, read off a prefix -/

end MIPRE.LIDT.CL.Regs

end


