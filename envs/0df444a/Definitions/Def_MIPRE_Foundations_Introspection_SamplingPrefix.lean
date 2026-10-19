-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
-- name    : MIPRE_Foundations_Introspection_SamplingPrefix
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:41.810825+00:00
-- url     : https://prove2.me/theorems/07596d50-63fc-4e59-b970-0a1b2fb67bad
-- title:
--   Definitions of SamplingPrefix: Reading prefixes from arbitrary claimed CL outputs The sampling test coarse-grains the entire answer alphabet, not…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.SamplingPrefix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reading prefixes from arbitrary claimed CL outputs. The sampling test coarse-grains the entire answer alphabet, not merely the image of the CL map. The prefix map therefore follows the claimed output's coordinate branches and does not apply the stage linear maps again.
--
--   **Definitions** (1): `MIPRE.CL.CLFun.outputPrefix` (Extract the first `k` register components from any claimed output.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `outputPrefix_cons`, `outputPrefix_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.SamplingPrefix` (`MIPRE/Foundations/Introspection/SamplingPrefix.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SamplingPrefix.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SamplingPrefix.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Theorems.Thm_MIPRE_CL_proj_add_proj_compl

/-! # Reading prefixes from arbitrary claimed CL outputs

The sampling test coarse-grains the entire answer alphabet, not merely the
image of the CL map. The prefix map therefore follows the claimed output's
coordinate branches and does not apply the stage linear maps again.
-/

namespace MIPRE.CL.CLFun

open Finset

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- Extract the first `k` register components from any claimed output. -/
def outputPrefix : {ℓ : ℕ} → CLFun F ι ℓ → ℕ → (ι → F) → (ι → F)
  | _, _, 0, _ => 0
  | _, .zero, _ + 1, _ => 0
  | _, .cons S _ next, k + 1, y =>
    proj S y + (next (proj S y)).outputPrefix k (proj Sᶜ y)

@[simp] theorem outputPrefix_zero (P : CLFun F ι ℓ) (y : ι → F) :
    P.outputPrefix 0 y = 0 := by cases P <;> rfl

@[simp] theorem outputPrefix_cons (S : Finset ι) (L : RegLinear F S)
    (next : (ι → F) → CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (cons S L next).outputPrefix (k + 1) y =
      proj S y + (next (proj S y)).outputPrefix k (proj Sᶜ y) := rfl

end MIPRE.CL.CLFun


