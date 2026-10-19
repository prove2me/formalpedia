-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
-- name    : MIPRE_Background_LIDT_Adapter_Value
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:06.255527+00:00
-- url     : https://prove2.me/theorems/a44ace6e-4d8e-4514-a1a9-a120f2cd62cb
-- title:
--   Definitions of Value: The value of a strategy for the seeded test, sample by sample The seeded test's question distribution is the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Adapter.Value` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a strategy for the seeded test, sample by sample. The seeded test's question distribution is the push-forward of the uniform distribution on `Sample F m` under the two typed question maps. A strategy's failure probability is therefore the average over samples of the conditional failure at the two questions the sample generates (`one_sub_povmValue_clGame`), and that average splits into the nine ordered type pairs (`sum_sample_eq`). The padded strategy of the Pauli basis test is analysed one type pair at a time, which is what these two identities are for. The file also records two…
--
--   **Definitions** (1): `MIPRE.LIDT.CL.sampleEquiv` (The verifier's random choices, split into the two types and the ambient triple.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Adapter.Value` (`MIPRE/Background/LIDT/Adapter/Value.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 13 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Value.lean; blueprint lem:qld-global-setup

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Value.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Theorems.Thm_MIPRE_LIDT_Adapter_canonLin_bot
import Theorems.Thm_MIPRE_LIDT_Adapter_rep_eq

/-!
# The value of a strategy for the seeded test, sample by sample

The seeded test's question distribution is the push-forward of the uniform distribution on
`Sample F m` under the two typed question maps. A strategy's failure probability is therefore the
average over samples of the conditional failure at the two questions the sample generates
(`one_sub_povmValue_clGame`), and that average splits into the nine ordered type pairs
(`sum_sample_eq`). The padded strategy of the Pauli basis test is analysed one type pair at a
time, which is what these two identities are for.

The file also records two facts about a seeded line question that the analysis reads off the
geometry: a point lies on its own line at the parameter `lineParam` computes, whether or not the
direction vanishes (`rep_add_lineParam_smul`), and a degenerate diagonal direction is rare
(`sum_indicator_zeroBelow_eq_zero_le`).
-/

namespace MIPRE.LIDT.CL

open Finset MIPRE

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}

/-! ## The sample space -/

/-- The verifier's random choices, split into the two types and the ambient triple. -/
def sampleEquiv (F : Type*) (m : ℕ) :
    Sample F m ≃ (Ty × Ty) × (Point F m × F × Point F m) where
  toFun sm := ((sm.tyA, sm.tyB), (sm.u, sm.s, sm.v))
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## A point lies on its own line -/

/-! ## Degenerate diagonal directions are rare -/

/-! ## The failure probability, sample by sample -/

variable [NeZero m] (hm : m ∣ Fintype.card F)

end MIPRE.LIDT.CL


