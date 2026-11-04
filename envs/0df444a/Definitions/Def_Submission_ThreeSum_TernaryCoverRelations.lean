-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
-- name    : Submission_ThreeSum_TernaryCoverRelations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:41:08.884208+00:00
-- url     : https://prove2.me/theorems/9fe1407f-c672-491e-bb0e-54e7bf8ca47c
-- title:
--   Ternary Cover Relations
-- statement:
--   Definitions and structural lemmas for Ternary Cover Relations, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRelations.lean

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]
def digitVector {d : ℕ} (v : Fin d → Fin 3) : Fin d → K :=
  fun i => ((v i).val : K)
def spanCode (d : ℕ) (v : Fin d → Fin d → Fin 3) : Submodule K (Fin d → K) :=
  Submodule.span K (Set.range fun j => digitVector (v j))
def possibleSpans (K : Type*) [Field K] (d : ℕ) : Finset (Submodule K (Fin d → K)) := by
  classical
  exact (univ : Finset (Fin d → Fin d → Fin 3)).image (spanCode d)
def relationSpace {d : ℕ} (S : Submodule K (Fin d → K)) : Submodule K (Fin d → K) :=
  S.dualAnnihilator.comap (dotProductEquiv K (Fin d)).toLinearMap
def possibleRelations (K : Type*) [Field K] (d : ℕ) : Finset (Submodule K (Fin d → K)) := by
  classical
  exact (possibleSpans K d).image relationSpace
end ThreeSum.TernaryCoverRelations


