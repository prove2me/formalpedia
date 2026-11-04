-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
-- name    : Submission_ThreeSum_TernaryPairedPotential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:59.454194+00:00
-- url     : https://prove2.me/theorems/a0154051-e049-44ee-90da-aeb86251424e
-- title:
--   Ternary Paired Potential
-- statement:
--   Definitions and structural lemmas for Ternary Paired Potential, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]
def minorWeight {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) : ℕ :=
  ∑ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs ^ 2
def pairedMatrix {m Λ : ℕ} (L R : Fin m → Fin Λ → ℤ) :
    Matrix (Fin m ⊕ Fin m) (Fin Λ) ℤ := Sum.elim L R
def rowWeight {ι : Type*} [Fintype ι] {Λ : ℕ} (A : ι → Fin Λ → ℤ) : ℕ :=
  minorWeight (fun i => A ((Fintype.equivFin ι).symm i))
end ThreeSum.TernaryPairedPotential


