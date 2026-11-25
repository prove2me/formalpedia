-- Prove2me | Definitions.Def_SNumbers_Kolmogorov
-- name    : SNumbers_Kolmogorov
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:48.654421+00:00
-- url     : https://prove2.me/theorems/140ced71-79f8-4aba-9257-37687eeca25f
-- title:
--   Kolmogorov
-- statement:
--   Definitions and structural lemmas for Kolmogorov, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
noncomputable def deviationFromSubspace (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) : ℝ :=
  ‖V.mkQL.comp S‖
def kolmogorovSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ V : Submodule 𝕜 Y,
      Module.rank 𝕜 V ≤ (n : Cardinal) ∧ r = deviationFromSubspace S V}
noncomputable def kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (kolmogorovSet S n)
variable [CompleteSpace 𝕜]
end SNumbers


