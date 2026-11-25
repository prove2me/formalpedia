-- Prove2me | Definitions.Def_SNumbers_Examples_Identity
-- name    : SNumbers_Examples_Identity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:33:43.180108+00:00
-- url     : https://prove2.me/theorems/250c23d8-2089-5c3a-909e-cebdeb2052fa
-- title:
--   Identity
-- statement:
--   Definitions and structural lemmas for Identity, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
noncomputable def idEmbed (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (WithLp.ofLp x)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }
end SNumbers


