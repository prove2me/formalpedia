-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
-- name    : GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:21:56.51905+00:00
-- url     : https://prove2.me/theorems/cdfa197e-e5d4-53f2-a7ed-b77b3db6221a
-- title:
--   Completions Over Basis Repr
-- statement:
--   Definitions and structural lemmas for Completions Over Basis Repr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
namespace AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K) in

def finiteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
variable (L) in

def finiteRestrict (v : HeightOneSpectrum (𝓞 K)) : 𝔸[L] →+* CompletionsOver L v where
  toFun y w := y.2 w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
def completionsOverBasis (v : HeightOneSpectrum (𝓞 K)) :
    Basis ι (v.adicCompletion K) (CompletionsOver L v) :=
  (Algebra.TensorProduct.basis (v.adicCompletion K) b).map (tensorEquiv L v).toLinearEquiv
variable (K) in

def infiniteEval (v : InfinitePlace K) : 𝔸[K] →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
variable (L) in

def infiniteRestrict (v : InfinitePlace K) :
    𝔸[L] →+* GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v where
  toFun y w := y.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def piPlacesOverBasis (v : InfinitePlace K) :
    Basis ι v.Completion (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) :=
  (Algebra.TensorProduct.basis v.Completion b).map
    (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v).toLinearEquiv
end AdeleBaseChange
open AdeleBaseChange SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
end
end GroundTheory.Global


