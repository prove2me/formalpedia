-- Prove2me | Definitions.Def_SNumbers_Examples_IdentityL2Linfty
-- name    : SNumbers_Examples_IdentityL2Linfty
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:37:51.02868+00:00
-- url     : https://prove2.me/theorems/091adb4b-7fa0-4588-acbf-58a06b0459d6
-- title:
--   Identity L2 Linfty
-- statement:
--   Definitions and structural lemmas for Identity L2 Linfty, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
namespace SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
section OrthonormalBasis
variable {N : ℕ} {ι : Type*} [Fintype ι] {M : Submodule 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜))}
end OrthonormalBasis
abbrev L2LinfProd (𝕜 : Type u) [RCLike 𝕜] : Type u :=
  PiLp 2 (fun _ : Fin 71 => 𝕜) × PiLp ∞ (fun _ : Fin 71 => 𝕜)
noncomputable def crossS : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜 :=
  (inr 𝕜 _ _).comp ((idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2).comp (fst 𝕜 _ _))
noncomputable def crossT : L2LinfProd 𝕜 →L[𝕜] L2LinfProd 𝕜 :=
  (inl 𝕜 _ _).comp ((idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞).comp ((9 : 𝕜)⁻¹ • snd 𝕜 _ _))
noncomputable def graphThree : PiLp 2 (fun _ : Fin 71 => 𝕜) →L[𝕜] L2LinfProd 𝕜 :=
  (ContinuousLinearMap.id 𝕜 _).prod ((3 : 𝕜) • idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2)
end SNumbers.L2Linf


