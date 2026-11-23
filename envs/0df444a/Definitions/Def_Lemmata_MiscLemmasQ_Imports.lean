-- Prove2me | Definitions.Def_Lemmata_MiscLemmasQ_Imports
-- name    : Lemmata_MiscLemmasQ_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:23.164132+00:00
-- url     : https://prove2.me/theorems/7f1edb84-698e-4a9e-8a7b-2bacf583d4c5
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasQ/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Bl.ThirdBlockLemmaB
noncomputable def goal1 :
  {S : Type} →   [inst : CommRing S] →     {A A' : Type} →       [inst_1 : CommRing A] →         [inst_2 : Algebra S A] →           [inst_3 : CommRing A'] → [inst_4 : Algebra S A'] → AlgHom S A A' → AlgHom S (DualNumber A) (DualNumber A') :=
  fun {S} _ {A A'} _ _ _ _ φ =>
    TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom S A' A').comp φ)
      (((TrivSqZeroExt.inrHom A' A').restrictScalars S).comp φ.toLinearMap)
      (fun x y => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inr_mul_inr])
      (fun r x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, map_mul])
      (fun r x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inr_mul_inl, op_smul_eq_mul, map_mul])
end Bl.ThirdBlockLemmaB


