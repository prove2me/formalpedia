-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:42.353527+00:00
-- url     : https://prove2.me/theorems/2acf725e-bb67-43a4-b1c9-7f4e7a97ee91
-- title:
--   Exists Unitary Char Of Open Subgroup And Hom
-- statement:
--   Definitions and structural lemmas for Exists Unitary Char Of Open Subgroup And Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUnitaryCharOfOpenSubgroupAndHom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace GlobalTheory
noncomputable def unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) : A →* Circle where
  toFun y := ⟨(a y : ℂ), by simpa [Submonoid.unitSphere] using ha y⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    exact (congrArg (fun u : ℂˣ => (u : ℂ)) (map_mul a x y)).trans (Units.val_mul _ _)
end GlobalTheory


