-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:29.117596+00:00
-- url     : https://prove2.me/theorems/ce111cfd-47d6-4d9a-af86-0cda6104af7b
-- title:
--   Exists Unique Comap Eq Vanishing Ideal
-- statement:
--   Definitions and structural lemmas for Exists Unique Comap Eq Vanishing Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
namespace GlobalTheory.GaloisDescent
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}
include H
noncomputable def twist (σ : L →ₐ[K] L) : Y ⟶ Y :=
  H.lift π (q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    rw [H.w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact σ.comp_algebraMap.symm)
end GlobalTheory.GaloisDescent


