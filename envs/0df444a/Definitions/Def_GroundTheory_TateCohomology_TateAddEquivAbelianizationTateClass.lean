-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
-- name    : GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:36.167111+00:00
-- url     : https://prove2.me/theorems/75666e08-b95e-4c1f-9381-a9a31a48305f
-- title:
--   Tate Add Equiv Abelianization Tate Class
-- statement:
--   Definitions and structural lemmas for Tate Add Equiv Abelianization Tate Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateAddEquivAbelianizationTateClass.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory groupHomology TensorProduct Finsupp
universe u
section General
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) [A.IsTrivial]
noncomputable def h1Class (g : G) (a : A) : H1 A :=
  H1π A ((cycles₁IsoOfIsTrivial A).inv (single g a))
noncomputable def h1AddEquivAbelianization (e : A ≃+ ℤ) :
    H1 A ≃+ Additive (Abelianization G) :=
  (H1AddEquivOfIsTrivial A).trans <|
    ((TensorProduct.congr (LinearEquiv.refl ℤ (Additive (Abelianization G)))
      e.toIntLinearEquiv).trans (TensorProduct.rid ℤ (Additive (Abelianization G)))).toAddEquiv
end General
section Tate
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
noncomputable def tateNegTwoIsoH1 : tateCohomology A (-2) ≅ H1 A :=
  (TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A
variable [A.IsTrivial]
noncomputable def tateClass (g : G) (a : A) : tateCohomology A (-2) :=
  (tateNegTwoIsoH1 A).inv (h1Class A g a)
noncomputable def tateAddEquivAbelianization (e : A ≃+ ℤ) :
    tateCohomology A (-2) ≃+ Additive (Abelianization G) :=
  (tateNegTwoIsoH1 A).toLinearEquiv.toAddEquiv.trans (h1AddEquivAbelianization A e)
end Tate
section Int
variable (G : Type) [Group G]
noncomputable def h1IntAddEquiv : H1 (Rep.trivial ℤ G ℤ) ≃+ Additive (Abelianization G) :=
  h1AddEquivAbelianization (Rep.trivial ℤ G ℤ) (AddEquiv.refl ℤ)
noncomputable def h1IntIso :
    H1 (Rep.trivial ℤ G ℤ) ≅ ModuleCat.of ℤ (Additive (Abelianization G)) :=
  (h1IntAddEquiv G).toIntLinearEquiv.toModuleIso
variable [Fintype G]
noncomputable def tateIntAddEquiv :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G) :=
  tateAddEquivAbelianization (Rep.trivial ℤ G ℤ) (AddEquiv.refl ℤ)
noncomputable def tateIntIso :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≅ ModuleCat.of ℤ (Additive (Abelianization G)) :=
  (tateIntAddEquiv G).toIntLinearEquiv.toModuleIso
end Int
section ULiftInt
variable (G : Type u) [Group G]
noncomputable def h1ULiftIntAddEquiv :
    H1 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) ≃+ Additive (Abelianization G) :=
  h1AddEquivAbelianization (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) AddEquiv.ulift
variable [Fintype G]
noncomputable def tateULiftIntAddEquiv :
    tateCohomology (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) (-2) ≃+
      Additive (Abelianization G) :=
  tateAddEquivAbelianization (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) AddEquiv.ulift
end ULiftInt
end GroundTheory.GroupCoh


