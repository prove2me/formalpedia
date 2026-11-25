-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
-- name    : GroundTheory_TateCohomology_TateSubgroupMaps
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:04:08.537589+00:00
-- url     : https://prove2.me/theorems/cca6484f-1486-49e4-a0f8-293aceeb2743
-- title:
--   Tate Subgroup Maps
-- statement:
--   Definitions and structural lemmas for Tate Subgroup Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
section Delta
variable [Fintype G]
def IsTateDelta {U V : Subgroup G} [Fintype U] [Fintype V]
    (α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n) : Prop :=
  ∀ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ),
    TateCohomology.δ (shortExact_map_resFunctor U hX) n ≫ (α (n + 1)).app X.X₁ =
      (α n).app X.X₃ ≫ TateCohomology.δ (shortExact_map_resFunctor V hX) n
namespace IsTateDelta
variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]
omit [Fintype G] in

theorem id : IsTateDelta (fun n => 𝟙 (resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n)) :=
  fun _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
end IsTateDelta
end Delta
section LE
variable {U W : Subgroup G} (h : W ≤ U)
@[simps]
def resLENatTrans :
    resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype ⋙
        resFunctor ((Subgroup.subgroupOfEquivOfLe h).symm : W →* W.subgroupOf U) ⟶
      resFunctor (k := k) W.subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl
@[simps]
def coresLENatTrans :
    resFunctor W.subtype ⋙ resFunctor (Subgroup.subgroupOfEquivOfLe h : W.subgroupOf U →* W) ⟶
      resFunctor (k := k) U.subtype ⋙ resFunctor (W.subgroupOf U).subtype where
  app _ := Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  naturality _ _ _ := rfl
variable [Fintype U] [Fintype W]
@[instance_reducible]
noncomputable def fintypeSubgroupOf : Fintype (W.subgroupOf U) :=
  Fintype.ofEquiv W (Subgroup.subgroupOfEquivOfLe h).symm.toEquiv
noncomputable def tateResLE (n : ℤ) :
    resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n :=
  letI := fintypeSubgroupOf h
  Functor.whiskerLeft (resFunctor U.subtype) (tateRes (W.subgroupOf U) n) ≫
    Functor.whiskerLeft (resFunctor U.subtype ⋙ resFunctor (W.subgroupOf U).subtype)
      (tateTransport (Subgroup.subgroupOfEquivOfLe h).symm n) ≫
    Functor.whiskerRight (resLENatTrans h) (tateCohomologyFunctor n)
noncomputable def tateCoresLE (n : ℤ) :
    resFunctor W.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor U.subtype ⋙ tateCohomologyFunctor n :=
  letI := fintypeSubgroupOf h
  Functor.whiskerLeft (resFunctor W.subtype) (tateTransport (Subgroup.subgroupOfEquivOfLe h) n) ≫
    Functor.whiskerRight (coresLENatTrans h) (tateCohomologyFunctor n) ≫
    Functor.whiskerLeft (resFunctor U.subtype) (tateCores (W.subgroupOf U) n)
omit [Fintype U] [Fintype W] in

def invariantsLE {A : Rep.{u} k G} (y : (res U.subtype A).ρ.invariants) :
    (res W.subtype A).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨w, h w.2⟩⟩
omit [Fintype U] [Fintype W] in
variable (U) in

def invariantsSubgroupOf {A : Rep.{u} k G} (y : (res W.subtype A).ρ.invariants) :
    (res (W.subgroupOf U).subtype (res U.subtype A)).ρ.invariants :=
  ⟨y, fun w => y.2 ⟨(w : U), w.2⟩⟩
end LE
end GroundTheory.GroupCoh


