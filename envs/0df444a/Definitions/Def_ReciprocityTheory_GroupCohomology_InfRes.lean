-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
-- name    : ReciprocityTheory_GroupCohomology_InfRes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:38.856362+00:00
-- url     : https://prove2.me/theorems/9a58ba78-b08d-43e5-af74-e18fb5097a56
-- title:
--   Inf Res
-- statement:
--   Definitions and structural lemmas for Inf Res, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
instance instCCSInv (M : TRep R G) (N : Subgroup G) :
    ContinuousConstSMul R (Representation.invariants (M.rho.comp N.subtype)) :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩
abbrev invQ (M : TRep R G) (N : Subgroup G) [N.Normal] : TRep R (G ⧸ N) where
  V := Representation.invariants (M.rho.comp N.subtype)
  rho := Representation.quotientToInvariants M.rho N
  cont := by
    have hq : Topology.IsQuotientMap (fun p : G × Representation.invariants (M.rho.comp N.subtype) =>
        ((p.1 : G ⧸ N), p.2)) :=
      (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    refine Continuous.subtype_mk ?_ _
    exact M.cont.comp ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
def invP (M : TRep R G) (N : Subgroup G) [N.Normal] : Pair (invQ M N) M where
  φ := QuotientGroup.mk' N
  u := (Representation.invariants (M.rho.comp N.subtype)).subtype
  φ_cont := continuous_quot_mk
  u_cont := continuous_subtype_val
  equiv _ _ := rfl
end
end ReciprocityTheory.Coh.InflationRestrictionInvariants
namespace ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
abbrev e1 (a : G) : Fin 1 → G := fun _ => a
def const0 (M : TRep R G) (m : M.V) : M.coch.X 0 := ⟨fun _ => m, continuous_const⟩
end
end ReciprocityTheory.Coh.InflationRestrictionInvariants
namespace ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def conjPair (M : TRep R G) (s : G) : Pair M M where
  φ := { toFun := fun g => s⁻¹ * g * s, map_one' := by group, map_mul' := fun a b => by group }
  u := M.rho s
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := M.cont.comp (continuous_const.prodMk continuous_id)
  equiv g m := by
    show (M.rho s * M.rho (s⁻¹ * g * s)) m = (M.rho g * M.rho s) m
    rw [← map_mul, ← map_mul]
    congr 2
    group
end
end ReciprocityTheory.Coh.InflationRestrictionInvariants
namespace ReciprocityTheory.Coh
open InflationRestrictionInvariants
universe u
end ReciprocityTheory.Coh


