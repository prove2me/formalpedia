-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
-- name    : ReciprocityTheory_GroupCohomology_ShiftA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:59.955017+00:00
-- url     : https://prove2.me/theorems/dc12b635-17c6-4312-85cf-2c563c194fde
-- title:
--   Shift A
-- statement:
--   Definitions and structural lemmas for Shift A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ShiftA.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero


set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace KernelCokernelKilling
section Disc
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem contAction_of_disc {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V]
    [DiscreteTopology V] (rho : Representation R G V) (h : ∀ v, Continuous fun g => rho g v) :
    ContAction rho :=
  continuous_prod_of_discrete_right.2 h
theorem orbit_cont (B : TRep R G) (v : B.V) : Continuous fun g => B.rho g v :=
  B.cont.comp (f := fun g : G => (g, v)) (continuous_id.prodMk continuous_const)
def subRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := S
  ccs := ⟨fun _ => continuous_of_discreteTopology⟩
  rho := B.rho.subrepresentation S hS
  cont := contAction_of_disc _ fun v => (orbit_cont B v.1).subtype_mk _
instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (subRep B S hS).V := inferInstanceAs (DiscreteTopology S)
theorem disc_quot {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [DiscreteTopology V]
    (S : Submodule R V) : DiscreteTopology (V ⧸ S) :=
  discreteTopology_iff_forall_isOpen.2 fun _ =>
    (Submodule.isQuotientMap_mkQ S).isOpen_preimage.1 (isOpen_discrete _)
def quotRep (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V)
    (hS : ∀ g, S ≤ S.comap (B.rho g)) : TRep R G where
  V := B.V ⧸ S
  ccs := ⟨fun _ => by have := disc_quot S; exact continuous_of_discreteTopology⟩
  rho := B.rho.quotient S hS
  cont := by
    have := disc_quot S
    refine contAction_of_disc _ fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v => exact (continuous_of_discreteTopology (f := S.mkQ)).comp (orbit_cont B v)
instance (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) :
    DiscreteTopology (quotRep B S hS).V := disc_quot S
def subIncl (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) : Pair (subRep B S hS) B :=
  Pair.ofMap S.subtype continuous_of_discreteTopology fun _ _ => rfl
def quotMk (B : TRep R G) [DiscreteTopology B.V] (S : Submodule R B.V) (hS) : Pair B (quotRep B S hS) :=
  Pair.ofMap (M' := quotRep B S hS) S.mkQ continuous_of_discreteTopology fun _ _ => rfl
end Disc
section Triv
variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]
end Triv
section ShiftSec
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem disc_CM {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have he : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h; ext x; exact h (f x) ⟨x, rfl⟩ rfl
  rw [he]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete _).preimage f.continuous).isCompact (isOpen_discrete _)
variable [CompactSpace G]
end ShiftSec
section ShiftC
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]
instance disc_resBot : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V :=
  inferInstanceAs (DiscreteTopology M.V)
abbrev shC : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)
instance disc_shC : DiscreteTopology (shC M).V := by
  have := disc_CM (X := G) (Y := (M.resSub (⊥ : Subgroup G)).V)
  exact inferInstanceAs (DiscreteTopology (coindSub (⊥ : Subgroup G) (M.resSub ⊥)))
def shI : M.V →ₗ[R] (shC M).V where
  toFun m := ⟨⟨fun g => M.rho g m, orbit_cont M m⟩, fun x g => by
    have hx : (x : G) = 1 := Subgroup.mem_bot.1 x.2
    show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
    rw [hx, one_mul, map_one, Module.End.one_apply]⟩
  map_add' m m' := Subtype.ext (ContinuousMap.ext fun g => map_add (M.rho g) m m')
  map_smul' r m := Subtype.ext (ContinuousMap.ext fun g => map_smul (M.rho g) r m)
theorem shI_equiv (g : G) (m : M.V) : shI M (M.rho g m) = (shC M).rho g (shI M m) :=
  Subtype.ext (ContinuousMap.ext fun h => by
    show M.rho h (M.rho g m) = M.rho (h * g) m
    rw [map_mul]; rfl)
theorem shI_stable (g : G) : LinearMap.range (shI M) ≤ (LinearMap.range (shI M)).comap ((shC M).rho g) := by
  rintro v ⟨m, rfl⟩
  exact ⟨M.rho g m, shI_equiv M g m⟩
def shIP : Pair M (shC M) := Pair.ofMap (shI M) continuous_of_discreteTopology (shI_equiv M)
abbrev shQ : TRep R G := quotRep (shC M) (LinearMap.range (shI M)) (shI_stable M)
end ShiftC
end KernelCokernelKilling
end
end ReciprocityTheory.Coh


