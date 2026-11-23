-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
-- name    : ReciprocityTheory_GroupCohomology_InfIsoA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:36.3138+00:00
-- url     : https://prove2.me/theorems/9bfe4576-222b-4fa6-92f1-01528d90012f
-- title:
--   Inf Iso A
-- statement:
--   Definitions and structural lemmas for Inf Iso A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
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
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
namespace InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def stabN (A : TRep R G) (N : Subgroup G) (a : A.V) : Subgroup N where
  carrier := {n | A.rho (n : G) a = a}
  mul_mem' {x y} hx hy := by
    show A.rho ((x * y : N) : G) a = a
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, show A.rho (y : G) a = a from hy]
    exact hx
  one_mem' := by show A.rho ((1 : N) : G) a = a; simp
  inv_mem' {x} hx := by
    show A.rho ((x⁻¹ : N) : G) a = a
    have hx' : A.rho (x : G) a = a := hx
    conv_lhs => rw [← hx']
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one,
      Module.End.one_apply]
theorem cmap_disc (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [DiscreteTopology Y] : DiscreteTopology C(X, Y) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun f => ?_
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) = ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro rfl y _ x hx; exact hx
    · intro h
      ext x
      exact h (f x) ⟨x, rfl⟩ (show x ∈ f ⁻¹' {f x} from rfl)
  rw [hset]
  exact hfin.isOpen_biInter fun y _ => ContinuousMap.isOpen_setOfPred_mapsTo
    ((isClosed_discrete {y}).preimage f.continuous).isCompact (isOpen_discrete _)
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
abbrev CG (M : TRep R G) : TRep R G := coindRep (⊥ : Subgroup G) (M.resSub ⊥)
instance CG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (CG M).V := by
  have : DiscreteTopology (M.resSub (⊥ : Subgroup G)).V := ‹DiscreteTopology M.V›
  have := cmap_disc G (M.resSub (⊥ : Subgroup G)).V
  exact (IsEmbedding.subtypeVal (p := fun f => f ∈ coindSub (⊥ : Subgroup G) (M.resSub ⊥))).discreteTopology
def iCG (M : TRep R G) : M.V →ₗ[R] (CG M).V where
  toFun m := ⟨⟨fun x => M.rho x m, M.cont.comp (f := fun x : G => (x, m)) (continuous_id.prodMk continuous_const)⟩,
    fun x g => by
      show M.rho ((x : G) * g) m = M.rho (x : G) (M.rho g m)
      rw [map_mul, Module.End.mul_apply]⟩
  map_add' a b := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (a + b) = M.rho x a + M.rho x b; simp)
  map_smul' r a := Subtype.ext (ContinuousMap.ext fun x => by
    show M.rho x (r • a) = r • M.rho x a; simp)
@[simp] theorem iCG_apply (M : TRep R G) (m : M.V) (x : G) : (iCG M m).1 x = M.rho x m := rfl
theorem iCG_equiv (M : TRep R G) (g : G) (m : M.V) : iCG M (M.rho g m) = (CG M).rho g (iCG M m) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  show M.rho x (M.rho g m) = M.rho (x * g) m
  rw [map_mul, Module.End.mul_apply]
def iP (M : TRep R G) [DiscreteTopology M.V] : Pair M (CG M) :=
  Pair.ofMap (iCG M) continuous_of_discreteTopology (iCG_equiv M)
def QG (M : TRep R G) : TRep R G where
  V := (CG M).V ⧸ LinearMap.range (iCG M)
  rho := (CG M).rho.quotient (LinearMap.range (iCG M)) (fun g x hx => by
    obtain ⟨m, rfl⟩ := hx
    exact ⟨M.rho g m, iCG_equiv M g m⟩)
  cont := by
    have hq : IsQuotientMap (fun p : G × (CG M).V => (p.1, (LinearMap.range (iCG M)).mkQ p.2)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ _)).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    exact (Submodule.isQuotientMap_mkQ _).continuous.comp (CG M).cont
instance QG_disc [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V] : DiscreteTopology (QG M).V := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x => ?_
  exact (Submodule.isQuotientMap_mkQ (LinearMap.range (iCG M))).isOpen_preimage.1 (isOpen_discrete _)
def pLin (M : TRep R G) : (CG M).V →ₗ[R] (QG M).V := (LinearMap.range (iCG M)).mkQ
theorem pLin_cont (M : TRep R G) : Continuous (pLin M) := (Submodule.isQuotientMap_mkQ _).continuous
theorem pLin_equiv (M : TRep R G) (g : G) (c : (CG M).V) : pLin M ((CG M).rho g c) = (QG M).rho g (pLin M c) := rfl
def pP (M : TRep R G) : Pair (CG M) (QG M) := Pair.ofMap (pLin M) (pLin_cont M) (pLin_equiv M)
end InflationIsomorphism
end
end ReciprocityTheory.Coh


