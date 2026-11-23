-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:49.441807+00:00
-- url     : https://prove2.me/theorems/633544f3-5490-40d9-9c5d-31962de4d11f
-- title:
--   Cyc Tate
-- statement:
--   Definitions and structural lemmas for Cyc Tate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


set_option autoImplicit false
namespace GroundTheory.Global
open GroundTheory.GroupCoh
section KerModRange
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
noncomputable def kerModRangeEquivOfSurjective {f g : A →+ A} (φ : f.ker →+ B)
    (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) :
    KerModRange f g ≃+ B :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext a
      rw [AddMonoidHom.mem_ker, hk, AddSubgroup.mem_addSubgroupOf])).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hs)
theorem addEquiv_symm_apply_comm {f : A →+ A} {f' : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (f a) = f' (e a)) (b : B) :
    e.symm.toAddMonoidHom (f' b) = f (e.symm.toAddMonoidHom b) := by
  apply e.injective
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, hf]
noncomputable def kerModRangeCongr {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) :
    KerModRange fA gA ≃+ KerModRange fB gB where
  toFun := KerModRange.map e.toAddMonoidHom hf hg
  invFun := KerModRange.map e.symm.toAddMonoidHom (addEquiv_symm_apply_comm e hf)
    (addEquiv_symm_apply_comm e hg)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (Subtype.ext (e.symm_apply_apply (a : A)))
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (Subtype.ext (e.apply_symm_apply (a : B)))
  map_add' := map_add _
noncomputable def kerModRangePiEquiv {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i))
    (hG : ∀ x i, G x i = g i (x i)) :
    KerModRange F G ≃+ ∀ i, KerModRange (f i) (g i) :=
  kerModRangeEquivOfSurjective
    (AddMonoidHom.pi fun i => (QuotientAddGroup.mk' _).comp
      (((Pi.evalAddMonoidHom A i).comp F.ker.subtype).codRestrict (f i).ker fun x => by
        simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, Pi.evalAddMonoidHom_apply,
          AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]))
    (by
      intro y
      choose z hz using fun i => QuotientAddGroup.mk_surjective (y i)
      refine ⟨⟨fun i => z i, AddMonoidHom.mem_ker.2 (funext fun i => ?_)⟩, funext fun i => ?_⟩
      · rw [hF, AddMonoidHom.mem_ker.1 (z i).2, Pi.zero_apply]
      · rw [← hz i]
        rfl)
    (by
      intro x
      constructor
      · intro h
        have h' : ∀ i, (x : ∀ i, A i) i ∈ (g i).range := fun i => by
          have := congrFun h i
          rw [Pi.zero_apply] at this
          exact (KerModRange.mk_eq_zero_iff _).1 this
        choose y hy using fun i => AddMonoidHom.mem_range.1 (h' i)
        exact AddMonoidHom.mem_range.2 ⟨y, funext fun i => by rw [hG, hy]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h
        funext i
        rw [Pi.zero_apply]
        refine (KerModRange.mk_eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨y i, ?_⟩)
        show g i (y i) = (x : ∀ i, A i) i
        rw [← hG, hy])
end KerModRange
section Defs
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
def cycSubOne (ρ : Representation k G V) (σ : G) : V →+ V :=
  (ρ σ - 1 : Module.End k V).toAddMonoidHom
theorem cycSubOne_apply (ρ : Representation k G V) (σ : G) (x : V) :
    cycSubOne ρ σ x = ρ σ x - x :=
  rfl
variable [Fintype G]
def cycNorm (ρ : Representation k G V) : V →+ V :=
  ρ.norm.toAddMonoidHom
theorem cycNorm_apply (ρ : Representation k G V) (x : V) : cycNorm ρ x = ∑ g : G, ρ g x := by
  simp [cycNorm, Representation.norm, LinearMap.sum_apply]
abbrev CycTateZero (ρ : Representation k G V) (σ : G) : Type _ :=
  KerModRange (cycSubOne ρ σ) (cycNorm ρ)
abbrev CycTateNegOne (ρ : Representation k G V) (σ : G) : Type _ :=
  KerModRange (cycNorm ρ) (cycSubOne ρ σ)
noncomputable def cycHerbrand (ρ : Representation k G V) (σ : G) : ℚ :=
  herbrandQuotient (cycSubOne ρ σ) (cycNorm ρ)
end Defs
section Congr
variable {k G V W : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
noncomputable def cycTateZeroCongr {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    CycTateZero ρ σ ≃+ CycTateZero ρ' σ :=
  kerModRangeCongr e (fun v => by simp [cycSubOne_apply, he])
    (fun v => by simp [cycNorm_apply, map_sum, he])
noncomputable def cycTateNegOneCongr {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    CycTateNegOne ρ σ ≃+ CycTateNegOne ρ' σ :=
  kerModRangeCongr e (fun v => by simp [cycNorm_apply, map_sum, he])
    (fun v => by simp [cycSubOne_apply, he])
end Congr
section Pi
variable {k G ι : Type*} [CommRing k] [Group G] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)]
def piRep (ρ : ∀ i, Representation k G (V i)) : Representation k G (∀ i, V i) where
  toFun g := LinearMap.pi fun i => (ρ i g).comp (LinearMap.proj i)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp
theorem cycSubOne_piRep_apply (ρ : ∀ i, Representation k G (V i)) (σ : G) (x : ∀ i, V i)
    (i : ι) : cycSubOne (piRep ρ) σ x i = cycSubOne (ρ i) σ (x i) :=
  rfl
variable [Fintype G]
theorem cycNorm_piRep_apply (ρ : ∀ i, Representation k G (V i)) (x : ∀ i, V i) (i : ι) :
    cycNorm (piRep ρ) x i = cycNorm (ρ i) (x i) := by
  rw [cycNorm_apply, cycNorm_apply, Finset.sum_apply]
  rfl
noncomputable def cycTateZeroPiEquiv (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    CycTateZero (piRep ρ) σ ≃+ ∀ i, CycTateZero (ρ i) σ :=
  kerModRangePiEquiv _ _ _ _ (cycSubOne_piRep_apply ρ σ) (cycNorm_piRep_apply ρ)
noncomputable def cycTateNegOnePiEquiv (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    CycTateNegOne (piRep ρ) σ ≃+ ∀ i, CycTateNegOne (ρ i) σ :=
  kerModRangePiEquiv _ _ _ _ (cycNorm_piRep_apply ρ) (cycSubOne_piRep_apply ρ σ)
end Pi
end GroundTheory.Global


