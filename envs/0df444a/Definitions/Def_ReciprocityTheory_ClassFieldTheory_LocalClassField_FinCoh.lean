-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:05.226402+00:00
-- url     : https://prove2.me/theorems/a9b3a5e5-4005-599c-911f-8b8c16f21086
-- title:
--   Fin Coh
-- statement:
--   Definitions and structural lemmas for Fin Coh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/FinCoh.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsLowExists
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
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
import Theorems.Thm_ReciprocityTheory_Coh_exists_isLow
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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh CategoryTheory
noncomputable section
universe u
variable {R : Type u} [CommRing R]
section Discrete
variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
theorem contAction_of_discrete [DiscreteTopology G] {V : Type u} [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul R V] (rho : Representation R G V)
    (h : ∀ g, Continuous (rho g)) : ReciprocityTheory.Gal.ContAction rho :=
  continuous_prod_of_discrete_left.2 h
def discRep [DiscreteTopology G] {V : Type u} [AddCommGroup V] [Module R V] (rho : Representation R G V) :
    TRep R G :=
  letI : TopologicalSpace V := ⊥
  haveI : DiscreteTopology V := ⟨rfl⟩
  { V := V
    rho := rho
    cont := contAction_of_discrete rho fun _ => continuous_of_discreteTopology }
def pairRepHom {M : TRep R G} {M' : TRep R G'} (P : Pair M M') :
    Rep.res P.φ (Rep.of M.rho) ⟶ Rep.of M'.rho :=
  Rep.ofHom ⟨P.u, fun g => LinearMap.ext fun m => P.equiv g m⟩
open groupCohomology
def zIncl (M : TRep R G) (n : ℕ) : M.coch.Z n →ₗ[R] ((Fin n → G) → M.V) where
  toFun z := z.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem zIncl_d (M : TRep R G) (n : ℕ) :
    ModuleCat.ofHom (zIncl M n) ≫ (inhomogeneousCochains (Rep.of M.rho)).d n (n + 1) = 0 := by
  rw [inhomogeneousCochains.d_def]
  ext z g
  exact congrFun (congrArg Subtype.val z.2) g
def toCyc (M : TRep R G) (n : ℕ) : ModuleCat.of R (M.coch.Z n) ⟶ cocycles (Rep.of M.rho) n :=
  (inhomogeneousCochains (Rep.of M.rho)).liftCycles (ModuleCat.ofHom (zIncl M n)) (n + 1) (by simp)
    (zIncl_d M n)
theorem i_toCyc (M : TRep R G) (n : ℕ) (z : M.coch.Z n) :
    iCocycles (Rep.of M.rho) n (toCyc M n z) = z.1.1 :=
  congrArg (fun φ => φ.hom z)
    ((inhomogeneousCochains (Rep.of M.rho)).liftCycles_i (ModuleCat.ofHom (zIncl M n)) (n + 1) (by simp)
      (zIncl_d M n))
theorem iCocycles_injective (A : Rep R G) (n : ℕ) : Function.Injective (iCocycles A n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance
theorem d_iCocycles (A : Rep R G) (n : ℕ) (c : cocycles A n) :
    inhomogeneousCochains.d A n (iCocycles A n c) = 0 := by
  have h := (inhomogeneousCochains A).iCycles_d n (n + 1)
  rw [inhomogeneousCochains.d_def] at h
  exact congrArg (fun φ => φ.hom c) h
theorem π_eq_zero_iff (A : Rep R G) (i n : ℕ) (hi : (ComplexShape.up ℕ).prev n = i) (c : cocycles A n) :
    π A n c = 0 ↔ ∃ y, toCocycles A i n y = c := by
  have ex : (ShortComplex.mk (toCocycles A i n) (π A n)
      ((inhomogeneousCochains A).toCycles_comp_homologyπ i n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ ((inhomogeneousCochains A).homologyIsCokernel i n hi)
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).1 ex c
  · rintro ⟨y, rfl⟩
    exact congrArg (fun φ => φ.hom y) ((inhomogeneousCochains A).toCycles_comp_homologyπ i n)
theorem i_toCocycles (A : Rep R G) (i n : ℕ) (y) :
    iCocycles A n (toCocycles A i n y) = (inhomogeneousCochains A).d i n y :=
  congrArg (fun φ => φ.hom y) ((inhomogeneousCochains A).toCycles_i i n)
variable [DiscreteTopology G] [DiscreteTopology G']
theorem toCyc_surjective (M : TRep R G) (n : ℕ) : Function.Surjective (toCyc M n) := by
  intro c
  refine ⟨⟨⟨iCocycles _ n c, continuous_of_discreteTopology⟩, Subtype.ext (d_iCocycles _ n c)⟩, ?_⟩
  exact iCocycles_injective _ n (i_toCyc M n _)
def toH (M : TRep R G) (n : ℕ) : M.coch.Z n →ₗ[R] groupCohomology (Rep.of M.rho) n :=
  (toCyc M n ≫ π (Rep.of M.rho) n).hom
theorem toH_surjective (M : TRep R G) (n : ℕ) : Function.Surjective (toH M n) := by
  intro x
  induction x using groupCohomology_induction_on with
  | h c =>
    obtain ⟨z, rfl⟩ := toCyc_surjective M n c
    exact ⟨z, rfl⟩
theorem ker_toH (M : TRep R G) (n : ℕ) :
    (M.coch.B n).comap (M.coch.Z n).subtype = LinearMap.ker (toH M n) := by
  ext z
  rw [LinearMap.mem_ker]
  show z.1 ∈ M.coch.B n ↔ π _ n (toCyc M n z) = 0
  cases n with
  | zero =>
    rw [π_eq_zero_iff _ 0 0 (by simp)]
    constructor
    · intro hz
      have hz' : z.1 = 0 := hz
      have : z = 0 := Subtype.ext hz'
      subst this
      exact ⟨0, by simp⟩
    · rintro ⟨y, hy⟩
      have h := i_toCocycles (Rep.of M.rho) 0 0 y
      rw [hy, i_toCyc, (inhomogeneousCochains (Rep.of M.rho)).shape 0 0 (by simp)] at h
      show z.1 = 0
      exact Subtype.ext h
  | succ n =>
    rw [π_eq_zero_iff _ n (n + 1) (by simp)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y.1, iCocycles_injective _ _ ?_⟩
      rw [i_toCocycles, i_toCyc, inhomogeneousCochains.d_def, ← hy]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨⟨y, continuous_of_discreteTopology⟩, Subtype.ext ?_⟩
      have h := i_toCocycles (Rep.of M.rho) n (n + 1) y
      rw [hy, i_toCyc, inhomogeneousCochains.d_def] at h
      exact h.symm
def finEquiv (M : TRep R G) (n : ℕ) : M.H n ≃ₗ[R] groupCohomology (Rep.of M.rho) n :=
  (Submodule.quotEquivOfEq _ _ (ker_toH M n)).trans ((toH M n).quotKerEquivOfSurjective (toH_surjective M n))
end Discrete
section Cyclic
def kerQuotEquiv {V : Type u} [AddCommGroup V] [Module R V] (p q : V →ₗ[R] V)
    (h : ∀ x, p x ∈ LinearMap.ker q) (W : Submodule R V) (hW : LinearMap.ker q = W) :
    (LinearMap.ker q ⧸ LinearMap.range (p.codRestrict (LinearMap.ker q) h)) ≃ₗ[R]
      (W ⧸ (LinearMap.range p).comap W.subtype) := by
  subst hW
  exact Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)
def scEquiv {V : Type u} [AddCommGroup V] [Module R V] (p q : V →ₗ[R] V)
    (h : ModuleCat.ofHom p ≫ ModuleCat.ofHom q = 0) (W : Submodule R V) (hW : LinearMap.ker q = W) :
    (ShortComplex.mk (ModuleCat.ofHom p) (ModuleCat.ofHom q) h).homology ≃ₗ[R]
      (W ⧸ (LinearMap.range p).comap W.subtype) :=
  (ShortComplex.moduleCatHomologyIso _).toLinearEquiv ≪≫ₗ
    kerQuotEquiv p q (fun x => LinearMap.mem_ker.2
      (congrArg (fun φ : ModuleCat.of R V ⟶ ModuleCat.of R V => φ.hom x) h)) W hW
variable {C : Type u} [CommGroup C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C]
  [DiscreteTopology C]
end Cyclic
section Low
variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
def lowEquiv0 (M : TRep R G) : M.H 0 ≃ₗ[R] _root_.Neutral.B1.H0 M.rho :=
  (exists_isLow M).choose
def lowEquiv1 (M : TRep R G) : M.H 1 ≃ₗ[R] _root_.Neutral.B1.H1 M.rho :=
  (exists_isLow M).choose_spec.choose
def lowEquiv2 (M : TRep R G) : M.H 2 ≃ₗ[R] _root_.Neutral.B1.H2 M.rho :=
  (exists_isLow M).choose_spec.choose_spec.choose
end Low
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


