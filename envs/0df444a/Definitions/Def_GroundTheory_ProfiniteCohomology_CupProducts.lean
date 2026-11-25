-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CupProducts
-- name    : GroundTheory_ProfiniteCohomology_CupProducts
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:13.12635+00:00
-- url     : https://prove2.me/theorems/041f227c-63b3-485e-905d-793158c9eb1a
-- title:
--   Cup Products
-- statement:
--   Definitions and structural lemmas for Cup Products, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CupProducts.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_Bridge
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_d_cupCochain
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isLocallyConstant_apply
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_nestedLinearEquiv_apply
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.nestedLinearEquiv_apply
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.ProfCoh
open CategoryTheory Limits MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
section Discrete
omit [TopologicalSpace G] in

theorem stabilizer_inf_le_stabilizer_tmul (A B : Rep.{u} k G) (a : A) (b : B) :
    stabilizer A.ρ a ⊓ stabilizer B.ρ b ≤
      stabilizer (A ⊗ B).ρ (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) := by
  intro g hg
  rw [Subgroup.mem_inf, mem_stabilizer, mem_stabilizer] at hg
  rw [mem_stabilizer, tensor_ρ_tmul, hg.1, hg.2]
variable [IsTopologicalGroup G]
instance isDiscreteRep_tensor (A B : Rep.{u} k G) [IsDiscreteRep A] [IsDiscreteRep B] :
    IsDiscreteRep (A ⊗ B) := by
  rw [isDiscreteRep_iff_smoothSubmodule_eq_top, Submodule.eq_top_iff']
  intro x
  refine TensorProduct.induction_on (R := k) (M := A) (N := B)
    (motive := fun x => x ∈ smoothSubmodule (A ⊗ B)) x (Submodule.zero_mem _) ?_ ?_
  · intro a b
    refine Subgroup.isOpen_mono (stabilizer_inf_le_stabilizer_tmul A B a b) ?_
    rw [Subgroup.coe_inf]
    exact (isOpen_stabilizer A a).inter (isOpen_stabilizer B b)
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy
end Discrete
variable [IsTopologicalGroup G]
section LocallyConstant
theorem isLocallyConstant_cupCochain {A B : Rep.{u} k G} [IsDiscreteRep B] {p q n : ℕ}
    (h : p + q = n) {f : (Fin p → G) → A} {g : (Fin q → G) → B} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) : IsLocallyConstant (cupCochain h f g) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpre : Continuous fun y : Fin n → G => fun i : Fin p => y ⟨i, by omega⟩ :=
    continuous_pi fun i => continuous_apply _
  have hsuf : Continuous fun y : Fin n → G => fun j : Fin q => y ⟨p + j, by omega⟩ :=
    continuous_pi fun j => continuous_apply _
  have hP : Continuous fun y : Fin n → G => Fin.partialProd y ⟨p, by omega⟩ :=
    (continuous_apply _).comp (continuous_partialProd (G := G) n)
  have e1 : ∀ᶠ y in nhds x, f (fun i : Fin p => y ⟨i, by omega⟩) =
      f (fun i : Fin p => x ⟨i, by omega⟩) :=
    hpre.continuousAt.eventually (hf.eventually_eq _)
  have e2 : ∀ᶠ y in nhds x, g (fun j : Fin q => y ⟨p + j, by omega⟩) =
      g (fun j : Fin q => x ⟨p + j, by omega⟩) :=
    hsuf.continuousAt.eventually (hg.eventually_eq _)
  have e3 : ∀ᶠ y in nhds x,
      B.ρ (Fin.partialProd y ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩) =
        B.ρ (Fin.partialProd x ⟨p, by omega⟩) (g fun j : Fin q => x ⟨p + j, by omega⟩) :=
    hP.continuousAt.eventually ((isLocallyConstant_apply B _).eventually_eq _)
  filter_upwards [e1, e2, e3] with y h1 h2 h3
  rw [cupCochain_apply, cupCochain_apply, h1, h2, h3]
variable {A B : Rep.{u} k G} {p q n : ℕ}
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cupCochain_zero_left (h : p + q = n) (g : (Fin q → G) → B) :
    cupCochain h (0 : (Fin p → G) → A) g = 0 :=
  (cupₗ h).map_zero₂ g
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cupCochain_zero_right (h : p + q = n) (f : (Fin p → G) → A) :
    cupCochain h f (0 : (Fin q → G) → B) = 0 :=
  (cupₗ h f).map_zero
section Elements
variable (A) in

def cochainOf [IsDiscreteRep A] {i : ℕ} (a : (cochainsComplex A).X i) : (Fin i → G) → A :=
  (a : locallyConstantCochains A i).1
variable (A) in

def mkCochain [IsDiscreteRep A] {i : ℕ} (c : (Fin i → G) → A) (hc : IsLocallyConstant c) :
    (cochainsComplex A).X i :=
  (⟨c, hc⟩ : locallyConstantCochains A i)
variable [IsDiscreteRep A]
@[simp]
theorem cochainOf_mkCochain {i : ℕ} (c : (Fin i → G) → A) (hc : IsLocallyConstant c) :
    cochainOf A (mkCochain A c hc) = c :=
  rfl
theorem isLocallyConstant_cochainOf {i : ℕ} (a : (cochainsComplex A).X i) :
    IsLocallyConstant (cochainOf A a) :=
  (a : locallyConstantCochains A i).2
theorem cochainOf_injective {i : ℕ} : Function.Injective (cochainOf A (i := i)) :=
  fun _ _ h => Subtype.ext h
@[simp]
theorem cochainOf_add {i : ℕ} (a b : (cochainsComplex A).X i) :
    cochainOf A (a + b) = cochainOf A a + cochainOf A b :=
  rfl
@[simp]
theorem cochainOf_smul {i : ℕ} (c : k) (a : (cochainsComplex A).X i) :
    cochainOf A (c • a) = c • cochainOf A a :=
  rfl
@[simp]
theorem cochainOf_zero {i : ℕ} : cochainOf A (0 : (cochainsComplex A).X i) = 0 :=
  rfl
theorem cochainOf_d {i : ℕ} (a : (cochainsComplex A).X i) :
    cochainOf A ((cochainsComplex A).d i (i + 1) a) =
      (inhomogeneousCochains.d A i).hom (cochainOf A a) := by
  rw [cochainsComplex_d]
  rfl
end Elements
variable [IsDiscreteRep A] [IsDiscreteRep B]
def cupLocallyConstant (h : p + q = n) :
    (cochainsComplex A).X p →ₗ[k] (cochainsComplex B).X q →ₗ[k] (cochainsComplex (A ⊗ B)).X n :=
  LinearMap.mk₂ k (fun f g => mkCochain (A ⊗ B) (cupCochain h (cochainOf A f) (cochainOf B g))
      (isLocallyConstant_cupCochain h (isLocallyConstant_cochainOf f)
        (isLocallyConstant_cochainOf g)))
    (fun f f' g => cochainOf_injective ((cupₗ h).map_add₂ (cochainOf A f) (cochainOf A f') (cochainOf B g)))
    (fun c f g => cochainOf_injective ((cupₗ h).map_smul₂ c (cochainOf A f) (cochainOf B g)))
    (fun f g g' => cochainOf_injective ((cupₗ h (cochainOf A f)).map_add (cochainOf B g) (cochainOf B g')))
    (fun c f g => cochainOf_injective ((cupₗ h (cochainOf A f)).map_smul c (cochainOf B g)))
@[simp]
theorem cochainOf_cupLocallyConstant (h : p + q = n) (f : (cochainsComplex A).X p)
    (g : (cochainsComplex B).X q) :
    cochainOf (A ⊗ B) (cupLocallyConstant h f g) = cupCochain h (cochainOf A f) (cochainOf B g) :=
  rfl
end LocallyConstant
section Cocycles
variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}
variable (A p) in

def cocycleι : cocycles A p →ₗ[k] (cochainsComplex A).X p :=
  ((cochainsComplex A).iCycles p).hom
theorem cocycleι_injective : Function.Injective (cocycleι A p) :=
  (ModuleCat.mono_iff_injective ((cochainsComplex A).iCycles p)).1 inferInstance
theorem d_cocycleι (x : cocycles A p) :
    (inhomogeneousCochains.d A p).hom (cochainOf A (cocycleι A p x)) = 0 := by
  rw [← cochainOf_d]
  have h := congrArg (fun φ => φ.hom x) ((cochainsComplex A).iCycles_d p (p + 1))
  exact congrArg (cochainOf A) h
theorem cochainOf_cocycleι_toCycles {i : ℕ} (a : (cochainsComplex A).X i) :
    cochainOf A (cocycleι A (i + 1) ((cochainsComplex A).toCycles i (i + 1) a)) =
      (inhomogeneousCochains.d A i).hom (cochainOf A a) := by
  rw [← cochainOf_d]
  exact congrArg (fun φ => cochainOf A (φ.hom a)) ((cochainsComplex A).toCycles_i i (i + 1))
theorem isCocycle_cupCochain (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom
      (cupCochain h (cochainOf A (cocycleι A p x)) (cochainOf B (cocycleι B q y))) = 0 := by
  rw [d_cupCochain, d_cocycleι, d_cocycleι, cupCochain_zero_left, cupCochain_zero_right,
    smul_zero, add_zero]
def cupCocyclesAlt (h : p + q = n) (x : cocycles A p) (y : cocycles B q) : cocycles (A ⊗ B) n :=
  (cochainsComplex (A ⊗ B)).cyclesMk
    (cupLocallyConstant h (cocycleι A p x) (cocycleι B q y)) (n + 1) (by simp) (by
      apply cochainOf_injective (A := A ⊗ B)
      exact (cochainOf_d (A := A ⊗ B) _).trans (isCocycle_cupCochain h x y))
theorem cocycle_inclusion_cupCocycles (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cocycleι (A ⊗ B) n (cupCocyclesAlt h x y) =
      cupLocallyConstant h (cocycleι A p x) (cocycleι B q y) :=
  (cochainsComplex (A ⊗ B)).i_cyclesMk _ _ _ _
def cupCocycles (h : p + q = n) :
    cocycles A p →ₗ[k] cocycles B q →ₗ[k] cocycles (A ⊗ B) n :=
  LinearMap.mk₂ k (cupCocyclesAlt h)
    (fun x x' y => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
    (fun c x y => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
    (fun x y y' => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
    (fun c x y => cocycleι_injective (by simp [cocycle_inclusion_cupCocycles]))
@[simp]
theorem cocycleι_cupCocycles (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cocycleι (A ⊗ B) n (cupCocycles h x y) =
      cupLocallyConstant h (cocycleι A p x) (cocycleι B q y) :=
  cocycle_inclusion_cupCocycles h x y
theorem cupCocycles_toCycles_left (h : p + q = n) {i m : ℕ} (hi : i + 1 = p) (hm : i + q = m)
    (hmn : m + 1 = n) (a : (cochainsComplex A).X i) (y : cocycles B q) :
    cupCocycles h ((cochainsComplex A).toCycles i p a) y =
      (cochainsComplex (A ⊗ B)).toCycles m n (cupLocallyConstant hm a (cocycleι B q y)) := by
  subst hi hm hmn
  apply cocycleι_injective
  apply cochainOf_injective
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cocycleι_toCycles,
    cochainOf_cocycleι_toCycles, cochainOf_cupLocallyConstant, d_cupCochain, d_cocycleι,
    cupCochain_zero_right, smul_zero, add_zero]
theorem cupCocycles_toCycles_right (h : p + q = n) {j m : ℕ} (hj : j + 1 = q) (hm : p + j = m)
    (hmn : m + 1 = n) (x : cocycles A p) (b : (cochainsComplex B).X j) :
    cupCocycles h x ((cochainsComplex B).toCycles j q b) =
      (-1 : k) ^ p • (cochainsComplex (A ⊗ B)).toCycles m n
        (cupLocallyConstant hm (cocycleι A p x) b) := by
  subst hj hm hmn
  apply cocycleι_injective
  apply cochainOf_injective
  rw [map_smul, cochainOf_smul, cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_toCycles, cochainOf_cocycleι_toCycles, cochainOf_cupLocallyConstant,
    d_cupCochain, d_cocycleι, cupCochain_zero_left, zero_add, smul_smul, ← mul_pow, neg_one_mul,
    neg_neg, one_pow, one_smul]
end Cocycles
section Cohomology
variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}
theorem cohomologyπ_surjective (A : Rep.{u} k G) [IsDiscreteRep A] (p : ℕ) :
    Function.Surjective (cohomologyπ A p) :=
  (ModuleCat.epi_iff_surjective ((cochainsComplex A).homologyπ p)).1 inferInstance
theorem cohomologyπ_toCycles (A : Rep.{u} k G) [IsDiscreteRep A] (i p : ℕ)
    (a : (cochainsComplex A).X i) :
    cohomologyπ A p ((cochainsComplex A).toCycles i p a) = 0 :=
  congrArg (fun φ => φ.hom a) ((cochainsComplex A).toCycles_comp_homologyπ i p)
theorem cohomology_linearMap_ext {M : Type*} [AddCommGroup M] [Module k M]
    {f g : cohomology A p →ₗ[k] M} (hfg : ∀ x, f (cohomologyπ A p x) = g (cohomologyπ A p x)) :
    f = g := by
  ext z
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A p z
  exact hfg x
def cocyclesHom {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M) :
    (cochainsComplex A).cycles p ⟶ ModuleCat.of k M :=
  ModuleCat.ofHom L
theorem toCycles_cocyclesHom {M : Type u} [AddCommGroup M] [Module k M]
    (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochainsComplex A).toCycles i p a) = 0) :
    (cochainsComplex A).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cocyclesHom L = 0 := by
  by_cases hr : (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev p) p
  · ext a
    exact hL _ hr a
  · rw [(cochainsComplex A).toCycles_eq_zero hr]
    exact zero_comp
def descCohomologyHom {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochainsComplex A).toCycles i p a) = 0) :
    cohomology A p ⟶ ModuleCat.of k M :=
  ((cochainsComplex A).homologyIsCokernel _ p rfl).desc
    (CokernelCofork.ofπ (cocyclesHom L) (toCycles_cocyclesHom L hL))
theorem π_descCohomologyHom {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochainsComplex A).toCycles i p a) = 0) :
    cohomologyπ A p ≫ descCohomologyHom L hL = cocyclesHom L :=
  Cofork.IsColimit.π_desc ((cochainsComplex A).homologyIsCokernel _ p rfl)
def descCohomology {M : Type u} [AddCommGroup M] [Module k M] (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochainsComplex A).toCycles i p a) = 0) :
    cohomology A p →ₗ[k] M :=
  (descCohomologyHom L hL).hom
@[simp]
theorem descCohomology_cohomologyπ {M : Type u} [AddCommGroup M] [Module k M]
    (L : cocycles A p →ₗ[k] M)
    (hL : ∀ i, i + 1 = p → ∀ a, L ((cochainsComplex A).toCycles i p a) = 0) (x : cocycles A p) :
    descCohomology L hL (cohomologyπ A p x) = L x :=
  ConcreteCategory.congr_hom (π_descCohomologyHom L hL) x
def cupCocyclesπ (h : p + q = n) :
    cocycles A p →ₗ[k] cocycles B q →ₗ[k] cohomology (A ⊗ B) n :=
  (cupCocycles h).compr₂ (cohomologyπ (A ⊗ B) n).hom
theorem cupCocyclesπ_apply (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cupCocyclesπ h x y = cohomologyπ (A ⊗ B) n (cupCocycles h x y) :=
  rfl
theorem cupCocyclesπ_toCycles_left (h : p + q = n) (i : ℕ) (hi : i + 1 = p)
    (a : (cochainsComplex A).X i) (y : cocycles B q) :
    cupCocyclesπ h ((cochainsComplex A).toCycles i p a) y = 0 := by
  rw [cupCocyclesπ_apply, cupCocycles_toCycles_left h hi rfl (by omega), cohomologyπ_toCycles]
theorem cupCocyclesπ_toCycles_right (h : p + q = n) (x : cocycles A p) (j : ℕ) (hj : j + 1 = q)
    (b : (cochainsComplex B).X j) :
    cupCocyclesπ h x ((cochainsComplex B).toCycles j q b) = 0 := by
  rw [cupCocyclesπ_apply, cupCocycles_toCycles_right h hj rfl (by omega), map_smul,
    cohomologyπ_toCycles, smul_zero]
def cupProductCocycleClass (h : p + q = n) : cohomology B q →ₗ[k] cocycles A p →ₗ[k] cohomology (A ⊗ B) n :=
  descCohomology (cupCocyclesπ h).flip fun j hj b => by
    ext x
    exact cupCocyclesπ_toCycles_right h x j hj b
theorem cup_cohomology_class (h : p + q = n) (x : cocycles A p) (y : cocycles B q) :
    cupProductCocycleClass h (cohomologyπ B q y) x = cupCocyclesπ h x y := by
  rw [cupProductCocycleClass, descCohomology_cohomologyπ]
  rfl
def cup (h : p + q = n) : cohomology A p →ₗ[k] cohomology B q →ₗ[k] cohomology (A ⊗ B) n :=
  descCohomology (cupProductCocycleClass h).flip fun i hi a => by
    apply cohomology_linearMap_ext
    intro y
    rw [LinearMap.flip_apply, cup_cohomology_class, cupCocyclesπ_toCycles_left h i hi]
    rfl
end Cohomology
end GroundTheory.ProfCoh


