-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_Bridge
-- name    : GroundTheory_ProfiniteCohomology_Bridge
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:09.768062+00:00
-- url     : https://prove2.me/theorems/5d4d5795-d1ec-59c0-8bd2-dc3d6c3f3aab
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Bridge.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeNested
import Theorems.Thm_GroundTheory_ProfCoh_dLocallyConstant_hom_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isLocallyConstant_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_nestedHomeomorph_d_apply
import Theorems.Thm_GroundTheory_ProfCoh_nestedLinearEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_nestedHomeomorph___apply_068446922cac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.nestedLinearEquiv_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory TopRep ContRepresentation
universe u
section General
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
theorem continuous_partialProd (n : ℕ) :
    Continuous fun g : Fin n → G => Fin.partialProd g := by
  refine continuous_pi fun i => ?_
  induction i using Fin.induction with
  | zero => simpa using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (continuous_apply i)
variable {k : Type u} [CommRing k]
theorem isLocallyConstant_ρ_apply {Y : Type*} [TopologicalSpace Y] (A : Rep.{u} k G)
    [IsDiscreteRep A] {p : Y → G} (hp : Continuous p) {ψ : Y → A} (hψ : IsLocallyConstant ψ) :
    IsLocallyConstant fun y => A.ρ (p y) (ψ y) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have h1 : ∀ᶠ z in nhds y, ψ z = ψ y := hψ.eventually_eq y
  have h2 : ∀ᶠ z in nhds y, A.ρ (p z) (ψ y) = A.ρ (p y) (ψ y) :=
    hp.continuousAt.eventually ((isLocallyConstant_apply A (ψ y)).eventually_eq (p y))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]
end General
variable {k G : Type u} [CommRing k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
section Invariant
variable (X : TopRep.{u} k G)
theorem nestedHomeomorph_mul_apply_of_mem_invariants {m : ℕ} {a : resolutionX X m}
    (ha : a ∈ (resolutionX X m).ρ.invariants) (g : G) (x : Fin m → G) :
    nestedHomeomorph X m a (fun i => g * x i) = X.ρ g (nestedHomeomorph X m a x) := by
  have h := nestedHomeomorph_ρ_apply X m g a (fun i => g * x i)
  rw [(mem_invariants a).1 ha g] at h
  simpa using h
end Invariant
variable (X : TopRep.{u} k G) [DiscreteTopology X] [IsDiscreteRep (underlyingRep X)]
def toInhomogeneous (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) :
    locallyConstantCochains (underlyingRep X) n :=
  ⟨fun g => nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g),
    (IsLocallyConstant.iff_continuous _).2
      ((nestedHomeomorph X (n + 1) σ.1).continuous.comp (continuous_partialProd n))⟩
omit [IsDiscreteRep (underlyingRep X)] in
theorem toInhomogeneous_apply (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants) (g : Fin n → G) :
    (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g =
      nestedHomeomorph X (n + 1) σ.1 (Fin.partialProd g) :=
  rfl
def homogeneousFun (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (x : Fin (n + 1) → G) : X :=
  X.ρ (x 0) (φ fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
omit [LocallyCompactSpace G] [DiscreteTopology X] in
theorem isLocallyConstant_homogeneousFun (n : ℕ) {φ : (Fin n → G) → underlyingRep X}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant (homogeneousFun X n φ) :=
  isLocallyConstant_ρ_apply (underlyingRep X) (continuous_apply 0)
    (hφ.comp_continuous (continuous_pi fun _ =>
      ((continuous_apply _).inv).mul (continuous_apply _)))
omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [DiscreteTopology X]
  [IsDiscreteRep (underlyingRep X)] in
theorem homogeneousFun_mul (n : ℕ) (φ : (Fin n → G) → underlyingRep X) (g : G)
    (x : Fin (n + 1) → G) :
    homogeneousFun X n φ (fun i => g * x i) = X.ρ g (homogeneousFun X n φ x) := by
  simp only [homogeneousFun, mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
  rfl
def ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n) :
    (resolutionX X (n + 1)).ρ.invariants :=
  ⟨(nestedHomeomorph X (n + 1)).symm
      ⟨homogeneousFun X n φ.1, (isLocallyConstant_homogeneousFun X n φ.2).continuous⟩, by
    rw [mem_invariants]
    intro g
    apply (nestedHomeomorph X (n + 1)).injective
    ext x
    rw [nestedHomeomorph_ρ_apply, Homeomorph.apply_symm_apply]
    change X.ρ g (homogeneousFun X n φ.1 fun i => g⁻¹ * x i) = homogeneousFun X n φ.1 x
    rw [homogeneousFun_mul]
    change (X.ρ g * X.ρ g⁻¹) _ = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl⟩
omit [DiscreteTopology X] in
theorem nestedHomeomorph_ofInhomogeneous (n : ℕ) (φ : locallyConstantCochains (underlyingRep X) n)
    (x : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 1) (ofInhomogeneous X n φ).1 x = homogeneousFun X n φ.1 x := by
  simp [ofInhomogeneous]
def homogeneousEquiv (n : ℕ) :
    locallyConstantCochains (underlyingRep X) n ≃ₗ[k] (resolutionX X (n + 1)).ρ.invariants :=
  LinearEquiv.symm
  { toFun := toInhomogeneous X n
    invFun := ofInhomogeneous X n
    map_add' σ τ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_add, Pi.add_apply]
      rw [nestedHomeomorph_add]
      rfl
    map_smul' r σ := by
      ext g
      simp only [toInhomogeneous_apply, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [nestedHomeomorph_smul]
      rfl
    left_inv σ := by
      apply Subtype.ext
      apply (nestedHomeomorph X (n + 1)).injective
      ext x
      rw [nestedHomeomorph_ofInhomogeneous]
      change X.ρ (x 0) (nestedHomeomorph X (n + 1) σ.1
        (Fin.partialProd fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)) = _
      rw [← nestedHomeomorph_mul_apply_of_mem_invariants X σ.2]
      congr 1
      exact Fin.partialProd_left_inv x
    right_inv φ := by
      ext g
      rw [toInhomogeneous_apply, nestedHomeomorph_ofInhomogeneous]
      simp only [homogeneousFun, Fin.partialProd_zero, Fin.partialProd_right_inv, map_one]
      rfl }
omit [IsDiscreteRep (underlyingRep X)] in

theorem nestedHomeomorph_d_partialProd (n : ℕ) (σ : (resolutionX X (n + 1)).ρ.invariants)
    (g : Fin (n + 1) → G) :
    nestedHomeomorph X (n + 2) ((d X (n + 1)).hom σ.1) (Fin.partialProd g) =
      (inhomogeneousCochains.d (underlyingRep X) n).hom
        (toInhomogeneous X n σ : (Fin n → G) → underlyingRep X) g := by
  rw [nestedHomeomorph_d_apply, Fin.sum_univ_succ, inhomogeneousCochains.d_hom_apply]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.partialProd_succ']
    exact nestedHomeomorph_mul_apply_of_mem_invariants X σ.2 _ _
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [toInhomogeneous_apply, Fin.partialProd_contractNth, Fin.val_succ]
    rfl
theorem homogeneousEquiv_symm_d (i : ℕ) (σ : (homogeneousCochains X).X i) :
    (homogeneousEquiv X (i + 1)).symm (((homogeneousCochains X).d i (i + 1)).hom σ) =
      (dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ) := by
  apply Subtype.ext
  funext g
  rw [dLocallyConstant_hom_apply]
  change nestedHomeomorph X (i + 2) (((homogeneousCochains X).d i (i + 1)).hom σ).1
    (Fin.partialProd g) = _
  rw [homogeneousCochains.d_apply]
  exact nestedHomeomorph_d_partialProd X i σ g
noncomputable def cochainsIsoHomogeneousCochains :
    cochainsComplex (underlyingRep X) ≅
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        (homogeneousCochains X) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (homogeneousEquiv X n).toModuleIso) (by
    rintro i j (rfl : i + 1 = j)
    rw [cochainsComplex_d]
    ext φ : 2
    obtain ⟨σ, rfl⟩ := (homogeneousEquiv X i).symm.surjective φ
    change ((homogeneousCochains X).d i (i + 1)).hom (homogeneousEquiv X i
      ((homogeneousEquiv X i).symm σ)) = homogeneousEquiv X (i + 1)
        ((dLocallyConstant (underlyingRep X) i).hom ((homogeneousEquiv X i).symm σ))
    rw [LinearEquiv.apply_symm_apply]
    exact (homogeneousEquiv X (i + 1)).symm_apply_eq.1 (homogeneousEquiv_symm_d X i σ))
noncomputable def cohomologyIsoContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology n X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cochainsIsoHomogeneousCochains X) ≪≫
    ((homogeneousCochains X).sc n).mapHomologyIso (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
noncomputable def cohomologyLinearEquivContinuousCohomology (n : ℕ) :
    cohomology (underlyingRep X) n ≃ₗ[k]
      ((continuousCohomology n X : TopModuleCat.{u} k) : Type u) :=
  (cohomologyIsoContinuousCohomology X n).toLinearEquiv
section Discrete
variable [DiscreteTopology k]
noncomputable def cohomologyIsoContinuousCohomologyDiscrete (A : Rep.{u} k G) [IsDiscreteRep A]
    (n : ℕ) :
    cohomology A n ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj
        (continuousCohomology n (discreteTopRep A)) :=
  cohomologyIsoContinuousCohomology (discreteTopRep A) n
noncomputable def cohomologyLinearEquivContinuousCohomologyDiscrete (A : Rep.{u} k G)
    [IsDiscreteRep A] (n : ℕ) :
    cohomology A n ≃ₗ[k]
      ((continuousCohomology n (discreteTopRep A) : TopModuleCat.{u} k) : Type u) :=
  cohomologyLinearEquivContinuousCohomology (discreteTopRep A) n
end Discrete
end GroundTheory.ProfCoh


