-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
-- name    : GroundTheory_AutomorphicForms_WhittakerGroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:55.884795+00:00
-- url     : https://prove2.me/theorems/1d7bce02-6422-4e35-87f9-bf276a5c8781
-- title:
--   Whittaker Groups
-- statement:
--   Definitions and structural lemmas for Whittaker Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_unipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open Matrix DoubleCoset
section Algebra
variable {F : Type*} [Field F] {n : ℕ}
def superdiagSum (M : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin n, ∑ j : Fin n, if j.val = i.val + 1 then M i j else 0
theorem mul_apply_of_val_eq_succ {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) {i j : Fin n} (hij : j.val = i.val + 1) :
    ((u * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (u : Matrix (Fin n) (Fin n) F) i j + (v : Matrix (Fin n) (Fin n) F) i j := by
  rw [Units.val_mul, Matrix.mul_apply]
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have key : ∀ k : Fin n, (u : Matrix (Fin n) (Fin n) F) i k * (v : Matrix (Fin n) (Fin n) F) k j =
      (if k = i then (v : Matrix (Fin n) (Fin n) F) i j else 0) +
        (if k = j then (u : Matrix (Fin n) (Fin n) F) i j else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, if_neg hne, hu.2 k, one_mul, add_zero]
    by_cases hkj : k = j
    · subst hkj
      rw [if_neg hki, if_pos rfl, hv.2 k, mul_one, zero_add]
    rw [if_neg hki, if_neg hkj, add_zero]
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hu.1 hlt, zero_mul]
    · have : j < k := by
        have h1 : i.val < k.val := hgt
        have h2 : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        show j.val < k.val
        omega
      rw [hv.1 this, mul_zero]
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), add_comm]
theorem superdiagSum_mul {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) :
    superdiagSum ((u * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      superdiagSum (u : Matrix (Fin n) (Fin n) F) + superdiagSum (v : Matrix (Fin n) (Fin n) F) := by
  unfold superdiagSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · exact mul_apply_of_val_eq_succ hu hv h
  · rw [add_zero]
theorem superdiagSum_one : superdiagSum (1 : Matrix (Fin n) (Fin n) F) = 0 := by
  unfold superdiagSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by rw [e] at h; omega)
  · rfl
def psiN (ψ₀ : AddChar F ℂ) (g : GL (Fin n) F) : ℂ :=
  ψ₀ (superdiagSum (g : Matrix (Fin n) (Fin n) F))
variable (ψ₀ : AddChar F ℂ)
theorem psiN_mul {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) : psiN ψ₀ (u * v) = psiN ψ₀ u * psiN ψ₀ v := by
  rw [psiN, superdiagSum_mul hu hv, AddChar.map_add_eq_mul]
  rfl
@[simp]
theorem psiN_one : psiN ψ₀ (1 : GL (Fin n) F) = 1 := by
  rw [psiN, Units.val_one, superdiagSum_one, AddChar.map_zero_eq_one]
def psiNHom : Iwasawa.unipotent F n →* ℂ where
  toFun u := psiN ψ₀ (u : GL (Fin n) F)
  map_one' := psiN_one ψ₀
  map_mul' u v := psiN_mul ψ₀ u.2 v.2
@[simp]
theorem psiNHom_apply (u : Iwasawa.unipotent F n) : psiNHom ψ₀ u = psiN ψ₀ (u : GL (Fin n) F) :=
  rfl
def sigmaMat (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => M (Fin.rev j) (Fin.rev i)
omit [Field F] in
theorem sigmaMat_apply (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    sigmaMat M i j = M (Fin.rev j) (Fin.rev i) := rfl
theorem sigmaMat_mul (M M' : Matrix (Fin n) (Fin n) F) :
    sigmaMat (M * M') = sigmaMat M' * sigmaMat M := by
  ext i j
  simp only [sigmaMat_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply]
  ring
theorem sigmaMat_one : sigmaMat (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  ext i j
  simp only [sigmaMat_apply, Matrix.one_apply, Fin.rev_inj]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]
omit [Field F] in
theorem sigmaMat_sigmaMat (M : Matrix (Fin n) (Fin n) F) : sigmaMat (sigmaMat M) = M := by
  ext i j
  simp [sigmaMat_apply]
def sigma (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨sigmaMat (g : Matrix (Fin n) (Fin n) F), sigmaMat ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
    by rw [← sigmaMat_mul, Units.inv_mul, sigmaMat_one],
    by rw [← sigmaMat_mul, Units.mul_inv, sigmaMat_one]⟩
theorem coe_sigma (g : GL (Fin n) F) :
    ((sigma g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = sigmaMat (g : Matrix (Fin n) (Fin n) F) :=
  rfl
theorem sigma_apply (g : GL (Fin n) F) (i j : Fin n) :
    ((sigma g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (g : Matrix (Fin n) (Fin n) F) (Fin.rev j) (Fin.rev i) := rfl
theorem sigma_mul (g h : GL (Fin n) F) : sigma (g * h) = sigma h * sigma g :=
  Units.ext (by rw [Units.val_mul, coe_sigma, coe_sigma, coe_sigma, Units.val_mul, sigmaMat_mul])
@[simp]
theorem sigma_one : sigma (1 : GL (Fin n) F) = 1 :=
  Units.ext (by rw [coe_sigma, Units.val_one, sigmaMat_one])
@[simp]
theorem sigma_sigma (g : GL (Fin n) F) : sigma (sigma g) = g :=
  Units.ext (by rw [coe_sigma, coe_sigma, sigmaMat_sigmaMat])
theorem sigma_inv (g : GL (Fin n) F) : sigma g⁻¹ = (sigma g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← sigma_mul, mul_inv_cancel, sigma_one]
theorem sigma_mem_unipotent {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    sigma u ∈ Iwasawa.unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [sigma_apply]
    exact hu.1 (Fin.rev_lt_rev.2 hij)
  · rw [sigma_apply]
    exact hu.2 (Fin.rev i)
def theta (g : GL (Fin n) F) : GL (Fin n) F := (sigma g)⁻¹
theorem theta_mul (g h : GL (Fin n) F) : theta (g * h) = theta g * theta h := by
  rw [theta, theta, theta, sigma_mul, _root_.mul_inv_rev]
@[simp]
theorem theta_theta (g : GL (Fin n) F) : theta (theta g) = g := by
  rw [theta, theta, ← sigma_inv g, sigma_sigma, inv_inv]
theorem theta_mem_unipotent {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    theta u ∈ Iwasawa.unipotent F n :=
  (Iwasawa.unipotent F n).inv_mem (sigma_mem_unipotent hu)
def thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n where
  toFun u := ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩
  invFun u := ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩
  left_inv _ := Subtype.ext (theta_theta _)
  right_inv _ := Subtype.ext (theta_theta _)
  map_mul' _ _ := Subtype.ext (theta_mul _ _)
@[simp]
theorem coe_thetaN (u : Iwasawa.unipotent F n) :
    ((thetaN u : Iwasawa.unipotent F n) : GL (Fin n) F) = theta (u : GL (Fin n) F) := rfl
theorem single_mul_single_self_of_ne {i j : Fin n} (h : i ≠ j) (a b : F) :
    Matrix.single i j a * Matrix.single i j b = 0 :=
  Matrix.single_mul_single_of_ne a i j i (Ne.symm h) b
def rootElt (i j : Fin n) (a : F) : GL (Fin n) F :=
  if h : i = j then 1 else
    ⟨1 + Matrix.single i j a, 1 - Matrix.single i j a,
      by rw [add_mul, one_mul, mul_sub, mul_one, single_mul_single_self_of_ne h, sub_zero,
        sub_add_cancel],
      by rw [sub_mul, one_mul, mul_add, mul_one, single_mul_single_self_of_ne h, add_zero,
        add_sub_cancel_right]⟩
theorem coe_rootElt {i j : Fin n} (h : i ≠ j) (a : F) :
    ((rootElt i j a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single i j a := by
  rw [rootElt, dif_neg h]
theorem rootElt_self (i : Fin n) (a : F) : rootElt i i a = 1 := by
  rw [rootElt, dif_pos rfl]
@[simp]
theorem rootElt_zero (i j : Fin n) : rootElt i j (0 : F) = 1 := by
  by_cases h : i = j
  · rw [h, rootElt_self]
  · exact Units.ext (by rw [coe_rootElt h, Matrix.single_zero, add_zero, Units.val_one])
theorem rootElt_add (i j : Fin n) (a b : F) :
    rootElt i j (a + b) = rootElt i j a * rootElt i j b := by
  by_cases h : i = j
  · rw [h, rootElt_self, rootElt_self, rootElt_self, mul_one]
  · refine Units.ext ?_
    rw [Units.val_mul, coe_rootElt h, coe_rootElt h, coe_rootElt h, add_mul, one_mul, mul_add,
      mul_one, single_mul_single_self_of_ne h, add_zero, Matrix.single_add]
    abel
def rootEltHom (i j : Fin n) : Multiplicative F →* GL (Fin n) F where
  toFun a := rootElt i j a.toAdd
  map_one' := rootElt_zero i j
  map_mul' a b := rootElt_add i j a.toAdd b.toAdd
@[simp]
theorem rootEltHom_apply (i j : Fin n) (a : Multiplicative F) :
    rootEltHom i j a = rootElt i j a.toAdd := rfl
end Algebra
section Topology
variable {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ}
theorem continuous_sigmaMat_val :
    Continuous fun g : GL (Fin n) F => sigmaMat (g : Matrix (Fin n) (Fin n) F) :=
  continuous_matrix fun i j => Units.continuous_val.matrix_elem (Fin.rev j) (Fin.rev i)
theorem continuous_sigma : Continuous (sigma : GL (Fin n) F → GL (Fin n) F) := by
  refine Units.continuous_iff.2 ⟨continuous_sigmaMat_val, ?_⟩
  have : (fun g : GL (Fin n) F => (((sigma g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      fun g => sigmaMat ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    funext g
    rw [← sigma_inv, coe_sigma]
  rw [this]
  exact continuous_matrix fun i j => Units.continuous_coe_inv.matrix_elem (Fin.rev j) (Fin.rev i)
def sigmaHomeo : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toFun := sigma
  invFun := sigma
  left_inv := sigma_sigma
  right_inv := sigma_sigma
  continuous_toFun := continuous_sigma
  continuous_invFun := continuous_sigma
@[simp]
theorem sigmaHomeo_apply (g : GL (Fin n) F) : sigmaHomeo g = sigma g := rfl
variable [IsTopologicalRing F]
end Topology
section LocalField
open ValuativeRel Topology
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
theorem isClosed_unipotent : IsClosed (Iwasawa.unipotent F n : Set (GL (Fin n) F)) := by
  have hset : (Iwasawa.unipotent F n : Set (GL (Fin n) F)) =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i),
        {g : GL (Fin n) F | (g : Matrix (Fin n) (Fin n) F) i j = 0}) ∩
      ⋂ i : Fin n, {g : GL (Fin n) F | (g : Matrix (Fin n) (Fin n) F) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, Iwasawa.mem_unipotent, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨fun i j hij => h.1 hij, h.2⟩, fun h => ⟨fun i j hij => h.1 i j hij, h.2⟩⟩
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter
    fun _ => isClosed_eq (GLnLocal.continuous_entry F n i j) continuous_const)
    (isClosed_iInter fun i => isClosed_eq (GLnLocal.continuous_entry F n i i) continuous_const)
instance locallyCompactSpace_unipotent : LocallyCompactSpace (Iwasawa.unipotent F n) :=
  (isClosed_unipotent F n).locallyCompactSpace
instance totallyDisconnectedSpace_unipotent : TotallyDisconnectedSpace (Iwasawa.unipotent F n) :=
  inferInstance
instance sigmaCompactSpace_GL : SigmaCompactSpace (GL (Fin n) F) := inferInstance
instance sigmaCompactSpace_unipotent : SigmaCompactSpace (Iwasawa.unipotent F n) :=
  (isClosed_unipotent F n).sigmaCompactSpace
end LocalField
end Whittaker
end GroundTheory.Automorphic


