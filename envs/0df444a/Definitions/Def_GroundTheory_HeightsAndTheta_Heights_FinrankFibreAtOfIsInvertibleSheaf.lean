-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
-- name    : GroundTheory_HeightsAndTheta_Heights_FinrankFibreAtOfIsInvertibleSheaf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:24.486659+00:00
-- url     : https://prove2.me/theorems/77654642-4e77-419f-9577-70c5351c95f2
-- title:
--   Finrank Fibre At Of Is Invertible Sheaf
-- statement:
--   Definitions and structural lemmas for Finrank Fibre At Of Is Invertible Sheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FinrankFibreAtOfIsInvertibleSheaf.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
def Via {R : Type*} [CommRing R] (_φ : R →+* ℂ) : Type := ℂ
namespace Via
variable {R : Type*} [CommRing R] (φ : R →+* ℂ)
instance : Field (Via φ) := inferInstanceAs (Field ℂ)
instance : Algebra R (Via φ) := φ.toAlgebra
def ofComplex : ℂ ≃+* Via φ := RingEquiv.refl ℂ
def conj : Via φ →ₗ[R] Via ((starRingEnd ℂ).comp φ) where
  toFun z := starRingEnd ℂ (show ℂ from z)
  map_add' a b := map_add (starRingEnd ℂ) (show ℂ from a) (show ℂ from b)
  map_smul' r z := by
    change starRingEnd ℂ (φ r * (show ℂ from z)) = (starRingEnd ℂ) (φ r) * starRingEnd ℂ (show ℂ from z)
    rw [map_mul]
def conjInv : Via ((starRingEnd ℂ).comp φ) →ₗ[R] Via φ where
  toFun z := starRingEnd ℂ (show ℂ from z)
  map_add' a b := map_add (starRingEnd ℂ) (show ℂ from a) (show ℂ from b)
  map_smul' r z := by
    change starRingEnd ℂ (starRingEnd ℂ (φ r) * (show ℂ from z)) =
      φ r * starRingEnd ℂ (show ℂ from z)
    rw [map_mul, Complex.conj_conj]
lemma conjInv_conj (z : Via φ) : conjInv φ (conj φ z) = z := Complex.conj_conj (show ℂ from z)
lemma conj_conjInv (z : Via ((starRingEnd ℂ).comp φ)) : conj φ (conjInv φ z) = z :=
  Complex.conj_conj (show ℂ from z)
end Via
variable {X : Scheme.{u}} (L : X.Modules)
variable (X) in

abbrev locRing (p : X) : CommRingCat.{u} := TopCat.Presheaf.stalk (X := X.toTopCat) X.sheaf.obj p
abbrev modStalk (p : X) : Type u :=
  TopCat.Presheaf.stalk (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf p
def fibreAt (p : X) (φ : locRing X p →+* ℂ) : Type u :=
  TensorProduct (locRing X p) (Via φ) (modStalk L p)
variable {L}
def germM {U : X.Opens} {p : X} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) :
    modStalk L p :=
  TopCat.Presheaf.germ (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf U p hp s
def germR {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U) : locRing X p :=
  TopCat.Presheaf.germ (X := X.toTopCat) X.sheaf.obj U p hp r
lemma germM_smul {U : X.Opens} {p : X} (hp : p ∈ U) (r : ringOn X U)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (r • s) = germR hp r • germM hp s :=
  PresheafOfModules.germ_smul _ _ _ _ _ _
lemma germM_resM {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V)
    (s : ((preMod X).obj L).obj (op U)) : germM hp (resM _ hVU s) = germM (hVU hp) s :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) (C := Ab.{u}) ((preMod X).obj L).presheaf
    (homOfLE hVU) p hp s
lemma germR_resR {U V : X.Opens} (hVU : V ≤ U) {p : X} (hp : p ∈ V) (r : ringOn X U) :
    germR hp (resR hVU r) = germR (hVU hp) r :=
  TopCat.Presheaf.germ_res_apply (X := X.toTopCat) X.sheaf.obj (homOfLE hVU) p hp r
lemma germM_zero {U : X.Opens} {p : X} (hp : p ∈ U) :
    germM (L := L) hp (0 : ((preMod X).obj L).obj (op U)) = 0 :=
  map_zero _
theorem bijective_smul_germ {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) :
    Function.Bijective (fun r : locRing X p => r • germM hp e) := by
  have key : ∀ r : locRing X p, r • germM hp e = 0 → r = 0 := by
    intro r hr
    obtain ⟨V, hVU, hpV, r', rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat) X.sheaf.obj r hp
    change germR hpV r' • germM hp e = 0 at hr
    rw [← germM_resM hVU hpV, ← germM_smul] at hr
    obtain ⟨W, hpW, iV, iV', hW⟩ := TopCat.Presheaf.germ_eq (X := X.toTopCat) (C := Ab.{u})
      ((preMod X).obj L).presheaf p hpV hpV _ 0 (hr.trans (germM_zero hpV).symm)
    have h0 : resR iV.le r' • resM _ (iV.le.trans hVU) e = 0 := by
      rw [← resM_smul_res]
      exact hW.trans (map_zero _)
    have hz : resR iV.le r' = 0 :=
      (he W (iV.le.trans hVU)).1 (a₁ := resR iV.le r') (a₂ := 0) (by
        simp only [zero_smul]; exact h0)
    change germR hpV r' = 0
    rw [← germR_resR iV.le hpW, hz]
    exact map_zero _
  constructor
  · intro r₁ r₂ h
    have := key (r₁ - r₂) (by simp only at h; rw [sub_smul, h, sub_self])
    exact sub_eq_zero.mp this
  · intro m
    obtain ⟨V, hVU, hpV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq (X := X.toTopCat)
      (C := Ab.{u}) ((preMod X).obj L).presheaf m hp
    obtain ⟨r, hr⟩ := (he V hVU).2 t
    refine ⟨germR hpV r, ?_⟩
    change germR hpV r • germM hp e = germM hpV t
    rw [← hr, germM_smul, germM_resM]
def stalkEquiv {U : X.Opens} {p : X} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : locRing X p ≃ₗ[locRing X p] modStalk L p :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (germM hp e)) (bijective_smul_germ hp he)
section Fibre
variable {p : X} {φ : locRing X p →+* ℂ}
instance : AddCommGroup (fibreAt L p φ) :=
  inferInstanceAs (AddCommGroup (TensorProduct (locRing X p) (Via φ) (modStalk L p)))
instance : Module (Via φ) (fibreAt L p φ) :=
  inferInstanceAs (Module (Via φ) (TensorProduct (locRing X p) (Via φ) (modStalk L p)))
instance : Module ℂ (fibreAt L p φ) :=
  Module.compHom (fibreAt L p φ) (Via.ofComplex φ).toRingHom
lemma complex_smul_def (c : ℂ) (s : fibreAt L p φ) : c • s = Via.ofComplex φ c • s := rfl
variable (L φ) in

def fibreMk (c : Via φ) (m : modStalk L p) : fibreAt L p φ :=
  (c ⊗ₜ[locRing X p] m : TensorProduct (locRing X p) (Via φ) (modStalk L p))
variable (φ) in

def value {U : X.Opens} (hp : p ∈ U) (s : ((preMod X).obj L).obj (op U)) : fibreAt L p φ :=
  fibreMk L φ 1 (germM hp s)
variable (φ) in

def fibreEquiv {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreAt L p φ ≃ₗ[Via φ] Via φ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Via φ) (Via φ))
    (stalkEquiv hp he).symm).trans
      (TensorProduct.AlgebraTensorModule.rid (locRing X p) (Via φ) (Via φ))
variable (φ) in

def fibreEquivComplex {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) : fibreAt L p φ ≃ₗ[ℂ] ℂ where
  toFun s := (Via.ofComplex φ).symm (fibreEquiv φ hp he s)
  invFun c := (fibreEquiv φ hp he).symm (Via.ofComplex φ c)
  map_add' a b := by rw [map_add, map_add]
  map_smul' c s := by
    rw [complex_smul_def, LinearEquiv.map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    rfl
  left_inv s := by simp
  right_inv c := by simp
variable (φ) in

def fibreConj : fibreAt L p φ ≃+ fibreAt L p ((starRingEnd ℂ).comp φ) where
  toFun s := TensorProduct.map (Via.conj φ) LinearMap.id
    (show TensorProduct (locRing X p) (Via φ) (modStalk L p) from s)
  invFun s := TensorProduct.map (Via.conjInv φ) LinearMap.id
    (show TensorProduct (locRing X p) (Via ((starRingEnd ℂ).comp φ)) (modStalk L p) from s)
  left_inv s := by
    change TensorProduct.map (Via.conjInv φ) LinearMap.id
      (TensorProduct.map (Via.conj φ) LinearMap.id
        (show TensorProduct (locRing X p) (Via φ) (modStalk L p) from s)) = s
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have : (Via.conjInv φ).comp (Via.conj φ) = LinearMap.id := LinearMap.ext (Via.conjInv_conj φ)
    rw [this, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  right_inv s := by
    change TensorProduct.map (Via.conj φ) LinearMap.id
      (TensorProduct.map (Via.conjInv φ) LinearMap.id
        (show TensorProduct (locRing X p) (Via ((starRingEnd ℂ).comp φ)) (modStalk L p) from s)) = s
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have : (Via.conj φ).comp (Via.conjInv φ) = LinearMap.id := LinearMap.ext (Via.conj_conjInv φ)
    rw [this, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply]
  map_add' a b := map_add _ _ _
end Fibre
end
end GroundTheory.Heights₂.Heights


