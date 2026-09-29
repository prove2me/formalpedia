-- Prove2me | solution 1 for AutomorphicForm.integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2b34c072-4b0b-500c-8380-5b373524243e

import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral

set_option autoImplicit false

noncomputable section

namespace R4PartialClassUnfold

set_option maxHeartbeats 1600000

open MeasureTheory NumberField Filter Function Set
open scoped ENNReal NNReal Topology Pointwise

section Instances

variable (L : Type) [Field L] [NumberField L]

theorem countable_L : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := countable_L L
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := by
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Instances

section Algebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

abbrev σG : GL (Fin 2) L →* GL (Fin 2) L := Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L z * g = g * AutomorphicForm.centralScalar (𝓞 L) L z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq

omit [NumberField L] in
theorem scalar_comm (u : Lˣ) (g : GL (Fin 2) L) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (u : L) (fun r' => Commute.all _ r') _).eq

omit [NumberField L] in
theorem scalar_mem_center (u : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.center (GL (Fin 2) L) :=
  Subgroup.mem_center_iff.mpr fun g => (scalar_comm L u g).symm

omit [NumberField L] in

theorem exists_scalar_of_mem_center {s : GL (Fin 2) L} (hs : s ∈ Subgroup.center (GL (Fin 2) L)) :
    ∃ u : Lˣ, s = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  exact ⟨u, hu.symm⟩

omit [NumberField L] in
theorem scalar_injective : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Lˣ → GL (Fin 2) L) := by
  intro u v h
  have := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simpa using Units.ext_iff.mpr (by simpa [Matrix.scalar_apply] using this)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem globalPoints_scalar (u : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      AutomorphicForm.centralScalar (𝓞 L) L (princ L u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (u : L) i j) =
    Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem actU_princ (v : Lˣ) : actU K L D σ (princ L v) = princ L (Units.map (σ : L →* L) v) := by
  refine Units.ext ?_
  exact D.compat σ (v : L)

theorem princ_mul_actU (u : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    princ L u * actU K L D σ z = actU K L D σ (princ L (Units.map (σ.symm : L →* L) u) * z) := by
  rw [map_mul, actU_princ]
  congr 2
  refine Units.ext ?_
  show (u : L) = σ (σ.symm (u : L))
  rw [AlgEquiv.apply_symm_apply]

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L g) =
      AutomorphicForm.globalPoints (𝓞 L) L (σG K L σ g) :=
  AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g

theorem kernelArg_eq (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (r δ₀ : GL (Fin 2) L) (u : Lˣ)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L
        (r * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG K L σ r)⁻¹) *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x) =
    ((AutomorphicForm.globalPoints (𝓞 L) L r)⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ
        (AutomorphicForm.centralScalar (𝓞 L) L (princ L (Units.map (σ.symm : L →* L) u) * z) *
          ((AutomorphicForm.globalPoints (𝓞 L) L r)⁻¹ * x)) := by
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set θ := AutomorphicForm.sigmaAdelicAct K L D σ with hθ
  set c := AutomorphicForm.centralScalar (𝓞 L) L with hc
  have hσr : θ (ι r) = ι (σG K L σ r) := sigmaAdelicAct_globalPoints' K L D σ r
  have hcθ : ∀ w, θ (c w) = c (actU K L D σ w) := fun w => by
    rw [hθ, hc, sigmaAdelicAct_centralScalar]

  have hL : x⁻¹ * ι (r * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG K L σ r)⁻¹) * θ (c z * x) =
      x⁻¹ * ι r * ι δ₀ * (θ (ι r))⁻¹ * θ x * c (princ L u * actU K L D σ z) := by
    rw [map_mul ι, map_mul ι, map_mul ι, map_inv ι, globalPoints_scalar, ← hσr, map_mul θ, hcθ,
      map_mul c]
    have h1 := centralScalar_comm L (princ L u)
    have h2 := centralScalar_comm L (actU K L D σ z)
    have eA : ι r * ι δ₀ * c (princ L u) * (θ (ι r))⁻¹ = ι r * ι δ₀ * (θ (ι r))⁻¹ * c (princ L u) := by
      rw [mul_assoc (ι r * ι δ₀), h1 ((θ (ι r))⁻¹), ← mul_assoc]
    have eB : c (actU K L D σ z) * θ x = θ x * c (actU K L D σ z) := h2 (θ x)
    have eC : c (princ L u) * (θ x * c (actU K L D σ z)) = θ x * (c (princ L u) * c (actU K L D σ z)) := by
      rw [← mul_assoc, h1 (θ x), mul_assoc]
    rw [eA, eB]
    simp only [mul_assoc]
    rw [eC]

  have hR : ((ι r)⁻¹ * x)⁻¹ * ι δ₀ * θ (c (princ L (Units.map (σ.symm : L →* L) u) * z) * ((ι r)⁻¹ * x)) =
      x⁻¹ * ι r * ι δ₀ * (θ (ι r))⁻¹ * θ x * c (princ L u * actU K L D σ z) := by
    rw [mul_inv_rev, inv_inv, map_mul θ, hcθ, ← princ_mul_actU K L D σ u z, map_mul θ, map_inv θ]
    have h3 := centralScalar_comm L (princ L u * actU K L D σ z)
    calc x⁻¹ * ι r * ι δ₀ * (c (princ L u * actU K L D σ z) * ((θ (ι r))⁻¹ * θ x))
        = x⁻¹ * ι r * ι δ₀ * ((θ (ι r))⁻¹ * θ x * c (princ L u * actU K L D σ z)) := by rw [h3]
      _ = x⁻¹ * ι r * ι δ₀ * (θ (ι r))⁻¹ * θ x * c (princ L u * actU K L D σ z) := by
          simp only [mul_assoc]
  rw [hL, hR]

theorem orbArg_eq (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ₀ : GL (Fin 2) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L w * y) =
      y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ y *
        AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ w) := by
  rw [map_mul, sigmaAdelicAct_centralScalar, centralScalar_comm L, ← mul_assoc]

theorem conj_orbArg_eq (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (r δ₀ : GL (Fin 2) L)
    (w : (AdeleRing (𝓞 L) L)ˣ) :
    x * (((AutomorphicForm.globalPoints (𝓞 L) L r)⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ
          (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L r)⁻¹ * x))) *
      (AutomorphicForm.sigmaAdelicAct K L D σ x)⁻¹ =
    AutomorphicForm.globalPoints (𝓞 L) L (r * δ₀ * (σG K L σ r)⁻¹) *
      AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ w) := by
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set θ := AutomorphicForm.sigmaAdelicAct K L D σ with hθ
  set c := AutomorphicForm.centralScalar (𝓞 L) L with hc
  rw [orbArg_eq K L D σ]
  rw [mul_inv_rev, inv_inv, map_mul θ, map_inv θ, sigmaAdelicAct_globalPoints' K L D σ, map_mul ι, map_mul ι,
    map_inv ι]
  have h := centralScalar_comm L (actU K L D σ w)
  calc x * (x⁻¹ * ι r * ι δ₀ * ((ι (σG K L σ r))⁻¹ * θ x) * c (actU K L D σ w)) * (θ x)⁻¹
      = ι r * ι δ₀ * (ι (σG K L σ r))⁻¹ * (θ x * c (actU K L D σ w) * (θ x)⁻¹) := by
        simp only [mul_assoc, mul_inv_cancel_left]
    _ = ι r * ι δ₀ * (ι (σG K L σ r))⁻¹ * c (actU K L D σ w) := by
        rw [← h (θ x), mul_assoc (c _), mul_inv_cancel, mul_one]

end Algebra

section Param

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
variable (δ₀ : GL (Fin 2) L) (I : Set (GL (Fin 2) L))
  (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
    δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
  (Λ : Subgroup (GL (Fin 2) L))
  (hΛ : ∀ γ, γ ∈ Λ ↔
    δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
  {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)

def param (p : ι × Lˣ) : GL (Fin 2) L :=
  r p.1 * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 * (σG K L σ (r p.1))⁻¹

def cosImg (i : ι) : GL (Fin 2) L := r i * δ₀ * (σG K L σ (r i))⁻¹

theorem param_eq_cosImg_mul (p : ι × Lˣ) :
    param K L σ δ₀ r p = cosImg K L σ δ₀ r p.1 * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 := by
  simp only [param, cosImg, mul_assoc, scalar_comm L p.2]

include hI in
theorem param_mem (p : ι × Lˣ) : param K L σ δ₀ r p ∈ I := by
  rw [hI]
  refine ⟨r p.1, ?_⟩
  have : (r p.1)⁻¹ * param K L σ δ₀ r p * σG K L σ (r p.1) =
      δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 := by
    simp only [param, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [this, inv_mul_cancel_left]
  exact scalar_mem_center L p.2

include hΛ hr in

theorem eq_of_cosImg_eq_mul_scalar {i j : ι} {u : Lˣ}
    (h : cosImg K L σ δ₀ r i = cosImg K L σ δ₀ r j * Matrix.GeneralLinearGroup.scalar (Fin 2) u) : i = j := by

  set γ : GL (Fin 2) L := (r j)⁻¹ * r i with hγ
  have hγΛ : γ ∈ Λ := by
    rw [hΛ]
    have key : γ * δ₀ * (σG K L σ γ)⁻¹ = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      have h1 : γ * δ₀ * (σG K L σ γ)⁻¹ = (r j)⁻¹ * cosImg K L σ δ₀ r i * σG K L σ (r j) := by
        simp only [hγ, cosImg, map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
      rw [h1, h]
      simp only [cosImg, mul_assoc, inv_mul_cancel_left]
      rw [scalar_comm L u, inv_mul_cancel_left]
    rw [key, inv_mul_cancel_left]
    exact scalar_mem_center L u
  obtain ⟨k, -, hk⟩ := hr (r i)
  have hi : i = k := hk i (by show (r i)⁻¹ * r i ∈ Λ; rw [inv_mul_cancel]; exact Λ.one_mem)
  have hj : j = k := hk j hγΛ
  rw [hi, hj]

include hΛ hr in
theorem param_injective : Function.Injective (param K L σ δ₀ r) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  rw [param_eq_cosImg_mul, param_eq_cosImg_mul] at h
  have h' : cosImg K L σ δ₀ r i = cosImg K L σ δ₀ r j * Matrix.GeneralLinearGroup.scalar (Fin 2) (v * u⁻¹) := by
    rw [map_mul, ← mul_assoc, ← h, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hij : i = j := eq_of_cosImg_eq_mul_scalar K L σ δ₀ Λ hΛ r hr h'
  subst hij
  have huv : Matrix.GeneralLinearGroup.scalar (Fin 2) u = Matrix.GeneralLinearGroup.scalar (Fin 2) v :=
    mul_left_cancel h
  rw [scalar_injective L huv]

include hI hΛ hr in
theorem param_surjOn : Set.SurjOn (param K L σ δ₀ r) Set.univ I := by
  intro δ hδ
  rw [hI] at hδ
  obtain ⟨g, hg⟩ := hδ
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center L hg

  obtain ⟨i, hiΛ, -⟩ := hr g
  set lam : GL (Fin 2) L := (r i)⁻¹ * g with hlam
  have hlam' : g = r i * lam := by rw [hlam, mul_inv_cancel_left]
  have hlamΛ := hiΛ
  rw [hΛ] at hlamΛ
  obtain ⟨u', hu'⟩ := exists_scalar_of_mem_center L hlamΛ
  refine ⟨(i, u' * u), Set.mem_univ _, ?_⟩

  have hδ : δ = g * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG K L σ g)⁻¹ := by
    have : g⁻¹ * δ * σG K L σ g = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      rw [← hu, mul_inv_cancel_left]
    calc δ = g * (g⁻¹ * δ * σG K L σ g) * (σG K L σ g)⁻¹ := by group
      _ = _ := by rw [this, ← mul_assoc]

  have hlamδ : lam * δ₀ * (σG K L σ lam)⁻¹ = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u' := by
    rw [← hu', mul_inv_cancel_left]
  show r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (u' * u) * (σG K L σ (r i))⁻¹ = δ
  rw [hδ, hlam', map_mul (σG K L σ) (r i) lam, mul_inv_rev, map_mul (Matrix.GeneralLinearGroup.scalar (Fin 2)) u' u]
  calc r i * δ₀ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * Matrix.GeneralLinearGroup.scalar (Fin 2) u) *
        (σG K L σ (r i))⁻¹
      = r i * (δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u') * Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (σG K L σ (r i))⁻¹ := by simp only [mul_assoc]
    _ = r i * (lam * δ₀ * (σG K L σ lam)⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (σG K L σ (r i))⁻¹ := by rw [hlamδ]
    _ = r i * lam * δ₀ * ((σG K L σ lam)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u) *
          (σG K L σ (r i))⁻¹ := by simp only [mul_assoc]
    _ = r i * lam * δ₀ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG K L σ lam)⁻¹) *
          (σG K L σ (r i))⁻¹ := by rw [← scalar_comm L u ((σG K L σ lam)⁻¹)]
    _ = _ := by simp only [mul_assoc]

include hI hΛ hr in
theorem param_bijOn : Set.BijOn (param K L σ δ₀ r) Set.univ I :=
  ⟨fun p _ => param_mem K L σ δ₀ I hI r p, (param_injective K L σ δ₀ Λ hΛ r hr).injOn,
    param_surjOn K L σ δ₀ I hI Λ hΛ r hr⟩

def famSet (S : Set ι) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | ∃ i ∈ S,
    δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈ Subgroup.center (GL (Fin 2) L)}

theorem inv_mul_param_mul (p : ι × Lˣ) :
    (r p.1)⁻¹ * param K L σ δ₀ r p * σG K L σ (r p.1) = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) p.2 := by
  simp only [param, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem param_mem_famSet {S : Set ι} {p : ι × Lˣ} (hp : p.1 ∈ S) : param K L σ δ₀ r p ∈ famSet K L σ δ₀ r S := by
  refine ⟨p.1, hp, ?_⟩
  show δ₀⁻¹ * ((r p.1)⁻¹ * param K L σ δ₀ r p * σG K L σ (r p.1)) ∈ Subgroup.center (GL (Fin 2) L)
  rw [inv_mul_param_mul, inv_mul_cancel_left]
  exact scalar_mem_center L p.2

theorem param_surjOn_famSet (S : Set ι) :
    Set.SurjOn (param K L σ δ₀ r) (S ×ˢ (Set.univ : Set Lˣ)) (famSet K L σ δ₀ r S) := by
  rintro δ ⟨i, hiS, hδ⟩
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center L hδ
  refine ⟨(i, u), Set.mk_mem_prod hiS (Set.mem_univ _), ?_⟩
  have h1 : (r i)⁻¹ * δ * σG K L σ (r i) = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [← hu, mul_inv_cancel_left]
  show r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG K L σ (r i))⁻¹ = δ
  calc r i * δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * (σG K L σ (r i))⁻¹
      = r i * ((r i)⁻¹ * δ * σG K L σ (r i)) * (σG K L σ (r i))⁻¹ := by rw [h1, ← mul_assoc]
    _ = δ := by group

include hΛ hr in

theorem param_bijOn_famSet (S : Set ι) :
    Set.BijOn (param K L σ δ₀ r) (S ×ˢ (Set.univ : Set Lˣ)) (famSet K L σ δ₀ r S) :=
  ⟨fun _ hp => param_mem_famSet K L σ δ₀ r (Set.mem_prod.mp hp).1,
    (param_injective K L σ δ₀ Λ hΛ r hr).injOn, param_surjOn_famSet K L σ δ₀ r S⟩

end Param

section Centre

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; (simp [Matrix.scalar_apply]; exact continuous_id)
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

theorem continuous_actU : Continuous (actU K L D σ) :=
  Continuous.units_map _ (D.continuous_act σ)

theorem actU_inv_apply (w : (AdeleRing (𝓞 L) L)ˣ) : actU K L D σ⁻¹ (actU K L D σ w) = w := by
  refine Units.ext ?_
  show (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (w : AdeleRing (𝓞 L) L)) = w
  rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem actU_apply_inv (w : (AdeleRing (𝓞 L) L)ˣ) : actU K L D σ (actU K L D σ⁻¹ w) = w := by
  refine Units.ext ?_
  show (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) (w : AdeleRing (𝓞 L) L)) = w
  rw [← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem isCompact_preimage_centralScalar {C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    IsCompact (AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C) := by
  set Φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ := fun g =>
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0,
      MulOpposite.op (((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0))
    with hΦ
  have hΦc : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact (Units.continuous_val.matrix_elem 0 0)
    · exact MulOpposite.continuous_op.comp (Units.continuous_coe_inv.matrix_elem 0 0)
  have hsub : AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C ⊆ Units.embedProduct _ ⁻¹' (Φ '' C) := by
    intro w hw
    refine ⟨AutomorphicForm.centralScalar (𝓞 L) L w, hw, ?_⟩
    simp only [hΦ, Units.embedProduct_apply]
    refine Prod.ext ?_ ?_
    · show Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L) 0 0 = (w : AdeleRing (𝓞 L) L)
      simp [Matrix.scalar_apply]
    · show MulOpposite.op (Matrix.scalar (Fin 2) ((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) 0 0) =
        MulOpposite.op ((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
      simp [Matrix.scalar_apply]
  have hclosed : IsClosed (AutomorphicForm.centralScalar (𝓞 L) L ⁻¹' C) :=
    hC.isClosed.preimage (continuous_centralScalar L)
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.image hΦc)).of_isClosed_subset hclosed hsub

theorem isCompact_preimage_actU {C : Set (AdeleRing (𝓞 L) L)ˣ} (hC : IsCompact C) :
    IsCompact (actU K L D σ ⁻¹' C) := by
  have himg : IsCompact (actU K L D σ⁻¹ '' C) := hC.image (continuous_actU K L D σ⁻¹)
  refine himg.of_isClosed_subset (hC.isClosed.preimage (continuous_actU K L D σ)) ?_
  intro w hw
  exact ⟨actU K L D σ w, hw, actU_inv_apply K L D σ w⟩

theorem finite_setOf_globalPoints_mem {C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    {γ : GL (Fin 2) L | AutomorphicForm.globalPoints (𝓞 L) L γ ∈ C}.Finite := by

  have hent : ∀ a b : Fin 2, {t : L | algebraMap L (AdeleRing (𝓞 L) L) t ∈
      (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) a b) '' C}.Finite :=
    fun a b => NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L
      (hC.image (Units.continuous_val.matrix_elem a b))
  have hpi : (Set.univ.pi fun p : Fin 2 × Fin 2 => {t : L | algebraMap L (AdeleRing (𝓞 L) L) t ∈
      (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) p.1 p.2) '' C}).Finite :=
    Set.Finite.pi fun p => hent p.1 p.2
  refine (hpi.preimage (f := fun γ : GL (Fin 2) L => fun p : Fin 2 × Fin 2 =>
    (γ : Matrix (Fin 2) (Fin 2) L) p.1 p.2) ?_).subset ?_
  · intro γ _ γ' _ h
    refine Matrix.GeneralLinearGroup.ext fun a b => ?_
    exact congrFun h (a, b)
  · intro γ hγ
    refine Set.mem_preimage.mpr (Set.mem_univ_pi.mpr fun p => ?_)
    exact ⟨AutomorphicForm.globalPoints (𝓞 L) L γ, hγ, rfl⟩

theorem finite_setOf_princ_mem {C : Set (AdeleRing (𝓞 L) L)ˣ} (hC : IsCompact C) :
    {u : Lˣ | princ L u ∈ C}.Finite := by
  have h := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L (hC.image Units.continuous_val)
  refine (h.preimage (f := fun u : Lˣ => (u : L)) (Units.val_injective.injOn)).subset ?_
  intro u hu
  exact ⟨princ L u, hu, rfl⟩

def projInv (γ : GL (Fin 2) L) : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → L :=
  fun p => (γ : Matrix (Fin 2) (Fin 2) L) p.1.1 p.1.2 * ((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) p.2.1 p.2.2

omit [NumberField L] in

theorem exists_scalar_of_projInv_eq {γ γ' : GL (Fin 2) L} (h : projInv L γ = projInv L γ') :
    ∃ u : Lˣ, γ = γ' * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by

  have hne : ∀ g : GL (Fin 2) L, ∃ a b : Fin 2, (g : Matrix (Fin 2) (Fin 2) L) a b ≠ 0 := by
    intro g
    by_contra hcon
    push Not at hcon
    have h0 : (g : Matrix (Fin 2) (Fin 2) L) = 0 := Matrix.ext fun a b => hcon a b
    have := g.isUnit.ne_zero
    exact this h0
  obtain ⟨a, b, hab⟩ := hne γ
  obtain ⟨c, d, hcd⟩ := hne γ⁻¹
  have hval : ∀ (p q : Fin 2 × Fin 2), (γ : Matrix (Fin 2) (Fin 2) L) p.1 p.2 *
      ((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) q.1 q.2 =
      (γ' : Matrix (Fin 2) (Fin 2) L) p.1 p.2 * ((γ'⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) q.1 q.2 :=
    fun p q => congrFun h (p, q)
  have h1 := hval (a, b) (c, d)
  simp only at h1
  have hprod : (γ' : Matrix (Fin 2) (Fin 2) L) a b * ((γ'⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) c d ≠ 0 := by
    rw [← h1]; exact mul_ne_zero hab hcd
  have hcd' : ((γ'⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) c d ≠ 0 := right_ne_zero_of_mul hprod

  set lam : L := ((γ'⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) c d /
    ((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) c d with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero hcd' hcd
  refine ⟨Units.mk0 lam hlam0, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  have h2 := hval (i, j) (c, d)
  simp only at h2
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change (γ : Matrix (Fin 2) (Fin 2) L) i j =
    ((γ' : Matrix (Fin 2) (Fin 2) L) * Matrix.scalar (Fin 2) ((Units.mk0 lam hlam0 : Lˣ) : L)) i j
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Units.val_mk0, hlam]
  field_simp
  linear_combination h2

theorem finite_image_projInv {C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    (projInv L '' {γ : GL (Fin 2) L | ∃ w : (AdeleRing (𝓞 L) L)ˣ,
      AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.centralScalar (𝓞 L) L w ∈ C}).Finite := by

  set e : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → AutomorphicForm.AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L :=
    fun p k => (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) p.1.1 p.1.2 *
      ((k⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) p.2.1 p.2.2 with he
  have hec : ∀ p, Continuous (e p) := fun p =>
    (Units.continuous_val.matrix_elem _ _).mul (Units.continuous_coe_inv.matrix_elem _ _)
  have hfin : ∀ p, {t : L | algebraMap L (AdeleRing (𝓞 L) L) t ∈ e p '' C}.Finite := fun p =>
    NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L (hC.image (hec p))
  refine (Set.Finite.pi fun p => hfin p).subset ?_
  rintro _ ⟨γ, ⟨w, hw⟩, rfl⟩
  refine Set.mem_univ_pi.mpr fun p => ?_
  refine ⟨_, hw, ?_⟩

  simp only [he, projInv]
  rw [mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  have hc1 : ((AutomorphicForm.centralScalar (𝓞 L) L w : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L) := rfl
  have hc2 : (((AutomorphicForm.centralScalar (𝓞 L) L w)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) ((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
    rw [← map_inv]; rfl
  have hg1 : ((AutomorphicForm.globalPoints (𝓞 L) L γ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = (γ : Matrix (Fin 2) (Fin 2) L).map (algebraMap L (AdeleRing (𝓞 L) L)) := rfl
  have hg2 : (((AutomorphicForm.globalPoints (𝓞 L) L γ)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
        ((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).map (algebraMap L (AdeleRing (𝓞 L) L)) := by
    rw [← map_inv]; rfl
  rw [hc1, hc2, hg1, hg2, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Matrix.map_apply, map_mul]
  calc (algebraMap L (AdeleRing (𝓞 L) L)) ((γ : Matrix (Fin 2) (Fin 2) L) p.1.1 p.1.2) * (w : AdeleRing (𝓞 L) L) *
        (((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) *
          (algebraMap L (AdeleRing (𝓞 L) L)) (((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) p.2.1 p.2.2))
      = (algebraMap L (AdeleRing (𝓞 L) L)) ((γ : Matrix (Fin 2) (Fin 2) L) p.1.1 p.1.2) *
          ((w : AdeleRing (𝓞 L) L) * ((w⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          (algebraMap L (AdeleRing (𝓞 L) L)) (((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) p.2.1 p.2.2) := by
        ring
    _ = _ := by rw [Units.mul_inv, mul_one]

end Centre

section Orbital

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (δ₀ : GL (Fin 2) L) (Λ : Subgroup (GL (Fin 2) L))
  (hΛ : ∀ γ, γ ∈ Λ ↔
    δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
  {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
  (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)

def orbF (i : ι) (w : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
    AutomorphicForm.sigmaAdelicAct K L D σ
      (AutomorphicForm.centralScalar (𝓞 L) L w * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))

def Kx : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  (fun m => x * m * (AutomorphicForm.sigmaAdelicAct K L D σ x)⁻¹) '' tsupport φ

theorem isCompact_Kx (hφs : HasCompactSupport φ) : IsCompact (Kx K L D σ φ x) :=
  hφs.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_Kx_of_orbF_ne_zero {i : ι} {w : (AdeleRing (𝓞 L) L)ˣ} (h : orbF K L D σ δ₀ r φ x i w ≠ 0) :
    AutomorphicForm.globalPoints (𝓞 L) L (cosImg K L σ δ₀ r i) *
        AutomorphicForm.centralScalar (𝓞 L) L (actU K L D σ w) ∈ Kx K L D σ φ x := by
  refine ⟨_, subset_tsupport φ (Function.mem_support.mpr h), ?_⟩
  exact conj_orbArg_eq K L D σ x (r i) δ₀ w

theorem continuous_orbF (hφc : Continuous φ) (i : ι) : Continuous (orbF K L D σ δ₀ r φ x i) := by
  refine hφc.comp ?_
  exact continuous_const.mul ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
    ((continuous_centralScalar L).mul continuous_const))

def Ki (i : ι) : Set (AdeleRing (𝓞 L) L)ˣ :=
  actU K L D σ ⁻¹' (AutomorphicForm.centralScalar (𝓞 L) L ⁻¹'
    ((fun k => (AutomorphicForm.globalPoints (𝓞 L) L (cosImg K L σ δ₀ r i))⁻¹ * k) '' Kx K L D σ φ x))

theorem isCompact_Ki (hφs : HasCompactSupport φ) (i : ι) : IsCompact (Ki K L D σ δ₀ r φ x i) :=
  isCompact_preimage_actU K L D σ (isCompact_preimage_centralScalar L
    ((isCompact_Kx K L D σ φ x hφs).image (continuous_const.mul continuous_id)))

theorem support_orbF_subset (i : ι) : support (orbF K L D σ δ₀ r φ x i) ⊆ Ki K L D σ δ₀ r φ x i := by
  intro w hw
  refine ⟨_, mem_Kx_of_orbF_ne_zero K L D σ δ₀ r φ x hw, ?_⟩
  simp only [inv_mul_cancel_left]

theorem hasCompactSupport_orbF (hφs : HasCompactSupport φ) (i : ι) :
    HasCompactSupport (orbF K L D σ δ₀ r φ x i) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Ki K L D σ δ₀ r φ x hφs i)
    (support_orbF_subset K L D σ δ₀ r φ x i)

def contrib : Set ι := {i | ∃ w : (AdeleRing (𝓞 L) L)ˣ, orbF K L D σ δ₀ r φ x i w ≠ 0}

include hΛ hr in

theorem finite_contrib (hφs : HasCompactSupport φ) : (contrib K L D σ δ₀ r φ x).Finite := by
  have hfin := finite_image_projInv L (isCompact_Kx K L D σ φ x hφs)
  have hinj : Set.InjOn (fun i : ι => projInv L (cosImg K L σ δ₀ r i))
      ((fun i : ι => projInv L (cosImg K L σ δ₀ r i)) ⁻¹'
        (projInv L '' {γ : GL (Fin 2) L | ∃ w : (AdeleRing (𝓞 L) L)ˣ,
          AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.centralScalar (𝓞 L) L w ∈ Kx K L D σ φ x})) := by
    intro i _ j _ h
    obtain ⟨u, hu⟩ := exists_scalar_of_projInv_eq L h
    exact eq_of_cosImg_eq_mul_scalar K L σ δ₀ Λ hΛ r hr hu
  refine (hfin.preimage hinj).subset ?_
  rintro i ⟨w, hw⟩
  exact ⟨cosImg K L σ δ₀ r i, ⟨actU K L D σ w, mem_Kx_of_orbF_ne_zero K L D σ δ₀ r φ x hw⟩, rfl⟩

theorem orbF_eq_zero_of_not_mem_contrib {i : ι} (hi : i ∉ contrib K L D σ δ₀ r φ x) (w : (AdeleRing (𝓞 L) L)ˣ) :
    orbF K L D σ δ₀ r φ x i w = 0 := by
  by_contra h
  exact hi ⟨w, h⟩

theorem finite_setOf_princ_mul_mem_support (hφs : HasCompactSupport φ) (i : ι) {N : Set (AdeleRing (𝓞 L) L)ˣ}
    (hN : IsCompact N) :
    {u : Lˣ | ∃ z ∈ N, orbF K L D σ δ₀ r φ x i (princ L u * z) ≠ 0}.Finite := by
  have hC : IsCompact ((fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 L) L)ˣ => p.1 * p.2⁻¹) ''
      (Ki K L D σ δ₀ r φ x i ×ˢ N)) :=
    ((isCompact_Ki K L D σ δ₀ r φ x hφs i).prod hN).image (continuous_fst.mul continuous_snd.inv)
  refine (finite_setOf_princ_mem L hC).subset ?_
  rintro u ⟨z, hz, hu⟩
  refine ⟨(princ L u * z, z), Set.mk_mem_prod (support_orbF_subset K L D σ δ₀ r φ x i hu) hz, ?_⟩
  simp only [mul_inv_cancel_right]

end Orbital

section Fold

variable (L : Type) [Field L] [NumberField L]

theorem princ_injective : Function.Injective (princ L) := by
  intro a b h
  have := congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h
  exact Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L this)

def princEquiv : Lˣ ≃ (princ L).range := (MonoidHom.ofInjective (princ_injective L)).toEquiv

theorem princEquiv_smul (u : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) : (princEquiv L u) • z = princ L u * z := rfl

theorem finsum_eq_tsum_range (g : (AdeleRing (𝓞 L) L)ˣ → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (hfin : (support fun u : Lˣ => g (princ L u * z)).Finite) :
    ∑ᶠ u : Lˣ, g (princ L u * z) = ∑' γ : (princ L).range, g (γ • z) := by
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional Lˣ) hfin]
  rw [← Equiv.tsum_eq (princEquiv L) (fun γ : (princ L).range => g (γ • z))]
  rfl

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)

theorem integrableOn_and_setIntegral_finsum_eq
    (hΩ : IsFundamentalDomain (princ L).range Ω νZ)
    (G : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hGc : Continuous G) (hGi : Integrable G νZ)
    (hfin : ∀ z, (support fun u : Lˣ => G (princ L u * z)).Finite)
    (hcont : Continuous fun z => ∑ᶠ u : Lˣ, G (princ L u * z)) :
    IntegrableOn (fun z => ∑ᶠ u : Lˣ, G (princ L u * z)) Ω νZ ∧
      ∫ z in Ω, ∑ᶠ u : Lˣ, G (princ L u * z) ∂νZ = ∫ w, G w ∂νZ := by
  haveI := countable_units L
  haveI : Countable (princ L).range :=
    Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (princ L))
  have hpt : ∀ z, ∑ᶠ u : Lˣ, G (princ L u * z) = ∑' γ : (princ L).range, G (γ • z) := fun z =>
    finsum_eq_tsum_range L G z (hfin z)
  have hfun : (fun z => ∑ᶠ u : Lˣ, G (princ L u * z)) = fun z => ∑' γ : (princ L).range, G (γ • z) :=
    funext hpt

  have hmeas : ∀ γ : (princ L).range, Continuous fun z => G (γ • z) := fun γ =>
    hGc.comp (continuous_const_smul γ)

  have hlin : ∑' γ : (princ L).range, ∫⁻ z in Ω, ‖G (γ • z)‖ₑ ∂νZ = ∫⁻ w, ‖G w‖ₑ ∂νZ :=
    (hΩ.lintegral_eq_tsum'' fun w => ‖G w‖ₑ).symm
  have hlt : ∫⁻ w, ‖G w‖ₑ ∂νZ < ⊤ := hGi.2
  refine ⟨?_, ?_⟩
  · refine ⟨hcont.aestronglyMeasurable, ?_⟩
    show ∫⁻ z in Ω, ‖∑ᶠ u : Lˣ, G (princ L u * z)‖ₑ ∂νZ < ⊤
    calc ∫⁻ z in Ω, ‖∑ᶠ u : Lˣ, G (princ L u * z)‖ₑ ∂νZ
        ≤ ∫⁻ z in Ω, ∑' γ : (princ L).range, ‖G (γ • z)‖ₑ ∂νZ := by
          refine lintegral_mono fun z => ?_
          rw [hpt z]
          exact enorm_tsum_le_tsum_enorm
      _ = ∑' γ : (princ L).range, ∫⁻ z in Ω, ‖G (γ • z)‖ₑ ∂νZ :=
          lintegral_tsum fun γ => (hmeas γ).enorm.measurable.aemeasurable
      _ < ⊤ := by rw [hlin]; exact hlt
  · rw [hfun, integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) (by rw [hlin]; exact hlt.ne)]
    exact (hΩ.integral_eq_tsum'' G hGi).symm

end Fold

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
  (hΩL : IsFundamentalDomain
    (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
    z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
      ξL ⟨z, Subgroup.mem_top z⟩ = 1)
  (δ₀ : GL (Fin 2) L)
  (Λ : Subgroup (GL (Fin 2) L))
  (hΛ : ∀ γ, γ ∈ Λ ↔
    δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
  {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
  (S : Set ι)
  (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
  (x : AutomorphicForm.AdelicGL2 (𝓞 L) L)

def ξf (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
theorem ξf_mul (a b : (AdeleRing (𝓞 L) L)ˣ) : ξf L ξL (a * b) = ξf L ξL a * ξf L ξL b := by
  have : (⟨a * b, Subgroup.mem_top (a * b)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
      ⟨a, Subgroup.mem_top a⟩ * ⟨b, Subgroup.mem_top b⟩ := rfl
  simp only [ξf, this, map_mul, Units.val_mul]

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
include hξt in
theorem ξf_princ_mul (u : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) : ξf L ξL (princ L u * z) = ξf L ξL z := by
  rw [ξf_mul, show ξf L ξL (princ L u) = 1 from ?_, one_mul]
  simp only [ξf, hξt (princ L u) ⟨u, rfl⟩, Units.val_one]

def Gi (i : ι) (w : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ξf L ξL w * orbF K L D σ δ₀ r φ x i w

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
include hξc hφc in
theorem continuous_Gi (i : ι) : Continuous (Gi K L D σ ξL δ₀ r φ x i) :=
  hξc.mul (continuous_orbF K L D σ δ₀ r φ x hφc i)

include hξc hφc hφs in
theorem integrable_Gi (i : ι) : Integrable (Gi K L D σ ξL δ₀ r φ x i) νZL :=
  (continuous_Gi K L D σ ξL hξc δ₀ r φ hφc x i).integrable_of_hasCompactSupport
    ((hasCompactSupport_orbF K L D σ δ₀ r φ x hφs i).mul_left)

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
theorem support_Gi_subset (i : ι) : support (Gi K L D σ ξL δ₀ r φ x i) ⊆ support (orbF K L D σ δ₀ r φ x i) := by
  intro w hw h0
  exact hw (by simp only [Gi, h0, mul_zero])

def Hi (i : ι) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ∑ᶠ u : Lˣ, Gi K L D σ ξL δ₀ r φ x i (princ L u * z)

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
include hφs in
theorem finite_support_Gi_princ_mul (i : ι) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (support fun u : Lˣ => Gi K L D σ ξL δ₀ r φ x i (princ L u * z)).Finite := by
  refine (finite_setOf_princ_mul_mem_support K L D σ δ₀ r φ x hφs i isCompact_singleton (N := {z})).subset ?_
  intro u hu
  exact ⟨z, rfl, support_Gi_subset K L D σ ξL δ₀ r φ x i hu⟩

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
include hξc hφc hφs in
theorem continuous_Hi (i : ι) : Continuous (Hi K L D σ ξL δ₀ r φ x i) := by
  haveI := locallyCompactSpace_ideles L
  refine continuous_finsum (fun u => (continuous_Gi K L D σ ξL hξc δ₀ r φ hφc x i).comp
    (continuous_const.mul continuous_id)) ?_
  intro z
  obtain ⟨N, hNc, hNz⟩ := exists_compact_mem_nhds z
  refine ⟨N, hNz, ?_⟩
  refine (finite_setOf_princ_mul_mem_support K L D σ δ₀ r φ x hφs i hNc).subset ?_
  rintro u ⟨z', hz'1, hz'2⟩
  exact ⟨z', hz'2, support_Gi_subset K L D σ ξL δ₀ r φ x i hz'1⟩

include hΩL hξc hφc hφs in
theorem integrableOn_Hi_and_setIntegral_eq (i : ι) :
    IntegrableOn (Hi K L D σ ξL δ₀ r φ x i) ΩL νZL ∧
      ∫ z in ΩL, Hi K L D σ ξL δ₀ r φ x i z ∂νZL = ∫ w, Gi K L D σ ξL δ₀ r φ x i w ∂νZL :=
  by
  have h := integrableOn_and_setIntegral_finsum_eq L νZL ΩL hΩL (Gi K L D σ ξL δ₀ r φ x i)
    (continuous_Gi K L D σ ξL hξc δ₀ r φ hφc x i) (integrable_Gi K L νZL D σ ξL hξc δ₀ r φ hφc hφs x i)
    (finite_support_Gi_princ_mul K L D σ ξL δ₀ r φ hφs x i) (continuous_Hi K L D σ ξL hξc δ₀ r φ hφc hφs x i)
  exact h

def unitsPerm : Lˣ ≃ Lˣ where
  toFun := Units.map (σ.symm : L →* L)
  invFun := Units.map (σ : L →* L)
  left_inv u := Units.ext (σ.apply_symm_apply (u : L))
  right_inv u := Units.ext (σ.symm_apply_apply (u : L))

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] in
include hΛ hr hξt hφs in
open scoped Classical in

theorem mul_finsum_famSet_eq (T : Finset ι) (hT : contrib K L D σ δ₀ r φ x ⊆ ↑T) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ξf L ξL z * ∑ᶠ δ ∈ famSet K L σ δ₀ r S, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) =
      ∑ i ∈ T.filter (· ∈ S), Hi K L D σ ξL δ₀ r φ x i z := by

  set f : ι × Lˣ → ℂ := fun p => orbF K L D σ δ₀ r φ x p.1 (princ L (unitsPerm K L σ p.2) * z) with hf

  have h1 : ∑ᶠ δ ∈ famSet K L σ δ₀ r S, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) =
      ∑ᶠ p ∈ S ×ˢ (Set.univ : Set Lˣ), f p := by
    refine (finsum_mem_eq_of_bijOn (param K L σ δ₀ r) (param_bijOn_famSet K L σ δ₀ Λ hΛ r hr S)
      fun p _ => ?_).symm
    exact congrArg φ (kernelArg_eq K L D σ x (r p.1) δ₀ p.2 z).symm

  have hU : ∀ i, {u : Lˣ | f (i, u) ≠ 0}.Finite := by
    intro i
    have hfin := finite_setOf_princ_mul_mem_support K L D σ δ₀ r φ x hφs i isCompact_singleton (N := {z})
    refine (hfin.preimage (unitsPerm K L σ).injective.injOn).subset ?_
    intro u hu
    exact ⟨z, rfl, hu⟩
  have hsupp : (support f).Finite := by
    refine ((finite_contrib K L D σ δ₀ Λ hΛ r hr φ x hφs).biUnion fun i _ => (hU i).image fun u => (i, u)).subset ?_
    rintro ⟨i, u⟩ hp
    have hi : i ∈ contrib K L D σ δ₀ r φ x := ⟨_, hp⟩
    exact Set.mem_biUnion hi ⟨u, hp, rfl⟩

  set g : ι × Lˣ → ℂ := fun p => (S ×ˢ (Set.univ : Set Lˣ)).indicator f p with hg
  have hgsupp : (support g).Finite :=
    hsupp.subset (by rw [hg, Set.support_indicator]; exact Set.inter_subset_right)
  have h2 : ∑ᶠ p ∈ S ×ˢ (Set.univ : Set Lˣ), f p = ∑ᶠ (i) (u), g (i, u) := by
    rw [finsum_mem_def]
    exact finsum_curry g hgsupp
  have hgi : ∀ i u, g (i, u) = if i ∈ S then f (i, u) else 0 := by
    intro i u
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact Set.indicator_of_mem (Set.mk_mem_prod hi (Set.mem_univ u)) f
    · rw [if_neg hi]; exact Set.indicator_of_notMem (fun h => hi (Set.mem_prod.mp h).1) f
  have hsub : (support fun i => ∑ᶠ u, g (i, u)) ⊆ ↑(T.filter (· ∈ S)) := by
    intro i hi
    rw [Finset.coe_filter]
    by_contra hni
    refine hi (finsum_eq_zero_of_forall_eq_zero fun u => ?_)
    rw [hgi]
    by_cases hiS : i ∈ S
    · rw [if_pos hiS]
      have hiT : i ∉ contrib K L D σ δ₀ r φ x := fun h => hni ⟨hT h, hiS⟩
      exact orbF_eq_zero_of_not_mem_contrib K L D σ δ₀ r φ x hiT _
    · rw [if_neg hiS]
  have h3 : ∑ᶠ (i) (u), g (i, u) = ∑ i ∈ T.filter (· ∈ S), ∑ᶠ u, g (i, u) :=
    finsum_eq_sum_of_support_subset _ hsub

  have h4 : ∀ i ∈ T.filter (· ∈ S), ξf L ξL z * ∑ᶠ u, g (i, u) = Hi K L D σ ξL δ₀ r φ x i z := by
    intro i hi
    have hiS : i ∈ S := (Finset.mem_filter.mp hi).2
    have hgf : (fun u => g (i, u)) = fun u => f (i, u) := funext fun u => by rw [hgi, if_pos hiS]
    rw [hgf, mul_finsum]
    unfold Hi
    rw [← finsum_comp_equiv (unitsPerm K L σ) (f := fun u => Gi K L D σ ξL δ₀ r φ x i (princ L u * z))]
    refine finsum_congr fun u => ?_
    show ξf L ξL z * orbF K L D σ δ₀ r φ x i (princ L (unitsPerm K L σ u) * z) =
      ξf L ξL (princ L (unitsPerm K L σ u) * z) * orbF K L D σ δ₀ r φ x i (princ L (unitsPerm K L σ u) * z)
    rw [ξf_princ_mul L ξL hξt]
  rw [h1, h2, h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => h4 i hi

include hΩL hΛ hr hξc hξt hφc hφs in
open scoped Classical in

theorem main :
    (contrib K L D σ δ₀ r φ x).Finite ∧
    (∀ i : ι, Integrable (Gi K L D σ ξL δ₀ r φ x i) νZL) ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
        ∑ᶠ δ ∈ famSet K L σ δ₀ r S, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL ∧
    (∫ z in ΩL, ξf L ξL z *
        ∑ᶠ δ ∈ famSet K L σ δ₀ r S, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) =
      ∑' i : S, ∫ w, Gi K L D σ ξL δ₀ r φ x (i : ι) w ∂νZL := by
  have hT := finite_contrib K L D σ δ₀ Λ hΛ r hr φ x hφs
  set T := hT.toFinset with hTdef
  have hfun : (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
      ∑ᶠ δ ∈ famSet K L σ δ₀ r S, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) =
      fun z => ∑ i ∈ T.filter (· ∈ S), Hi K L D σ ξL δ₀ r φ x i z :=
    funext fun z => mul_finsum_famSet_eq K L D σ ξL hξt δ₀ Λ hΛ r hr S φ hφs x T
      (by rw [hTdef, Set.Finite.coe_toFinset]) z
  have hH := fun i => integrableOn_Hi_and_setIntegral_eq K L νZL ΩL hΩL D σ ξL hξc δ₀ r φ hφc hφs x i
  refine ⟨hT, fun i => integrable_Gi K L νZL D σ ξL hξc δ₀ r φ hφc hφs x i, ?_, ?_⟩
  · rw [hfun]
    exact integrable_finsetSum _ fun i _ => (hH i).1
  · rw [hfun, integral_finsetSum _ fun i _ => (hH i).1]

    rw [tsum_subtype S (fun i : ι => ∫ w, Gi K L D σ ξL δ₀ r φ x i w ∂νZL)]
    rw [tsum_eq_sum (L := SummationFilter.unconditional ι) (s := T.filter (· ∈ S)) ?_]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Set.indicator_of_mem (Finset.mem_filter.mp hi).2, (hH i).2]
    · intro i hi
      by_cases hiS : i ∈ S
      · rw [Set.indicator_of_mem hiS]
        have hiT : i ∉ contrib K L D σ δ₀ r φ x := by
          intro h
          refine hi (Finset.mem_filter.mpr ⟨?_, hiS⟩)
          rw [hTdef, Set.Finite.mem_toFinset]; exact h
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
        show ξf L ξL w * orbF K L D σ δ₀ r φ x i w = 0
        rw [orbF_eq_zero_of_not_mem_contrib K L D σ δ₀ r φ x hiT, mul_zero]
      · exact Set.indicator_of_notMem hiS _

end Main

end R4PartialClassUnfold

end

section

open MeasureTheory NumberField

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L)
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (S : Set ι)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ,
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠
          0}.Finite ∧
    (∀ i : ι, Integrable (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))))
        νZL) ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ i ∈ S,
            δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈
              Subgroup.center (GL (Fin 2) L)},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL ∧
    (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ i ∈ S,
            δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈
              Subgroup.center (GL (Fin 2) L)},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) =
      ∑' i : S, ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r (i : ι)))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z *
              ((AutomorphicForm.globalPoints (𝓞 L) L (r (i : ι)))⁻¹ * x))) ∂νZL :=
  R4PartialClassUnfold.main K L νZL ΩL hΩL D σ ξL hξc hξt δ₀ Λ hΛ r hr S φ hφc hφs x

end

end S_AutomorphicForm_integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral (solution)
