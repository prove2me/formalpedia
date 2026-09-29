-- Prove2me | solution 1 for AutomorphicForm.exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b4f9f6f1-926b-5e49-b23c-949a51764a61

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure NumberField IsDedekindDomain TopologicalSpace Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace R3TwcIso

open AutomorphicForm

section LinearAlgebra

theorem exists_eq_smul_one_add_smul {R : Type*} [CommRing R] (g X : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (Matrix.trace g ^ 2 - 4 * Matrix.det g)) (h : X * g = g * X) :
    ∃ α β : R, X = α • (1 : Matrix (Fin 2) (Fin 2) R) + β • g := by
  obtain ⟨d, hd⟩ := hg.exists_left_inv
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hd
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  let B : R := d * (2 * g 1 0 * X 0 1 + 2 * g 0 1 * X 1 0 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  refine ⟨X 0 0 - B * g 0 0, B, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, B, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, mul_one, mul_zero, zero_add]
  · ring
  · linear_combination (-(X 0 1)) * hd - (d * (g 0 0 - g 1 1)) * e01 + (2 * d * g 0 1) * e00
  · linear_combination (-(X 1 0)) * hd + (d * (g 0 0 - g 1 1)) * e10 - (2 * d * g 1 0) * e00
  · linear_combination (X 0 0 - X 1 1) * hd - (2 * d * g 1 0) * e01 + (2 * d * g 0 1) * e10

theorem mul_comm_of_mem_centralizer {R : Type*} [CommRing R] {g : GL (Fin 2) R}
    (hg : IsRegularSemisimple g) {s z : GL (Fin 2) R}
    (hs : s ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) R)))
    (hz : z ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) R))) : s * z = z * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs hz
  have hs' : (s : Matrix (Fin 2) (Fin 2) R) * g = g * s := by
    rw [← Units.val_mul, hs, Units.val_mul]
  have hz' : (z : Matrix (Fin 2) (Fin 2) R) * g = g * z := by
    rw [← Units.val_mul, hz, Units.val_mul]
  obtain ⟨α, β, hS⟩ := exists_eq_smul_one_add_smul _ _ hg hs'
  obtain ⟨α', β', hZ⟩ := exists_eq_smul_one_add_smul _ _ hg hz'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hS, hZ]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul]
  rw [mul_comm α' α, mul_comm α' β, mul_comm β' α, mul_comm β' β]
  abel

theorem isRegularSemisimple_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {g : GL (Fin 2) R} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have := hg.map f
  simpa [map_ofNat] using this

theorem val_scalar {R : Type*} [CommRing R] (z : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (z : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  change Matrix.scalar (Fin 2) (z : R) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem isRegularSemisimple_mul_scalar {R : Type*} [CommRing R] {g : GL (Fin 2) R}
    (hg : IsRegularSemisimple g) (z : Rˣ) :
    IsRegularSemisimple (g * Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  unfold IsRegularSemisimple at hg ⊢
  rw [Units.val_mul, val_scalar, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.det_smul,
    Fintype.card_fin, smul_eq_mul]
  have : (↑z * Matrix.trace (g : Matrix (Fin 2) (Fin 2) R)) ^ 2 -
        4 * (↑z ^ 2 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) =
      (z : R) ^ 2 * (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 -
        4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
    ring
  rw [this]
  exact ((Units.isUnit z).pow 2).mul hg

theorem mul_scalar_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) c = Matrix.GeneralLinearGroup.scalar (Fin 2) c * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_scalar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem centralizer_mul_scalar {R : Type*} [CommRing R] (g : GL (Fin 2) R) (c : Rˣ) :
    Subgroup.centralizer ({g * Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) R)) =
      Subgroup.centralizer ({g} : Set (GL (Fin 2) R)) := by
  ext s
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, mul_assoc,
    ← mul_scalar_comm c s, ← mul_assoc, ← mul_assoc]
  exact mul_left_inj _

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) z) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, val_scalar, val_scalar, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem generalLinearGroup_map_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  intro g h hgh
  apply Units.ext
  have := congrArg (fun u : GL (Fin 2) S => (u : Matrix (Fin 2) (Fin 2) S)) hgh
  exact Matrix.map_injective hf this

end LinearAlgebra

section TensorFixed

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) : sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sigmaTensor]

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  rw [Algebra.TensorProduct.includeRight_apply, sigmaTensor_tmul, map_one]

theorem rTensor_sub_apply (u : L ⊗[K] A) :
    ((σ.toLinearMap - LinearMap.id).rTensor A) u = sigmaTensor K L A σ u - u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      rw [LinearMap.rTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply, TensorProduct.sub_tmul,
        sigmaTensor_tmul]
      rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]; abel

theorem exists_eq_tmul_of_fixed
    (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (u : L ⊗[K] A) (hu : sigmaTensor K L A σ u = u) :
    ∃ a : A, u = (1 : L) ⊗ₜ[K] a := by
  have hex : Function.Exact (Algebra.linearMap K L) (σ.toLinearMap - LinearMap.id : L →ₗ[K] L) := by
    intro l
    constructor
    · intro hl
      have hl' : σ l = l := by
        have : σ l - l = 0 := hl
        exact sub_eq_zero.1 this
      exact hfix l hl'
    · rintro ⟨k, rfl⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Algebra.linearMap_apply,
        AlgEquiv.toLinearMap_apply, AlgEquiv.commutes, sub_self]
  have hexA := Module.Flat.rTensor_exact A hex
  have hu0 : ((σ.toLinearMap - LinearMap.id).rTensor A) u = 0 := by
    rw [rTensor_sub_apply, hu, sub_self]
  obtain ⟨w, hw⟩ := (hexA u).1 hu0
  rw [← hw]
  clear hw hu0 hu
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul k a =>
      refine ⟨k • a, ?_⟩
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩

private theorem _root_.R3TwcIso.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "R3TwcIso" "includeRight_injective"

theorem includeLeftRingHom_injective (halg : Function.Injective (algebraMap K A)) :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) :=
  Algebra.TensorProduct.includeLeft_injective (S := K) halg

theorem exists_eq_algebraMap_of_tmul_one_eq_one_tmul (halg : Function.Injective (algebraMap K A))
    (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L)) {l : L} {a : A}
    (h : l ⊗ₜ[K] (1 : A) = (1 : L) ⊗ₜ[K] a) :
    ∃ k : K, l = algebraMap K L k ∧ a = algebraMap K A k := by
  have hσl : σ l = l := by
    have h1 : sigmaTensor K L A σ (l ⊗ₜ[K] (1 : A)) = l ⊗ₜ[K] (1 : A) := by
      rw [h, sigmaTensor_tmul, map_one]
    rw [sigmaTensor_tmul] at h1
    exact includeLeftRingHom_injective K L A halg h1
  obtain ⟨k, hk⟩ := hfix l hσl
  refine ⟨k, hk.symm, ?_⟩
  apply includeRight_injective K L A
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply, ← h, ← hk,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem sigmaTensor_sigmaTensor (τ : L ≃ₐ[K] L) (u : L ⊗[K] A) :
    sigmaTensor K L A σ (sigmaTensor K L A τ u) = sigmaTensor K L A (σ * τ) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.mul_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaTensor_iterate (r : ℕ) (u : L ⊗[K] A) :
    (sigmaTensor K L A σ)^[r] u = sigmaTensor K L A (σ ^ r) u := by
  induction r generalizing u with
  | zero =>
      rw [Function.iterate_zero, id, pow_zero]
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul l a => rw [sigmaTensor_tmul, AlgEquiv.one_apply]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, sigmaTensor_sigmaTensor, ← pow_succ']

theorem sigmaTensor_iterate_eq_self {n : ℕ} (hper : ∀ l : L, (⇑σ)^[n] l = l) (u : L ⊗[K] A) :
    (sigmaTensor K L A σ)^[n] u = u := by
  rw [sigmaTensor_iterate]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, AlgEquiv.coe_pow, hper]
  | add x y hx hy => rw [map_add, hx, hy]

end TensorFixed

section GLAlgebra

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem val_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := rfl

theorem val_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := rfl

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  apply Units.ext
  rw [val_sigmaGL, val_toTensorGL, Matrix.map_map]
  congr 1
  funext a
  exact sigmaTensor_includeRight K L A σ a

theorem toTensorGL_injective : Function.Injective (toTensorGL K L A) := by
  intro g h hgh
  apply Units.ext
  have := congrArg (fun u : GL (Fin 2) (L ⊗[K] A) => (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) hgh
  exact Matrix.map_injective (includeRight_injective K L A) this

theorem exists_toTensorGL_eq_of_fixed
    (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (g : GL (Fin 2) (L ⊗[K] A)) (hg : sigmaGL K L A σ g = g) :
    ∃ h : GL (Fin 2) A, toTensorGL K L A h = g := by
  set ι : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hι
  set φ : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ι.toRingHom.mapMatrix
    with hφ
  have hφinj : Function.Injective φ := fun M N h =>
    Matrix.map_injective (f := fun a : A => ι a) (includeRight_injective K L A) h
  have hginv : sigmaGL K L A σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hent : ∀ u : GL (Fin 2) (L ⊗[K] A), sigmaGL K L A σ u = u →
      ∀ i j, ∃ a : A, (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = ι a := by
    intro u hu i j
    have hij : sigmaTensor K L A σ ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) =
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j :=
      congrArg (fun w : GL (Fin 2) (L ⊗[K] A) => (w : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hu
    obtain ⟨a, ha⟩ := exists_eq_tmul_of_fixed K L A σ hfix _ hij
    exact ⟨a, ha⟩
  choose a ha using hent g hg
  choose b hb using hent g⁻¹ hginv
  have hA : φ (Matrix.of a) = (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j
    rw [ha i j]
    rfl
  have hB : φ (Matrix.of b) = ((g⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j
    rw [hb i j]
    rfl
  have h1 : Matrix.of a * Matrix.of b = 1 := hφinj (by
    rw [map_mul, map_one, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : Matrix.of b * Matrix.of a = 1 := hφinj (by
    rw [map_mul, map_one, hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  exact ⟨⟨Matrix.of a, Matrix.of b, h1, h2⟩, Units.ext hA⟩

theorem isRegularSemisimple_toTensorGL {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ) :
    IsRegularSemisimple (toTensorGL K L A γ) :=
  isRegularSemisimple_map _ hγ

theorem toTensorGL_scalar (z : Aˣ) :
    toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) : A →* L ⊗[K] A) z) :=
  map_scalar _ z

abbrev jL : GL (Fin 2) L →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)

theorem sigmaGL_jL (x : GL (Fin 2) L) :
    sigmaGL K L A σ (jL K L A x) = jL K L A (Matrix.GeneralLinearGroup.map (σ : L →+* L) x) := by
  apply Units.ext
  ext i j
  rw [val_sigmaGL, Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  change sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) L) i j ⊗ₜ[K] (1 : A)) =
    (σ : L →+* L) ((x : Matrix (Fin 2) (Fin 2) L) i j) ⊗ₜ[K] (1 : A)
  rw [sigmaTensor_tmul]
  rfl

theorem jL_map_algebraMap (w : GL (Fin 2) K) :
    jL K L A (Matrix.GeneralLinearGroup.map (algebraMap K L) w) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A) w) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, val_toTensorGL,
    Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply, Algebra.TensorProduct.includeRight_apply]
  change algebraMap K L ((w : Matrix (Fin 2) (Fin 2) K) i j) ⊗ₜ[K] (1 : A) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem jL_injective (halg : Function.Injective (algebraMap K A)) : Function.Injective (jL K L A) :=
  generalLinearGroup_map_injective _ (includeLeftRingHom_injective K L A halg)

theorem exists_map_algebraMap_eq_of_jL_eq_toTensorGL (halg : Function.Injective (algebraMap K A))
    (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    {w : GL (Fin 2) L} {S : GL (Fin 2) A} (h : jL K L A w = toTensorGL K L A S) :
    ∃ w₀ : GL (Fin 2) K, Matrix.GeneralLinearGroup.map (algebraMap K L) w₀ = w ∧
      Matrix.GeneralLinearGroup.map (algebraMap K A) w₀ = S := by
  have hent : ∀ (x : GL (Fin 2) L) (T : GL (Fin 2) A), jL K L A x = toTensorGL K L A T →
      ∀ i j, ∃ k : K, (x : Matrix (Fin 2) (Fin 2) L) i j = algebraMap K L k ∧
        (T : Matrix (Fin 2) (Fin 2) A) i j = algebraMap K A k := by
    intro x T hxT i j
    have hij := congrArg (fun u : GL (Fin 2) (L ⊗[K] A) => (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hxT
    simp only [Matrix.GeneralLinearGroup.map_apply, val_toTensorGL, Matrix.map_apply,
      Algebra.TensorProduct.includeRight_apply] at hij
    exact exists_eq_algebraMap_of_tmul_one_eq_one_tmul K L A σ halg hfix hij
  have hinv : jL K L A w⁻¹ = toTensorGL K L A S⁻¹ := by rw [map_inv, map_inv, h]
  choose k hk using hent w S h
  choose k' hk' using hent w⁻¹ S⁻¹ hinv
  have hK : (algebraMap K L).mapMatrix (Matrix.of k) = (w : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    exact (hk i j).1.symm
  have hK' : (algebraMap K L).mapMatrix (Matrix.of k') =
      ((w⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    exact (hk' i j).1.symm
  have hφinj : Function.Injective ((algebraMap K L).mapMatrix :
      Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) L) := fun M N hMN =>
    Matrix.map_injective (algebraMap K L).injective hMN
  have h1 : Matrix.of k * Matrix.of k' = 1 := hφinj (by
    rw [map_mul, map_one, hK, hK', ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : Matrix.of k' * Matrix.of k = 1 := hφinj (by
    rw [map_mul, map_one, hK, hK', ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨Matrix.of k, Matrix.of k', h1, h2⟩, Units.ext hK, Units.ext ?_⟩
  ext i j
  exact (hk i j).2.symm

variable [FiniteDimensional K L]

omit [FiniteDimensional K L] in

theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ =
      LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  rfl

omit [FiniteDimensional K L] in

theorem sigmaGL_iterate_eq_self (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g :=
  LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self
    (fun u => sigmaTensor_iterate_eq_self K L A σ hper u) g

omit [FiniteDimensional K L] in

theorem sigmaGL_normString (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A σ (normString K L A σ δ) = δ⁻¹ * normString K L A σ δ * δ := by
  rw [normString_eq_sigmaNormPow]
  exact LT.TwistedNorm.map_sigmaNormPow _ _ (sigmaGL_iterate_eq_self K L A σ hper δ)

omit [FiniteDimensional K L] in

theorem mul_sigmaPartialNorm_of_mem_twistedCentralizer {δ t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) (r : ℕ) :
    t * LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r =
      LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r * (⇑(sigmaGL K L A σ))^[r] t := by
  have h1 : t * δ = δ * sigmaGL K L A σ t := mul_inv_eq_iff_eq_mul.1 (mem_sigmaCentralizer_iff.1 ht)
  induction r with
  | zero => simp
  | succ r ih =>
      rw [LT.TwistedNorm.sigmaPartialNorm_succ', ← mul_assoc, h1, mul_assoc, ← map_mul, ih, map_mul,
        mul_assoc, Function.iterate_succ_apply']

omit [FiniteDimensional K L] in

theorem mul_normString_of_mem_twistedCentralizer (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    {δ t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ twistedCentralizer K L A σ δ) :
    t * normString K L A σ δ = normString K L A σ δ * t := by
  rw [normString_eq_sigmaNormPow, LT.TwistedNorm.sigmaNormPow_def,
    mul_sigmaPartialNorm_of_mem_twistedCentralizer K L A σ ht, sigmaGL_iterate_eq_self K L A σ hper]

omit [FiniteDimensional K L] in

theorem sigmaPartialNorm_mul_of_central {δ Z : GL (Fin 2) (L ⊗[K] A)} (hZ : ∀ g, g * Z = Z * g)
    (r : ℕ) :
    LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) (δ * Z) r =
      LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r *
        LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) Z r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [LT.TwistedNorm.sigmaPartialNorm_succ', LT.TwistedNorm.sigmaPartialNorm_succ',
        LT.TwistedNorm.sigmaPartialNorm_succ', ih, map_mul]
      calc δ * Z * (sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r) *
            sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) Z r))
          = δ * (Z * sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r)) *
            sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) Z r) := by group
        _ = δ * (sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r) * Z) *
            sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) Z r) := by
              rw [hZ]
        _ = δ * sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ r) *
            (Z * sigmaGL K L A σ (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) Z r)) := by group

omit [FiniteDimensional K L] in

theorem normString_mul_of_central {δ Z : GL (Fin 2) (L ⊗[K] A)} (hZ : ∀ g, g * Z = Z * g) :
    normString K L A σ (δ * Z) = normString K L A σ δ * normString K L A σ Z := by
  simp only [normString_eq_sigmaNormPow, LT.TwistedNorm.sigmaNormPow_def]
  exact sigmaPartialNorm_mul_of_central K L A σ hZ _

omit [FiniteDimensional K L] in

theorem normString_jL (x : GL (Fin 2) L) :
    normString K L A σ (jL K L A x) =
      jL K L A (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L))
        (Module.finrank K L) x) := by
  rw [normString_eq_sigmaNormPow]
  exact (LT.TwistedNorm.hom_sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L))
    (sigmaGL K L A σ) (jL K L A) (fun z => (sigmaGL_jL K L A σ z).symm) _ x).symm

end GLAlgebra

section Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in

theorem continuous_includeRight :
    Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  refine h.congr fun a => ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

omit [IsTopologicalRing A] in

theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A =>
    M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  exact continuous_id.matrix_map (continuous_includeRight K L A)

omit [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K L] in
open TensorProduct.RightActions in

theorem exists_retraction : ∃ r : (L ⊗[K] A) →ₗ[A] A, ∀ a : A, r ((1 : L) ⊗ₜ[K] a) = a := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hlam1 : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  refine ⟨(TensorProduct.AlgebraTensorModule.rid K A A).toLinearMap ∘ₗ
      (Module.TensorProduct.comm K A K).symm.toLinearMap ∘ₗ
      TensorProduct.RightActions.LinearMap.baseChange K L K A lam, fun a => ?_⟩
  simp [hlam1]

theorem isEmbedding_matrixMap :
    IsEmbedding (fun M : Matrix (Fin 2) (Fin 2) A =>
      M.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  obtain ⟨r, hr⟩ := exists_retraction K L A
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have hleft : Function.LeftInverse (fun N : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => N.map r)
      (fun M : Matrix (Fin 2) (Fin 2) A =>
        M.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) := by
    intro M
    ext i j
    exact hr (M i j)
  exact hleft.isEmbedding (continuous_id.matrix_map hrc)
    (continuous_id.matrix_map (continuous_includeRight K L A))

theorem isEmbedding_toTensorGL : IsEmbedding (toTensorGL K L A) := by
  haveI := isTopologicalRing_tensor K L A
  set φ : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := fun M =>
    M.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) with hφ
  have hφe : IsEmbedding φ := isEmbedding_matrixMap K L A
  have hφop : IsEmbedding (MulOpposite.op ∘ φ ∘ MulOpposite.unop :
      (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ → (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isEmbedding.comp (hφe.comp MulOpposite.opHomeomorph.symm.isEmbedding)
  have hcomp : IsEmbedding (Prod.map φ (MulOpposite.op ∘ φ ∘ MulOpposite.unop) ∘
      Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) :=
    (hφe.prodMap hφop).comp Units.isEmbedding_embedProduct
  have heq : (Prod.map φ (MulOpposite.op ∘ φ ∘ MulOpposite.unop) ∘
      Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) =
      Units.embedProduct (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) ∘ toTensorGL K L A := by
    funext u
    rfl
  rw [heq] at hcomp
  exact Units.isEmbedding_embedProduct.of_comp_iff.1 hcomp

end Topology

section Core

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {A : Type} [CommRing A] [Algebra K A] {σ : L ≃ₐ[K] L}
  (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
  (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
  {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ)
  {δ : GL (Fin 2) (L ⊗[K] A)} {y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y)

include hy in

theorem normString_eq_conj : normString K L A σ δ = y * toTensorGL K L A γ * y⁻¹ := by
  have h : toTensorGL K L A γ = y⁻¹ * normString K L A σ δ * y := hy
  rw [h]; group

include hper hy in

theorem zed_mem_centralizer :
    y⁻¹ * δ * sigmaGL K L A σ y ∈
      Subgroup.centralizer ({toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hN := normString_eq_conj (K := K) (L := L) (A := A) (σ := σ) hy
  have hσN := sigmaGL_normString K L A σ hper δ
  rw [hN, map_mul, map_mul, map_inv, sigmaGL_toTensorGL] at hσN

  have h1 : sigmaGL K L A σ y * toTensorGL K L A γ =
      δ⁻¹ * (y * toTensorGL K L A γ * y⁻¹) * δ * sigmaGL K L A σ y := by
    rw [← hσN]; group
  calc y⁻¹ * δ * sigmaGL K L A σ y * toTensorGL K L A γ
      = y⁻¹ * δ * (sigmaGL K L A σ y * toTensorGL K L A γ) := by group
    _ = y⁻¹ * δ * (δ⁻¹ * (y * toTensorGL K L A γ * y⁻¹) * δ * sigmaGL K L A σ y) := by rw [h1]
    _ = toTensorGL K L A γ * (y⁻¹ * δ * sigmaGL K L A σ y) := by group

include hper hy in

theorem conj_mem_centralizer {t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ twistedCentralizer K L A σ δ) :
    y⁻¹ * t * y ∈ Subgroup.centralizer ({toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hN := normString_eq_conj (K := K) (L := L) (A := A) (σ := σ) hy
  have htN := mul_normString_of_mem_twistedCentralizer K L A σ hper ht
  rw [hN] at htN
  calc y⁻¹ * t * y * toTensorGL K L A γ = y⁻¹ * (t * (y * toTensorGL K L A γ * y⁻¹)) * y := by group
    _ = y⁻¹ * (y * toTensorGL K L A γ * y⁻¹ * t) * y := by rw [htN]
    _ = toTensorGL K L A γ * (y⁻¹ * t * y) := by group

include hper hγ hy in

theorem sigmaGL_conj_eq {t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ twistedCentralizer K L A σ δ) :
    sigmaGL K L A σ (y⁻¹ * t * y) = y⁻¹ * t * y := by
  have hz := zed_mem_centralizer (K := K) (L := L) (A := A) (σ := σ) hper hy
  have hs := conj_mem_centralizer (K := K) (L := L) (A := A) (σ := σ) hper hy ht
  have hcomm := mul_comm_of_mem_centralizer (isRegularSemisimple_toTensorGL K L A hγ) hs hz
  have h1 : sigmaGL K L A σ t = δ⁻¹ * t * δ := by
    have h := mem_sigmaCentralizer_iff_fixed.1 ht
    calc sigmaGL K L A σ t = δ⁻¹ * (δ * sigmaGL K L A σ t * δ⁻¹) * δ := by group
      _ = δ⁻¹ * t * δ := by rw [h]
  rw [map_mul, map_mul, map_inv, h1]
  calc (sigmaGL K L A σ y)⁻¹ * (δ⁻¹ * t * δ) * sigmaGL K L A σ y
      = (y⁻¹ * δ * sigmaGL K L A σ y)⁻¹ * ((y⁻¹ * t * y) * (y⁻¹ * δ * sigmaGL K L A σ y)) := by group
    _ = (y⁻¹ * δ * sigmaGL K L A σ y)⁻¹ * ((y⁻¹ * δ * sigmaGL K L A σ y) * (y⁻¹ * t * y)) := by
          rw [hcomm]
    _ = y⁻¹ * t * y := by group

include hper hγ hy in

theorem conj_toTensorGL_mem_twistedCentralizer {S : GL (Fin 2) A}
    (hS : S ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    y * toTensorGL K L A S * y⁻¹ ∈ twistedCentralizer K L A σ δ := by
  have hz := zed_mem_centralizer (K := K) (L := L) (A := A) (σ := σ) hper hy
  have hS' : toTensorGL K L A S ∈
      Subgroup.centralizer ({toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hS ⊢
    rw [← map_mul, hS, map_mul]
  have hcomm := mul_comm_of_mem_centralizer (isRegularSemisimple_toTensorGL K L A hγ) hS' hz
  rw [mem_sigmaCentralizer_iff, map_mul, map_mul, map_inv, sigmaGL_toTensorGL]
  calc y * toTensorGL K L A S * y⁻¹ * δ * (sigmaGL K L A σ y * toTensorGL K L A S * (sigmaGL K L A σ y)⁻¹)⁻¹
      = y * (toTensorGL K L A S * (y⁻¹ * δ * sigmaGL K L A σ y)) * (toTensorGL K L A S)⁻¹ *
          (sigmaGL K L A σ y)⁻¹ := by group
    _ = y * ((y⁻¹ * δ * sigmaGL K L A σ y) * toTensorGL K L A S) * (toTensorGL K L A S)⁻¹ *
          (sigmaGL K L A σ y)⁻¹ := by rw [hcomm]
    _ = δ := by group

def psiHom (y : GL (Fin 2) (L ⊗[K] A))
    (hmem : ∀ S : GL (Fin 2) A, S ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →
      y * toTensorGL K L A S * y⁻¹ ∈ twistedCentralizer K L A σ δ) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →* twistedCentralizer K L A σ δ where
  toFun S := ⟨y * toTensorGL K L A (S : GL (Fin 2) A) * y⁻¹, hmem S S.2⟩
  map_one' := by
    apply Subtype.ext
    change y * toTensorGL K L A (1 : GL (Fin 2) A) * y⁻¹ = 1
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' S T := by
    apply Subtype.ext
    change y * toTensorGL K L A ((S : GL (Fin 2) A) * T) * y⁻¹ =
      (y * toTensorGL K L A (S : GL (Fin 2) A) * y⁻¹) * (y * toTensorGL K L A (T : GL (Fin 2) A) * y⁻¹)
    rw [map_mul]
    group

theorem coe_psiHom_apply (y : GL (Fin 2) (L ⊗[K] A))
    (hmem : ∀ S : GL (Fin 2) A, S ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →
      y * toTensorGL K L A S * y⁻¹ ∈ twistedCentralizer K L A σ δ)
    (S : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((psiHom (σ := σ) (δ := δ) y hmem S : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (S : GL (Fin 2) A) * y⁻¹ := rfl

include hper hfix hγ hy in
theorem psiHom_bijective
    (hmem : ∀ S : GL (Fin 2) A, S ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →
      y * toTensorGL K L A S * y⁻¹ ∈ twistedCentralizer K L A σ δ) :
    Function.Bijective (psiHom (σ := σ) (δ := δ) y hmem) := by
  constructor
  · intro S T hST
    apply Subtype.ext
    apply toTensorGL_injective K L A
    have h := congrArg (fun u : twistedCentralizer K L A σ δ => (u : GL (Fin 2) (L ⊗[K] A))) hST
    simp only [coe_psiHom_apply] at h
    exact mul_left_cancel (mul_right_cancel h)
  · rintro ⟨t, ht⟩
    obtain ⟨S, hS⟩ := exists_toTensorGL_eq_of_fixed K L A σ hfix (y⁻¹ * t * y)
      (sigmaGL_conj_eq (K := K) (L := L) (A := A) (σ := σ) hper hγ hy ht)
    have hSc : S ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) := by
      have h := conj_mem_centralizer (K := K) (L := L) (A := A) (σ := σ) hper hy ht
      rw [← hS, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at h
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact toTensorGL_injective K L A h
    refine ⟨⟨S, hSc⟩, Subtype.ext ?_⟩
    rw [coe_psiHom_apply]
    change y * toTensorGL K L A S * y⁻¹ = t
    rw [hS]
    group

def eIso [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] : twistedCentralizer K L A σ δ ≃ₜ*
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) :=
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  let ψ : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃* twistedCentralizer K L A σ δ :=
    MulEquiv.ofBijective (psiHom (σ := σ) (δ := δ) y
      (fun _ hS => conj_toTensorGL_mem_twistedCentralizer hper hγ hy hS))
      (psiHom_bijective hper hfix hγ hy _)
  have hψ : ∀ S, ((ψ S : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (S : GL (Fin 2) A) * y⁻¹ := fun _ => rfl
  have hψs : ∀ t, toTensorGL K L A ((ψ.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
      GL (Fin 2) A) = y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y := by
    intro t
    have h := congrArg (fun s : twistedCentralizer K L A σ δ => (s : GL (Fin 2) (L ⊗[K] A)))
      (ψ.apply_symm_apply t)
    simp only [hψ] at h
    rw [← h]
    group
  { ψ.symm with
    continuous_toFun := by
      change Continuous ψ.symm
      rw [continuous_induced_rng, (isEmbedding_toTensorGL K L A).isInducing.continuous_iff]
      have : toTensorGL K L A ∘ (Subtype.val ∘ ψ.symm) =
          fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y :=
        funext hψs
      rw [this]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    continuous_invFun := by
      change Continuous ψ
      apply Continuous.subtype_mk
      exact (continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul
        continuous_const }

theorem toTensorGL_eIso_apply [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A]
    (t : twistedCentralizer K L A σ δ) :
    toTensorGL K L A ((eIso hper hfix hγ hy t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
      GL (Fin 2) A) = y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y := by
  set ψ : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃* twistedCentralizer K L A σ δ :=
    MulEquiv.ofBijective (psiHom (σ := σ) (δ := δ) y
      (fun _ hS => conj_toTensorGL_mem_twistedCentralizer hper hγ hy hS))
      (psiHom_bijective hper hfix hγ hy _) with hψdef
  have hψ : ∀ S, ((ψ S : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (S : GL (Fin 2) A) * y⁻¹ := fun _ => rfl
  have he : (eIso hper hfix hγ hy t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) = ψ.symm t :=
    rfl
  have h := congrArg (fun s : twistedCentralizer K L A σ δ => (s : GL (Fin 2) (L ⊗[K] A)))
    (ψ.apply_symm_apply t)
  simp only [hψ] at h
  rw [he, ← h]
  group

include hper hγ hy in

theorem conj_eq_conj_of_isNormConjugator {y' : GL (Fin 2) (L ⊗[K] A)}
    (hy' : IsNormConjugator K L A σ γ δ y') {t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) : y⁻¹ * t * y = y'⁻¹ * t * y' := by
  have hs := conj_mem_centralizer (K := K) (L := L) (A := A) (σ := σ) hper hy ht
  have hm : y⁻¹ * y' ∈ Subgroup.centralizer ({toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hN := normString_eq_conj (K := K) (L := L) (A := A) (σ := σ) hy
    have hN' := normString_eq_conj (K := K) (L := L) (A := A) (σ := σ) hy'
    rw [hN'] at hN
    calc y⁻¹ * y' * toTensorGL K L A γ = y⁻¹ * (y' * toTensorGL K L A γ * y'⁻¹) * y' := by group
      _ = y⁻¹ * (y * toTensorGL K L A γ * y⁻¹) * y' := by rw [hN]
      _ = toTensorGL K L A γ * (y⁻¹ * y') := by group
  have hcomm := mul_comm_of_mem_centralizer (isRegularSemisimple_toTensorGL K L A hγ) hs hm
  calc y⁻¹ * t * y = (y⁻¹ * y')⁻¹ * ((y⁻¹ * y') * (y⁻¹ * t * y)) := by group
    _ = (y⁻¹ * y')⁻¹ * ((y⁻¹ * t * y) * (y⁻¹ * y')) := by rw [hcomm]
    _ = y'⁻¹ * t * y' := by group

end Core

section Rational

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {A : Type} [CommRing A] [Algebra K A] {σ : L ≃ₐ[K] L}

theorem isNormConjugator_jL (γ₀ : GL (Fin 2) K) (a : Kˣ) (u : Aˣ) (δ₀ P : GL (Fin 2) L)
    (c : (L ⊗[K] A)ˣ)
    (hN : P⁻¹ * LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L))
        (Module.finrank K L) δ₀ * P =
      Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀))
    (hc : normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) :
    IsNormConjugator K L A σ
      (Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u))
      (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) (jL K L A P) := by
  unfold IsNormConjugator
  rw [normString_mul_of_central K L A σ (fun g => mul_scalar_comm c g), hc, normString_jL,
    toTensorGL_scalar]
  set Z : GL (Fin 2) (L ⊗[K] A) := Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) : A →* L ⊗[K] A) u) with hZ
  have hcen : ∀ g, g * Z = Z * g := mul_scalar_comm
    (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) : A →* L ⊗[K] A) u)
  symm
  calc (jL K L A P)⁻¹ * (jL K L A (LT.TwistedNorm.sigmaNormPow
          (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ₀) * Z) * jL K L A P
      = (jL K L A P)⁻¹ * jL K L A (LT.TwistedNorm.sigmaNormPow
          (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ₀) * (Z * jL K L A P) := by
        group
    _ = (jL K L A P)⁻¹ * jL K L A (LT.TwistedNorm.sigmaNormPow
          (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ₀) * (jL K L A P * Z) := by
        rw [← hcen (jL K L A P)]
    _ = jL K L A (P⁻¹ * LT.TwistedNorm.sigmaNormPow
          (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ₀ * P) * Z := by
        rw [map_mul, map_mul, map_inv]; group
    _ = jL K L A (Matrix.GeneralLinearGroup.map (algebraMap K L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) * Z := by rw [hN]
    _ = toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀)) *
          toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
        rw [jL_map_algebraMap, hZ, toTensorGL_scalar]
    _ = toTensorGL K L A (Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u)) := by
        rw [← map_mul, map_mul (Matrix.GeneralLinearGroup.map (algebraMap K A)), map_scalar,
          ← mul_scalar_comm (Units.map (algebraMap K A : K →* A) a)
            (Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀), mul_assoc, ← map_mul]

variable (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
  (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
  (halg : Function.Injective (algebraMap K A))

include hfix halg in

theorem rational_iff (γ₀ : GL (Fin 2) K) (zA : Aˣ) (δ₀ P : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ)
    {t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))
    {S : GL (Fin 2) A}
    (hS : S ∈ Subgroup.centralizer ({Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) zA} : Set (GL (Fin 2) A)))
    (he : toTensorGL K L A S = (jL K L A P)⁻¹ * t * jL K L A P) :
    S ∈ (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
        (Matrix.GeneralLinearGroup.map (algebraMap K A)) ↔
      t ∈ (sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (jL K L A) := by
  have hcen := mul_scalar_comm c
  constructor
  · rintro ⟨w₀, hw₀, rfl⟩
    refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap K L) w₀ * P⁻¹, ?_, ?_⟩
    ·
      have ht' := mem_sigmaCentralizer_iff.1 ht
      change _ ∈ sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀
      rw [mem_sigmaCentralizer_iff]
      apply jL_injective K L A halg
      have hteq : t = jL K L A (P * Matrix.GeneralLinearGroup.map (algebraMap K L) w₀ * P⁻¹) := by
        rw [map_mul, map_mul, map_inv, jL_map_algebraMap, he]; group
      rw [hteq, sigmaGL_jL] at ht'
      set t₀ := P * Matrix.GeneralLinearGroup.map (algebraMap K L) w₀ * P⁻¹
      rw [map_mul, map_mul, map_inv]
      calc jL K L A t₀ * jL K L A δ₀ * (jL K L A (Matrix.GeneralLinearGroup.map (σ : L →+* L) t₀))⁻¹
          = jL K L A t₀ * jL K L A δ₀ *
              ((jL K L A (Matrix.GeneralLinearGroup.map (σ : L →+* L) t₀))⁻¹ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ := by group
        _ = jL K L A t₀ * jL K L A δ₀ *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c *
                (jL K L A (Matrix.GeneralLinearGroup.map (σ : L →+* L) t₀))⁻¹) *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ := by
                rw [hcen ((jL K L A (Matrix.GeneralLinearGroup.map (σ : L →+* L) t₀))⁻¹)]
        _ = jL K L A t₀ * (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
              (jL K L A (Matrix.GeneralLinearGroup.map (σ : L →+* L) t₀))⁻¹ *
              (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ := by group
        _ = jL K L A δ₀ := by rw [ht']; group
    · rw [map_mul, map_mul, map_inv, jL_map_algebraMap, he]; group
  · rintro ⟨t₀, ht₀, rfl⟩
    have hw : jL K L A (P⁻¹ * t₀ * P) = toTensorGL K L A S := by
      rw [he, map_mul, map_mul, map_inv]
    obtain ⟨w₀, hw₀L, hw₀A⟩ := exists_map_algebraMap_eq_of_jL_eq_toTensorGL K L A σ halg hfix hw
    refine ⟨w₀, ?_, hw₀A⟩

    rw [centralizer_mul_scalar, Subgroup.mem_centralizer_singleton_iff, ← hw₀A, ← map_mul,
      ← map_mul] at hS
    change w₀ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact generalLinearGroup_map_injective _ halg hS

end Rational

section Measures

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

theorem coupled_map_symm (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (e : twistedCentralizer K L A σ δ ≃ₜ* Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (he : ∀ t, toTensorGL K L A ((e t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
      GL (Fin 2) A) = y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    Coupled K L A σ γ δ y τ
      (@Measure.map _ _ (centralizerBorel A γ) (twistedCentralizerBorel K L A σ δ) e.symm τ) := by
  letI mE : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  letI mC : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  letI mT : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  have hcj : Measurable fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  show Measure.map (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y)
      (Measure.map e.symm τ) =
    Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      toTensorGL K L A (t : GL (Fin 2) A)) τ
  rw [Measure.map_map hcj hes]
  congr 1
  funext s
  simp only [Function.comp_apply]
  rw [← he (e.symm s), ContinuousMulEquiv.apply_symm_apply]

end Measures

section General

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

theorem main_general
    (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (halg : Function.Injective (algebraMap K A))
    (γ₀ : GL (Fin 2) K) (hγ₀ : IsRegularSemisimple γ₀) (a : Kˣ) (u : Aˣ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ)
    (hN : LT.TwistedNorm.IsNormRep σ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) δ₀)
    (hc : normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) u))
    (y : GL (Fin 2) (L ⊗[K] A))
    (hy : IsNormConjugator K L A σ
      (Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u))
      (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) y) :
    ∃ e : twistedCentralizer K L A σ (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ*
        Subgroup.centralizer ({Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u)} :
          Set (GL (Fin 2) A)),
      (∀ t, toTensorGL K L A ((e t : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u)} :
            Set (GL (Fin 2) A))) : GL (Fin 2) A) =
        y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) ∧
      (∀ t, ((e t : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u)} :
            Set (GL (Fin 2) A))) : GL (Fin 2) A) ∈
          (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map
            (Matrix.GeneralLinearGroup.map (algebraMap K A)) ↔
        (t : GL (Fin 2) (L ⊗[K] A)) ∈
          (sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (jL K L A)) ∧
      (∀ τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u)} :
            Set (GL (Fin 2) A))) (centralizerBorel A _),
        Coupled K L A σ
          (Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u))
          (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) y τ
          (@Measure.map _ _ (centralizerBorel A _)
            (twistedCentralizerBorel K L A σ (jL K L A δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))
            e.symm τ)) := by

  have hγ : IsRegularSemisimple (Matrix.GeneralLinearGroup.map (algebraMap K A) γ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K A : K →* A) a * u)) :=
    isRegularSemisimple_mul_scalar (isRegularSemisimple_map _ hγ₀) _

  obtain ⟨P, hP⟩ := hN
  have hy₁ := isNormConjugator_jL (K := K) (L := L) (A := A) (σ := σ) γ₀ a u δ₀ P c hP hc
  refine ⟨eIso hper hfix hγ hy, toTensorGL_eIso_apply hper hfix hγ hy, fun t => ?_, fun τ => ?_⟩
  ·
    apply rational_iff hfix halg γ₀ _ δ₀ P c t.2 (eIso hper hfix hγ hy t).2
    rw [toTensorGL_eIso_apply]
    exact conj_eq_conj_of_isNormConjugator hper hγ hy hy₁ t.2
  ·
    exact coupled_map_symm K L A σ _ _ y (eIso hper hfix hγ hy) (toTensorGL_eIso_apply hper hfix hγ hy) τ

end General

section Main

theorem algebraMap_adeleRing_injective (K : Type) [Field K] [NumberField K] :
    Function.Injective (algebraMap K (AdeleRing (𝓞 K) K)) := by
  haveI : Nontrivial (AdeleRing (𝓞 K) K) :=
    inferInstanceAs (Nontrivial (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  exact (algebraMap K (AdeleRing (𝓞 K) K)).injective

end Main

end R3TwcIso

end

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open R3TwcIso in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ₀ : GL (Fin 2) K) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN : LT.TwistedNorm.IsNormRep σ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) δ₀)
    (hc : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ
      (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) y) :
    ∃ e : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ*
        Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      (∀ t, AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
          ((e t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
            Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) : AutomorphicForm.AdelicGL2 (𝓞 K) K) =
        y⁻¹ * (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * y) ∧
      (∀ t, ((e t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
            Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) : AutomorphicForm.AdelicGL2 (𝓞 K) K) ∈
          (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K) ↔
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          (AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))) ∧
      (∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) y τ
          (@Measure.map _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))
            e.symm τ)) :=
  main_general K L (AdeleRing (𝓞 K) K) σ
    (LT.TwistedNorm.iterate_finrank_apply_of_generator hgen)
    (fun _ hl => LT.TwistedNorm.mem_range_algebraMap_of_generator_apply_eq hgen hl)
    (algebraMap_adeleRing_injective K) γ₀ hγ₀ a u δ₀ c hN hc y hy

end S_AutomorphicForm_exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep (solution)
