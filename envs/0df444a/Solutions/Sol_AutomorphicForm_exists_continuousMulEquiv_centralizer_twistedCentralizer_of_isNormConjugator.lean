-- Prove2me | solution 1 for AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/aa6ed381-9a57-5b4c-b55d-a8cfffa621c8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator

set_option autoImplicit false

open TopologicalSpace Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor isTopologicalGroup_tensorGL toTensorGL sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer IsRegularSemisimple mem_sigmaCentralizer_iff mem_sigmaCentralizer_iff_fixed"
namespace NormConjugatorIso
p2m_open "AutomorphicForm"

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator.AutomorphicForm"

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

private theorem _root_.AutomorphicForm.NormConjugatorIso.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "AutomorphicForm.NormConjugatorIso" "includeRight_injective"

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

def psiIso [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* twistedCentralizer K L A σ δ :=
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
  { ψ with
    continuous_toFun := by
      change Continuous ψ
      apply Continuous.subtype_mk
      exact (continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul
        continuous_const
    continuous_invFun := by
      change Continuous ψ.symm
      rw [continuous_induced_rng, (isEmbedding_toTensorGL K L A).isInducing.continuous_iff]
      have : toTensorGL K L A ∘ (Subtype.val ∘ ψ.symm) =
          fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y :=
        funext hψs
      rw [this]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const }

theorem coe_psiIso_apply [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A]
    (s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((psiIso hper hfix hγ hy s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := rfl

end Core

end AutomorphicForm.NormConjugatorIso

end

open AutomorphicForm.NormConjugatorIso in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] A)) (hy : AutomorphicForm.IsNormConjugator K L A σ γ δ y) :
    ∃ e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* AutomorphicForm.twistedCentralizer K L A σ δ,
      ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
        ((e s : AutomorphicForm.twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
          y * AutomorphicForm.toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ :=
  ⟨psiIso (LT.TwistedNorm.iterate_finrank_apply_of_generator hσ)
      (fun _ hl => LT.TwistedNorm.mem_range_algebraMap_of_generator_apply_eq hσ hl) hγ hy,
    fun _ => rfl⟩

end S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator (solution)
