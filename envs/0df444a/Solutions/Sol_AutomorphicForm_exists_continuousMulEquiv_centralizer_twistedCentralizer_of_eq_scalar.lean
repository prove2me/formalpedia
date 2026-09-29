-- Prove2me | solution 1 for AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4152c2c4-e2c7-5764-bfed-5952437ef27d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar

set_option autoImplicit false

open TensorProduct Topology
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor isTopologicalGroup_tensorGL toTensorGL sigmaTensor sigmaGL twistedCentralizer sigmaCentralizer mem_sigmaCentralizer_iff"
namespace CentralPsi
p2m_open "AutomorphicForm"

section Scalars

variable {R : Type*} [CommRing R]

theorem scalar_mul_comm (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem centralizer_scalar_eq_top (c : Rˣ) :
    Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) R)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (scalar_mul_comm c g).symm

end Scalars

section Tensor

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

theorem exists_eq_tmul_of_fixed (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (u : L ⊗[K] A) (hu : sigmaTensor K L A σ u = u) : ∃ a : A, u = (1 : L) ⊗ₜ[K] a := by
  have hex : Function.Exact (Algebra.linearMap K L) (σ.toLinearMap - LinearMap.id : L →ₗ[K] L) := by
    intro l
    constructor
    · intro hl
      have : σ l - l = 0 := hl
      exact hfix l (sub_eq_zero.1 this)
    · rintro ⟨k, rfl⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Algebra.linearMap_apply,
        AlgEquiv.toLinearMap_apply, AlgEquiv.commutes, sub_self]
  have hexA := Module.Flat.rTensor_exact A hex
  have hu0 : ((σ.toLinearMap - LinearMap.id).rTensor A) u = 0 := by rw [rTensor_sub_apply, hu, sub_self]
  obtain ⟨w, hw⟩ := (hexA u).1 hu0
  rw [← hw]
  clear hw hu0 hu
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul k a =>
      refine ⟨k • a, ?_⟩
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩

private theorem _root_.AutomorphicForm.CentralPsi.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "AutomorphicForm.CentralPsi" "includeRight_injective"
theorem val_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := rfl

theorem val_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := rfl

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) : sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
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

theorem exists_toTensorGL_eq_of_fixed (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (g : GL (Fin 2) (L ⊗[K] A)) (hg : sigmaGL K L A σ g = g) : ∃ h : GL (Fin 2) A, toTensorGL K L A h = g := by
  set ι : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hι
  set φ : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ι.toRingHom.mapMatrix with hφ
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
    ext i j; rw [ha i j]; rfl
  have hB : φ (Matrix.of b) = ((g⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    ext i j; rw [hb i j]; rfl
  have h1 : Matrix.of a * Matrix.of b = 1 := hφinj (by
    rw [map_mul, map_one, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : Matrix.of b * Matrix.of a = 1 := hφinj (by
    rw [map_mul, map_one, hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  exact ⟨⟨Matrix.of a, Matrix.of b, h1, h2⟩, Units.ext hA⟩

end Tensor

section EmbedTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem continuous_includeRight : Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  refine h.congr fun a => ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

omit [IsTopologicalRing A] in
theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A => M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
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
    IsEmbedding (fun M : Matrix (Fin 2) (Fin 2) A => M.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  obtain ⟨r, hr⟩ := exists_retraction K L A
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have hleft : Function.LeftInverse (fun N : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => N.map r)
      (fun M : Matrix (Fin 2) (Fin 2) A => M.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)) := by
    intro M; ext i j; exact hr (M i j)
  exact hleft.isEmbedding (continuous_id.matrix_map hrc) (continuous_id.matrix_map (continuous_includeRight K L A))

theorem isEmbedding_toTensorGL : IsEmbedding (toTensorGL K L A) := by
  haveI := isTopologicalRing_tensor K L A
  set φ : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := fun M =>
    M.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) with hφ
  have hφe : IsEmbedding φ := isEmbedding_matrixMap K L A
  have hφop : IsEmbedding (MulOpposite.op ∘ φ ∘ MulOpposite.unop :
      (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ → (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isEmbedding.comp (hφe.comp MulOpposite.opHomeomorph.symm.isEmbedding)
  have hcomp : IsEmbedding (Prod.map φ (MulOpposite.op ∘ φ ∘ MulOpposite.unop) ∘ Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) :=
    (hφe.prodMap hφop).comp Units.isEmbedding_embedProduct
  have heq : (Prod.map φ (MulOpposite.op ∘ φ ∘ MulOpposite.unop) ∘ Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) =
      Units.embedProduct (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) ∘ toTensorGL K L A := by
    funext u; rfl
  rw [heq] at hcomp
  exact Units.isEmbedding_embedProduct.of_comp_iff.1 hcomp

end EmbedTopology

section Psi

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {A : Type} [CommRing A] [Algebra K A] {σ : L ≃ₐ[K] L}
  (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
  {γ : GL (Fin 2) A} (hγ : ∃ r : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) r)
  {δ y : GL (Fin 2) (L ⊗[K] A)} {ζ : (L ⊗[K] A)ˣ}
  (hζ : y⁻¹ * δ * sigmaGL K L A σ y = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ)

theorem mem_sigmaCentralizer_conj_iff {G : Type*} [Group G] (θ : G →* G) (d w t : G) :
    t ∈ sigmaCentralizer θ d ↔ w⁻¹ * t * w ∈ sigmaCentralizer θ (w⁻¹ * d * θ w) := by
  rw [mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc w⁻¹ * t * w * (w⁻¹ * d * θ w) * ((θ w)⁻¹ * θ t * θ w)⁻¹
        = w⁻¹ * (t * d * (θ t)⁻¹) * θ w := by group
      _ = w⁻¹ * d * θ w := by rw [h]
  · intro h
    calc t * d * (θ t)⁻¹ = w * (w⁻¹ * t * w * (w⁻¹ * d * θ w) * ((θ w)⁻¹ * θ t * θ w)⁻¹) * (θ w)⁻¹ := by group
      _ = w * (w⁻¹ * d * θ w) * (θ w)⁻¹ := by rw [h]
      _ = d := by group

theorem mem_sigmaCentralizer_central_iff {G : Type*} [Group G] (θ : G →* G) (s X : G)
    (hs : ∀ g : G, s * g = g * s) : X ∈ sigmaCentralizer θ s ↔ θ X = X := by
  rw [mem_sigmaCentralizer_iff, (hs X).symm, mul_assoc, mul_eq_left, mul_inv_eq_one, eq_comm]

include hζ in

theorem mem_twistedCentralizer_iff_fixed (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ twistedCentralizer K L A σ δ ↔ sigmaGL K L A σ (y⁻¹ * t * y) = y⁻¹ * t * y := by
  show t ∈ sigmaCentralizer (sigmaGL K L A σ) δ ↔ _
  rw [mem_sigmaCentralizer_conj_iff (sigmaGL K L A σ) δ y t, hζ,
    mem_sigmaCentralizer_central_iff _ _ _ (scalar_mul_comm ζ)]

include hζ in
theorem conj_toTensorGL_mem_twistedCentralizer (s : GL (Fin 2) A) :
    y * toTensorGL K L A s * y⁻¹ ∈ twistedCentralizer K L A σ δ := by
  rw [mem_twistedCentralizer_iff_fixed hζ]
  have : y⁻¹ * (y * toTensorGL K L A s * y⁻¹) * y = toTensorGL K L A s := by group
  rw [this, sigmaGL_toTensorGL]

def psiHom : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →* twistedCentralizer K L A σ δ where
  toFun s := ⟨y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹, conj_toTensorGL_mem_twistedCentralizer hζ _⟩
  map_one' := by
    apply Subtype.ext
    change y * toTensorGL K L A (1 : GL (Fin 2) A) * y⁻¹ = 1
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' s t := by
    apply Subtype.ext
    change y * toTensorGL K L A ((s : GL (Fin 2) A) * t) * y⁻¹ =
      (y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹) * (y * toTensorGL K L A (t : GL (Fin 2) A) * y⁻¹)
    rw [map_mul]; group

theorem coe_psiHom_apply (s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((psiHom hζ s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := rfl

include hfix hγ in
theorem psiHom_bijective : Function.Bijective (psiHom (γ := γ) hζ) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    apply toTensorGL_injective K L A
    have h := congrArg (fun u : twistedCentralizer K L A σ δ => (u : GL (Fin 2) (L ⊗[K] A))) hst
    simp only [coe_psiHom_apply] at h
    exact mul_left_cancel (mul_right_cancel h)
  · rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ := exists_toTensorGL_eq_of_fixed K L A σ hfix (y⁻¹ * t * y)
      ((mem_twistedCentralizer_iff_fixed hζ t).1 ht)
    obtain ⟨r, rfl⟩ := hγ
    refine ⟨⟨s, by rw [centralizer_scalar_eq_top]; trivial⟩, Subtype.ext ?_⟩
    rw [coe_psiHom_apply]
    change y * toTensorGL K L A s * y⁻¹ = t
    rw [hs]; group

def psiIso [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* twistedCentralizer K L A σ δ :=
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  let ψ : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃* twistedCentralizer K L A σ δ :=
    MulEquiv.ofBijective (psiHom hζ) (psiHom_bijective hfix hγ hζ)
  have hψ : ∀ s, ((ψ s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := fun _ => rfl
  have hψs : ∀ t, toTensorGL K L A ((ψ.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A) =
      y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y := by
    intro t
    have h := congrArg (fun s : twistedCentralizer K L A σ δ => (s : GL (Fin 2) (L ⊗[K] A))) (ψ.apply_symm_apply t)
    simp only [hψ] at h
    rw [← h]; group
  { ψ with
    continuous_toFun := by
      change Continuous ψ
      apply Continuous.subtype_mk
      exact (continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul continuous_const
    continuous_invFun := by
      change Continuous ψ.symm
      rw [continuous_induced_rng, (isEmbedding_toTensorGL K L A).isInducing.continuous_iff]
      have : toTensorGL K L A ∘ (Subtype.val ∘ ψ.symm) =
          fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y := funext hψs
      rw [this]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const }

theorem coe_psiIso_apply [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A]
    (s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((psiIso hfix hγ hζ s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      y * toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := rfl

end Psi

end AutomorphicForm.CentralPsi

end

open AutomorphicForm.CentralPsi in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] A)) (ζ : (L ⊗[K] A)ˣ)
    (hζ : y⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ y = Matrix.GeneralLinearGroup.scalar (Fin 2) ζ) :
    ∃ e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* AutomorphicForm.twistedCentralizer K L A σ δ,
      ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
        ((e s : AutomorphicForm.twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
          y * AutomorphicForm.toTensorGL K L A (s : GL (Fin 2) A) * y⁻¹ := by
  have hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L) := fun l hl =>
    LT.TwistedNorm.mem_range_algebraMap_of_generator_apply_eq hσ hl
  exact ⟨psiIso hfix hγ hζ, fun s => coe_psiIso_apply hfix hγ hζ s⟩

end S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar (solution)
