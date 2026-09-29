-- Prove2me | solution 1 for AutomorphicForm.exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9d30b0d0-b4a1-5239-8690-7834f027adeb

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure NumberField IsDedekindDomain TopologicalSpace Topology
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace R1NormConjCoupled

open AutomorphicForm

section FieldTheory

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem sigma_sq_and_fixed (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l, σ (σ l) = l) ∧ (∀ l, σ l = l → l ∈ Set.range (algebraMap K L)) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  have hord : orderOf σ = 2 := (orderOf_eq_card_of_forall_mem_zpowers hgen).trans hcard
  have hsq : σ * σ = 1 := by rw [← pow_two, ← hord]; exact pow_orderOf_eq_one σ
  refine ⟨fun l => ?_, fun l hl => ?_⟩
  · rw [← AlgEquiv.mul_apply, hsq, AlgEquiv.one_apply]
  · rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen f)
    have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) l := hl
    exact (Subgroup.zpowers_le.2 hmem) (Subgroup.zpow_mem_zpowers σ k)

end FieldTheory

section TensorFixed

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) : sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sigmaTensor]

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  rw [Algebra.TensorProduct.includeRight_apply, sigmaTensor_tmul, map_one]

theorem sigmaTensor_sigmaTensor (hσ : ∀ l, σ (σ l) = l) (u : L ⊗[K] A) :
    sigmaTensor K L A σ (sigmaTensor K L A σ u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

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

private theorem _root_.R1NormConjCoupled.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "R1NormConjCoupled" "includeRight_injective"
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

theorem sigmaGL_sigmaGL (hσ : ∀ l, σ (σ l) = l) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A σ (sigmaGL K L A σ g) = g :=
  Units.ext (Matrix.ext fun _ _ => sigmaTensor_sigmaTensor K L A σ hσ _)

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

theorem normString_of_finrank_eq_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = δ * sigmaGL K L A σ δ := by
  unfold normString
  rw [h2]
  simp [List.range_succ]

theorem mul_scalar_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) c = Matrix.GeneralLinearGroup.scalar (Fin 2) c * g := by
  apply Units.ext
  simp only [Units.val_mul]
  have : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  rw [this]
  exact ((Matrix.scalar_commute (c : R) (fun r' => mul_comm _ _) (g : Matrix (Fin 2) (Fin 2) R)).eq).symm

variable {K L A σ}

theorem conj_toTensorGL_mem_twistedCentralizer {δ x Z : GL (Fin 2) (L ⊗[K] A)}
    (hZc : ∀ g, g * Z = Z * g) (hδ : δ = x * Z * (sigmaGL K L A σ x)⁻¹) (g : GL (Fin 2) A) :
    x * toTensorGL K L A g * x⁻¹ ∈ twistedCentralizer K L A σ δ := by
  rw [twistedCentralizer, mem_sigmaCentralizer_iff, map_mul, map_mul, map_inv, sigmaGL_toTensorGL, hδ]
  calc x * toTensorGL K L A g * x⁻¹ * (x * Z * (sigmaGL K L A σ x)⁻¹) *
        (sigmaGL K L A σ x * toTensorGL K L A g * (sigmaGL K L A σ x)⁻¹)⁻¹
      = x * (toTensorGL K L A g * Z) * (toTensorGL K L A g)⁻¹ * (sigmaGL K L A σ x)⁻¹ := by group
    _ = x * Z * (sigmaGL K L A σ x)⁻¹ := by rw [hZc (toTensorGL K L A g)]; group

theorem sigmaGL_conj_eq_of_mem_twistedCentralizer {δ x Z : GL (Fin 2) (L ⊗[K] A)}
    (hZc : ∀ g, g * Z = Z * g) (hδ : δ = x * Z * (sigmaGL K L A σ x)⁻¹)
    {t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ twistedCentralizer K L A σ δ) :
    sigmaGL K L A σ (x⁻¹ * t * x) = x⁻¹ * t * x := by
  have h1 : t * δ = δ * sigmaGL K L A σ t :=
    mul_inv_eq_iff_eq_mul.1 (mem_sigmaCentralizer_iff.1 ht)
  rw [hδ] at h1
  have h2 : Z * sigmaGL K L A σ (x⁻¹ * t * x) = Z * (x⁻¹ * t * x) := by
    rw [map_mul, map_mul, map_inv]
    calc Z * ((sigmaGL K L A σ x)⁻¹ * sigmaGL K L A σ t * sigmaGL K L A σ x)
        = x⁻¹ * (x * Z * (sigmaGL K L A σ x)⁻¹ * sigmaGL K L A σ t) * sigmaGL K L A σ x := by group
      _ = x⁻¹ * (t * (x * Z * (sigmaGL K L A σ x)⁻¹)) * sigmaGL K L A σ x := by rw [h1]
      _ = x⁻¹ * t * x * Z := by group
      _ = Z * (x⁻¹ * t * x) := hZc _
  exact mul_left_cancel h2

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

omit [IsTopologicalRing A] in

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (sigmaTensor K L A σ) := by
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

omit [IsTopologicalRing A] in

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (sigmaGL K L A σ) := by
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact isClosed_singleton.preimage hc

omit [IsTopologicalRing A] in

theorem secondCountableTopology_GL {R : Type} [CommRing R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

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

section AlgebraPack

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem algebra_pack (hσσ : ∀ l, σ (σ l) = l) (h2 : Module.finrank K L = 2)
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) (hδ : IsNormConjugator K L A σ γ δ y)
    (z : (L ⊗[K] A)ˣ) (x : GL (Fin 2) (L ⊗[K] A))
    (hx : Matrix.GeneralLinearGroup.scalar (Fin 2) z = x⁻¹ * δ * sigmaGL K L A σ x) :
    IsNormConjugator K L A σ γ δ x ∧
      (∀ g : GL (Fin 2) A, g ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) ∧
      (∀ g : GL (Fin 2) A, x * toTensorGL K L A g * x⁻¹ ∈ twistedCentralizer K L A σ δ) ∧
      (∀ t : GL (Fin 2) (L ⊗[K] A), t ∈ twistedCentralizer K L A σ δ →
        sigmaGL K L A σ (x⁻¹ * t * x) = x⁻¹ * t * x) := by
  have hSS : ∀ g : GL (Fin 2) (L ⊗[K] A), sigmaGL K L A σ (sigmaGL K L A σ g) = g :=
    sigmaGL_sigmaGL K L A σ hσσ
  set S := sigmaGL K L A σ with hS
  set Z : GL (Fin 2) (L ⊗[K] A) := Matrix.GeneralLinearGroup.scalar (Fin 2) z with hZ
  have hZc : ∀ g, g * Z = Z * g := fun g => mul_scalar_comm z g
  have hSZc : ∀ g, g * S Z = S Z * g := by
    intro g
    calc g * S Z = S (S g) * S Z := by rw [hSS]
      _ = S (S g * Z) := by rw [map_mul]
      _ = S (Z * S g) := by rw [hZc]
      _ = S Z * g := by rw [map_mul, hSS]
  set W : GL (Fin 2) (L ⊗[K] A) := Z * S Z with hW
  have hWc : ∀ g, g * W = W * g := by
    intro g
    calc g * (Z * S Z) = Z * g * S Z := by rw [← mul_assoc, hZc]
      _ = Z * (S Z * g) := by rw [mul_assoc, hSZc]
      _ = Z * S Z * g := by rw [mul_assoc]
  have hδeq : δ = x * Z * (S x)⁻¹ := by
    rw [hx]; group

  have hN : normString K L A σ δ = W := by
    rw [normString_of_finrank_eq_two K L A σ h2, hδeq, ← hS, map_mul, map_mul, map_inv, hSS]
    calc x * Z * (S x)⁻¹ * (S x * S Z * x⁻¹) = x * (Z * S Z) * x⁻¹ := by group
      _ = Z * S Z * x * x⁻¹ := by rw [hWc x]
      _ = Z * S Z := by group

  have hγW : toTensorGL K L A γ = W := by
    have h := hδ
    unfold IsNormConjugator at h
    rw [hN] at h
    rw [h]
    calc y⁻¹ * W * y = y⁻¹ * (W * y) := mul_assoc _ _ _
      _ = y⁻¹ * (y * W) := by rw [hWc y]
      _ = W := by group
  refine ⟨?_, fun g => ?_, fun g => conj_toTensorGL_mem_twistedCentralizer hZc hδeq g,
    fun t ht => sigmaGL_conj_eq_of_mem_twistedCentralizer hZc hδeq ht⟩
  ·
    unfold IsNormConjugator
    rw [hN, hγW]
    calc W = x⁻¹ * (x * W) := by group
      _ = x⁻¹ * (W * x) := by rw [hWc x]
      _ = x⁻¹ * W * x := (mul_assoc _ _ _).symm
  ·
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply toTensorGL_injective K L A
    rw [map_mul, map_mul, hγW]
    exact hWc _

end AlgebraPack

section Psi

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  {A : Type} [CommRing A] [Algebra K A] {σ : L ≃ₐ[K] L}
  (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A)) (x : GL (Fin 2) (L ⊗[K] A))
  (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
  (hcent : ∀ g : GL (Fin 2) A, g ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
  (hmemT : ∀ g : GL (Fin 2) A, x * toTensorGL K L A g * x⁻¹ ∈ twistedCentralizer K L A σ δ)
  (hfixT : ∀ t : GL (Fin 2) (L ⊗[K] A), t ∈ twistedCentralizer K L A σ δ →
    sigmaGL K L A σ (x⁻¹ * t * x) = x⁻¹ * t * x)

def psiHom : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) →* twistedCentralizer K L A σ δ where
  toFun t := ⟨x * toTensorGL K L A (t : GL (Fin 2) A) * x⁻¹, hmemT t⟩
  map_one' := by
    apply Subtype.ext
    change x * toTensorGL K L A (1 : GL (Fin 2) A) * x⁻¹ = 1
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' s t := by
    apply Subtype.ext
    change x * toTensorGL K L A ((s : GL (Fin 2) A) * t) * x⁻¹ =
      (x * toTensorGL K L A (s : GL (Fin 2) A) * x⁻¹) * (x * toTensorGL K L A (t : GL (Fin 2) A) * x⁻¹)
    rw [map_mul]
    group

include hfix hcent hfixT in
theorem psiHom_bijective : Function.Bijective (psiHom (σ := σ) γ δ x hmemT) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    apply toTensorGL_injective K L A
    have h := congrArg (fun u : twistedCentralizer K L A σ δ => (u : GL (Fin 2) (L ⊗[K] A))) hst
    exact mul_left_cancel (mul_right_cancel h)
  · rintro ⟨t, ht⟩
    obtain ⟨g, hg⟩ := exists_toTensorGL_eq_of_fixed K L A σ hfix (x⁻¹ * t * x) (hfixT t ht)
    refine ⟨⟨g, hcent g⟩, Subtype.ext ?_⟩
    change x * toTensorGL K L A g * x⁻¹ = t
    rw [hg]
    group

def psi : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃* twistedCentralizer K L A σ δ :=
  MulEquiv.ofBijective (psiHom γ δ x hmemT) (psiHom_bijective γ δ x hfix hcent hmemT hfixT)

theorem coe_psi_apply (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((psi γ δ x hfix hcent hmemT hfixT t : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      x * toTensorGL K L A (t : GL (Fin 2) A) * x⁻¹ := rfl

theorem toTensorGL_psi_symm_apply (t : twistedCentralizer K L A σ δ) :
    toTensorGL K L A (((psi γ δ x hfix hcent hmemT hfixT).symm t :
        Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A) =
      x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x := by
  have h := congrArg (fun s : twistedCentralizer K L A σ δ => (s : GL (Fin 2) (L ⊗[K] A)))
    ((psi γ δ x hfix hcent hmemT hfixT).apply_symm_apply t)
  simp only [coe_psi_apply] at h
  rw [← h]
  group

variable [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_psi : Continuous (psi γ δ x hfix hcent hmemT hfixT) := by
  haveI := isTopologicalRing_tensor K L A
  apply Continuous.subtype_mk
  exact (continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul
    continuous_const

theorem continuous_psi_symm : Continuous (psi γ δ x hfix hcent hmemT hfixT).symm := by
  haveI := isTopologicalRing_tensor K L A
  rw [continuous_induced_rng, (isEmbedding_toTensorGL K L A).isInducing.continuous_iff]
  have : toTensorGL K L A ∘ (Subtype.val ∘ (psi γ δ x hfix hcent hmemT hfixT).symm) =
      fun t : twistedCentralizer K L A σ δ => x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x :=
    funext (toTensorGL_psi_symm_apply γ δ x hfix hcent hmemT hfixT)
  rw [this]
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end Psi

section General

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]

theorem main_general (σ : L ≃ₐ[K] L) (hσσ : ∀ l, σ (σ l) = l)
    (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (h2 : Module.finrank K L = 2)
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) (hδ : IsNormConjugator K L A σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ')
    (z : (L ⊗[K] A)ˣ) (hz : IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ (y₀ : GL (Fin 2) (L ⊗[K] A)) (r : ENNReal),
      IsNormConjugator K L A σ γ δ y₀ ∧ r ≠ 0 ∧ r ≠ ⊤ ∧ Coupled K L A σ γ δ y₀ τ (r • τ') := by

  letI mE : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  letI mC : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  letI mT : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  haveI := locallyCompactSpace_tensorGL K L A
  haveI := secondCountableTopology_tensor K L A
  haveI : SecondCountableTopology (GL (Fin 2) (L ⊗[K] A)) := secondCountableTopology_GL
  haveI : LocallyCompactSpace (twistedCentralizer K L A σ δ) :=
    (isClosed_twistedCentralizer K L A σ δ).locallyCompactSpace
  haveI : SecondCountableTopology (twistedCentralizer K L A σ δ) :=
    (IsInducing.subtypeVal :
      IsInducing (Subtype.val : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A))).secondCountableTopology
  haveI : IsHaarMeasure τ := hτ
  haveI : IsHaarMeasure τ' := hτ'

  obtain ⟨x, hx⟩ := hz
  obtain ⟨hNC, hcent, hmemT, hfixT⟩ := algebra_pack K L A σ hσσ h2 γ δ y hδ z x hx

  set ψ := psi γ δ x hfix hcent hmemT hfixT with hψ
  have hψc : Continuous ψ := continuous_psi γ δ x hfix hcent hmemT hfixT
  have hψsc : Continuous ψ.symm := continuous_psi_symm γ δ x hfix hcent hmemT hfixT

  have hHaar : IsHaarMeasure (Measure.map ψ τ) := ψ.isHaarMeasure_map τ hψc hψsc
  have huniq : Measure.map ψ τ = haarScalarFactor (Measure.map ψ τ) τ' • τ' :=
    isMulLeftInvariant_eq_smul _ _
  set c : ℝ≥0 := haarScalarFactor (Measure.map ψ τ) τ' with hc
  have hcpos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨x, (c : ℝ≥0∞), hNC, ENNReal.coe_ne_zero.2 hcpos.ne', ENNReal.coe_ne_top, ?_⟩

  have hsmul : ((c : ℝ≥0∞) • τ' : Measure (twistedCentralizer K L A σ δ)) = c • τ' := by
    ext s _
    rw [Measure.smul_apply, Measure.coe_nnreal_smul_apply, smul_eq_mul]
  have hcj : Measurable fun t : twistedCentralizer K L A σ δ => x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  show Measure.map (fun t : twistedCentralizer K L A σ δ => x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x)
      ((c : ℝ≥0∞) • τ') =
    Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      toTensorGL K L A (t : GL (Fin 2) A)) τ
  rw [hsmul, ← huniq, Measure.map_map hcj hψc.measurable]
  congr 1
  funext t
  simp only [Function.comp_apply, hψ, coe_psi_apply]
  group

end General

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem main
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsNormConjugator K L (v.adicCompletion K) σ γ δ y)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (z : (L ⊗[K] v.adicCompletion K)ˣ)
    (hz : IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ (y₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (r : ENNReal),
      IsNormConjugator K L (v.adicCompletion K) σ γ δ y₀ ∧ r ≠ 0 ∧ r ≠ ⊤ ∧
        Coupled K L (v.adicCompletion K) σ γ δ y₀ τ (r • τ') := by
  obtain ⟨hσσ, hfix⟩ := sigma_sq_and_fixed K L h2 σ hgen
  exact main_general K L (v.adicCompletion K) σ hσσ hfix h2 γ δ y hδ τ hτ τ' hτ' z hz

end Main

end R1NormConjCoupled

end

open R1NormConjCoupled in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (z : (L ⊗[K] v.adicCompletion K)ˣ)
    (hz : AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ (y₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (r : ENNReal),
      AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y₀ ∧ r ≠ 0 ∧ r ≠ ⊤ ∧
        AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ y₀ τ (r • τ') :=
  main K L h2 σ hgen v γ δ y hδ τ hτ τ' hτ' z hz

end S_AutomorphicForm_exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
