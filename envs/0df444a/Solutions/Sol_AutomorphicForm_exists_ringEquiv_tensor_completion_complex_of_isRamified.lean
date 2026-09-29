-- Prove2me | solution 1 for AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4a6d2a56-7696-505a-87b6-575ac4086b7b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL sigmaTensor"
namespace RamPlaceIsoSol
p2m_open "AutomorphicForm"

open NumberField NumberField.InfinitePlace
open scoped TensorProduct TensorProduct.RightActions

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem comap_eq_mk (w : InfinitePlace L) :
    w.comap (algebraMap K L) = InfinitePlace.mk (w.embedding.comp (algebraMap K L)) := by
  conv_lhs => rw [← mk_embedding w]
  exact comap_mk _ _

theorem embedding_comap_eq (w : InfinitePlace L) (hv : (w.comap (algebraMap K L)).IsReal) :
    (w.comap (algebraMap K L)).embedding = w.embedding.comp (algebraMap K L) := by
  have h := comap_eq_mk (K := K) w
  have h' : InfinitePlace.mk (w.comap (algebraMap K L)).embedding =
      InfinitePlace.mk (w.embedding.comp (algebraMap K L)) := by rw [mk_embedding]; exact h
  rcases mk_eq_iff.1 h' with h1 | h1
  · exact h1
  ·
    have hreal : ComplexEmbedding.IsReal (w.comap (algebraMap K L)).embedding := isReal_iff.1 hv
    rw [ComplexEmbedding.isReal_iff.1 hreal] at h1
    exact h1

theorem isReal_comp (w : InfinitePlace L) (hv : (w.comap (algebraMap K L)).IsReal) :
    ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K L)) := by
  rw [← embedding_comap_eq w hv]; exact isReal_iff.1 hv

theorem ringEquivReal_algebraMap (w : InfinitePlace L) (hv : (w.comap (algebraMap K L)).IsReal) (k : K) :
    ((Completion.ringEquivRealOfIsReal hv (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℝ) : ℂ) =
      w.embedding (algebraMap K L k) := by
  rw [Completion.ringEquivRealOfIsReal_apply, Completion.extensionEmbeddingOfIsReal_apply,
    IsScalarTower.algebraMap_apply K (WithAbs (w.comap (algebraMap K L)).1) (w.comap (algebraMap K L)).Completion]
  show Completion.extensionEmbedding (w.comap (algebraMap K L))
      (((WithAbs.equiv (w.comap (algebraMap K L)).1).symm k : WithAbs (w.comap (algebraMap K L)).1) :
        (w.comap (algebraMap K L)).Completion) = _
  rw [Completion.extensionEmbedding_coe, embedding_comap_eq w hv]
  simp

theorem embedding_sigma (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K) (x : L) :
    w.embedding (σ x) = (starRingEnd ℂ) (w.embedding x) := by
  classical
  obtain ⟨hwc, hv⟩ := isRamified_iff.1 hw
  set ψ : K →+* ℂ := w.embedding.comp (algebraMap K L) with hψ
  letI : Algebra K ℂ := ψ.toAlgebra
  have hreal : ComplexEmbedding.conjugate ψ = ψ := ComplexEmbedding.isReal_iff.1 (isReal_comp w hv)

  let W : L →ₐ[K] ℂ := ⟨w.embedding, fun k => rfl⟩
  let Wc : L →ₐ[K] ℂ := ⟨ComplexEmbedding.conjugate w.embedding, fun k => by
    show ComplexEmbedding.conjugate w.embedding (algebraMap K L k) = ψ k
    rw [← hreal]
    rfl⟩
  let Wσ : L →ₐ[K] ℂ := W.comp (σ : L →ₐ[K] L)
  have hcard : Fintype.card (L →ₐ[K] ℂ) = 2 := by rw [AlgHom.card K L ℂ, h2]
  have hne1 : W ≠ Wc := by
    intro h
    apply (isComplex_iff.1 hwc)
    rw [ComplexEmbedding.isReal_iff]
    have : (Wc : L →+* ℂ) = (W : L →+* ℂ) := by rw [h]
    exact this
  have hne2 : Wσ ≠ W := by
    intro h
    apply hσ
    ext x
    have hx : w.embedding (σ x) = w.embedding x := by
      have := congrArg (fun F : L →ₐ[K] ℂ => F x) h
      simpa [Wσ, W] using this
    exact w.embedding.injective hx

  have huniv : ({W, Wc} : Finset (L →ₐ[K] ℂ)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne1, hcard])
  have hmem : Wσ ∈ ({W, Wc} : Finset (L →ₐ[K] ℂ)) := by rw [huniv]; exact Finset.mem_univ _
  rcases Finset.mem_insert.1 hmem with h | h
  · exact absurd h hne2
  · rw [Finset.mem_singleton] at h
    have := congrArg (fun F : L →ₐ[K] ℂ => F x) h
    simpa [Wσ, W, Wc, ComplexEmbedding.conjugate_coe_eq] using this

end AutomorphicForm.RamPlaceIsoSol

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL sigmaTensor"
namespace RamPlaceIsoSol
p2m_open "AutomorphicForm"

open NumberField NumberField.InfinitePlace
open scoped TensorProduct TensorProduct.RightActions

theorem repr_tmul {R M A : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]
    {ι : Type} (b : Module.Basis ι R M) (x : M) (a : A) (i : ι) :
    (TensorProduct.RightActions.Algebra.TensorProduct.basis A b).repr (x ⊗ₜ a) i =
      a * algebraMap R A (b.repr x i) := by
  simp [TensorProduct.RightActions.Algebra.TensorProduct.basis, Algebra.TensorProduct.basis_repr_tmul]

section RealSpan

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem embedding_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι K L) (w : InfinitePlace L)
    (hreal : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K L))) (x : L) :
    w.embedding x = ∑ i, (hreal.embedding (b.repr x i) : ℝ) • w.embedding (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, Complex.real_smul, hreal.coe_embedding_apply]
  rfl

theorem top_le_span {ι : Type} [Fintype ι] (b : Module.Basis ι K L) (w : InfinitePlace L)
    (hreal : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K L))) (hwc : w.IsComplex) :
    ⊤ ≤ Submodule.span ℝ (Set.range fun i => w.embedding (b i)) := by

  have hmem : ∀ x : L, w.embedding x ∈ Submodule.span ℝ (Set.range fun i => w.embedding (b i)) := by
    intro x
    rw [embedding_eq_sum b w hreal x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hnr : ∃ x : L, (w.embedding x).im ≠ 0 := by
    by_contra h
    push Not at h
    apply (isComplex_iff.1 hwc)
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (h x)
  obtain ⟨x₀, hx₀⟩ := hnr
  intro z _
  have h1 : (1 : ℂ) ∈ Submodule.span ℝ (Set.range fun i => w.embedding (b i)) := by
    simpa using hmem 1
  have hz : z = (z.re - z.im * (w.embedding x₀).re / (w.embedding x₀).im) • (1 : ℂ) +
      (z.im / (w.embedding x₀).im) • w.embedding x₀ := by
    apply Complex.ext
    · simp [Complex.real_smul]
      field_simp
      ring
    · simp [Complex.real_smul]
      field_simp
  rw [hz]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ (hmem x₀))

end RealSpan

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_ringEquiv_of_bijective {R S : Type} [NonAssocSemiring R] [NonAssocSemiring S]
    [TopologicalSpace R] [TopologicalSpace S] (f : R →+* S) (hf : Function.Bijective f) (hc : Continuous f)
    (g : S → R) (hg : Continuous g) (hfg : ∀ y, f (g y) = y) :
    ∃ E : R ≃+* S, Continuous E ∧ Continuous E.symm ∧ ∀ z, E z = f z := by
  refine ⟨RingEquiv.ofBijective f hf, hc, ?_, fun _ => rfl⟩
  have hs : ∀ y, (RingEquiv.ofBijective f hf).symm y = g y := fun y =>
    hf.1 (((RingEquiv.ofBijective f hf).apply_symm_apply y).trans (hfg y).symm)
  exact hg.congr fun y => (hs y).symm

theorem main_coords (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K) :
    ∃ (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ)
      (E₀ : L ⊗[K] (w.comap (algebraMap K L)).Completion →+* ℂ ⊗[ℝ] ℝ)
      (g : ℂ ⊗[ℝ] ℝ → L ⊗[K] (w.comap (algebraMap K L)).Completion),
      Continuous e ∧ Continuous e.symm ∧
      (∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k)) ∧
      Function.Bijective E₀ ∧ Continuous E₀ ∧ Continuous g ∧ (∀ y, E₀ (g y) = y) ∧
      (∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
        E₀ (x ⊗ₜ a) = (w.embedding x * (e a : ℂ)) ⊗ₜ (1 : ℝ)) := by
  classical
  obtain ⟨hwc, hv⟩ := isRamified_iff.1 hw
  have hreal : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K L)) := isReal_comp w hv

  obtain ⟨e, he, he', healg⟩ : ∃ e : (w.comap (algebraMap K L)).Completion ≃+* ℝ,
      Continuous e ∧ Continuous e.symm ∧
      ∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k) :=
    ⟨Completion.ringEquivRealOfIsReal hv, (Completion.isometryEquivRealOfIsReal hv).continuous,
      (Completion.isometryEquivRealOfIsReal hv).symm.continuous, ringEquivReal_algebraMap w hv⟩
  have hσw : ∀ x, w.embedding (σ x) = (starRingEnd ℂ) (w.embedding x) := embedding_sigma h2 σ hσ w hw

  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : L ⊗[K] (w.comap (algebraMap K L)).Completion →+* ℂ ⊗[ℝ] ℝ,
      ∀ x a, E₀ (x ⊗ₜ a) = (w.embedding x * (e a : ℂ)) ⊗ₜ (1 : ℝ) := by
    letI algKC : Algebra K ℂ := (w.embedding.comp (algebraMap K L)).toAlgebra
    let W : L →ₐ[K] ℂ := ⟨w.embedding, fun _ => rfl⟩
    let G : (w.comap (algebraMap K L)).Completion →ₐ[K] ℂ :=
      ⟨Complex.ofRealHom.comp e.toRingHom, fun k => healg k⟩
    let m₁ : L ⊗[K] (w.comap (algebraMap K L)).Completion →ₐ[K] ℂ :=
      Algebra.TensorProduct.lift W G (fun _ _ => Commute.all _ _)
    have hm₁ : ∀ x a, m₁ (x ⊗ₜ a) = w.embedding x * (e a : ℂ) := fun x a => by
      simp only [m₁, Algebra.TensorProduct.lift_tmul]; rfl
    exact ⟨(Algebra.TensorProduct.includeLeftRingHom (R := ℝ) (A := ℂ) (B := ℝ)).comp m₁.toRingHom,
      fun x a => by
        show Algebra.TensorProduct.includeLeftRingHom (R := ℝ) (A := ℂ) (B := ℝ) (m₁ (x ⊗ₜ a)) = _
        rw [Algebra.TensorProduct.includeLeftRingHom_apply, hm₁]⟩

  let b := Module.finBasis K L
  have hcard : Fintype.card (Fin (Module.finrank K L)) = Module.finrank ℝ ℂ := by
    rw [Fintype.card_fin, h2, Complex.finrank_real_complex]
  obtain ⟨cB, hcB⟩ : ∃ cB : Module.Basis (Fin (Module.finrank K L)) ℝ ℂ, ∀ i, cB i = w.embedding (b i) :=
    ⟨basisOfTopLeSpanOfCardEqFinrank (fun i => w.embedding (b i)) (top_le_span b w hreal hwc) hcard,
      fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i⟩
  have hcBrepr : ∀ (x : L) (i : Fin (Module.finrank K L)),
      cB.repr (w.embedding x) i = hreal.embedding (b.repr x i) := by
    intro x i
    have hx : w.embedding x = cB.equivFun.symm (fun i => (hreal.embedding (b.repr x i) : ℝ)) := by
      rw [Module.Basis.equivFun_symm_apply, embedding_eq_sum b w hreal x]
      simp only [hcB]
    rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
  have healg' : ∀ k : K, e (algebraMap K (w.comap (algebraMap K L)).Completion k) = hreal.embedding k := by
    intro k
    apply Complex.ofReal_injective
    rw [healg, hreal.coe_embedding_apply]
    rfl
  let B₁ := TensorProduct.RightActions.Algebra.TensorProduct.basis (w.comap (algebraMap K L)).Completion b
  let B₂ := TensorProduct.RightActions.Algebra.TensorProduct.basis ℝ cB
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ : (L ⊗[K] (w.comap (algebraMap K L)).Completion) ≃L[(w.comap (algebraMap K L)).Completion]
      (Fin (Module.finrank K L) → (w.comap (algebraMap K L)).Completion), ∀ z, φ z = B₁.equivFun z :=
    ⟨IsModuleTopology.continuousLinearEquiv B₁.equivFun, fun _ => rfl⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ : (ℂ ⊗[ℝ] ℝ) ≃L[ℝ] (Fin (Module.finrank K L) → ℝ), ∀ z, φ z = B₂.equivFun z :=
    ⟨IsModuleTopology.continuousLinearEquiv B₂.equivFun, fun _ => rfl⟩
  let P : (Fin (Module.finrank K L) → (w.comap (algebraMap K L)).Completion) → (Fin (Module.finrank K L) → ℝ) :=
    fun u i => e (u i)
  let P' : (Fin (Module.finrank K L) → ℝ) → (Fin (Module.finrank K L) → (w.comap (algebraMap K L)).Completion) :=
    fun u i => e.symm (u i)
  have hP : Continuous P := continuous_pi fun i => he.comp (continuous_apply i)
  have hP' : Continuous P' := continuous_pi fun i => he'.comp (continuous_apply i)
  have hPP' : ∀ u, P (P' u) = u := fun u => funext fun i => e.apply_symm_apply _
  have hP'P : ∀ u, P' (P u) = u := fun u => funext fun i => e.symm_apply_apply _

  have key : ∀ z, E₀ z = φ₂.symm (P (φ₁ z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [E₀.map_zero, φ₁.map_zero]
        show (0 : ℂ ⊗[ℝ] ℝ) = φ₂.symm (fun _ => e 0)
        rw [e.map_zero]
        exact (φ₂.symm.map_zero).symm
    | tmul x a =>
        apply φ₂.injective
        rw [ContinuousLinearEquiv.apply_symm_apply, hE₀]
        rw [hφ₂, hφ₁]
        funext i
        show B₂.equivFun ((w.embedding x * (e a : ℂ)) ⊗ₜ (1 : ℝ)) i = e (B₁.equivFun (x ⊗ₜ a) i)
        have h1 : B₁.equivFun (x ⊗ₜ a) i =
            a * algebraMap K (w.comap (algebraMap K L)).Completion (b.repr x i) := by
          rw [Module.Basis.equivFun_apply, repr_tmul]
        have h2 : B₂.equivFun ((w.embedding x * (e a : ℂ)) ⊗ₜ (1 : ℝ)) i = cB.repr (w.embedding x * (e a : ℂ)) i := by
          rw [Module.Basis.equivFun_apply, repr_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply]
        have h3 : cB.repr (w.embedding x * (e a : ℂ)) i = e a * hreal.embedding (b.repr x i) := by
          rw [show w.embedding x * (e a : ℂ) = (e a : ℝ) • w.embedding x by rw [Complex.real_smul, mul_comm],
            map_smul, Finsupp.smul_apply, smul_eq_mul, hcBrepr]
        rw [h2, h3, h1, map_mul, healg']
    | add z₁ z₂ h₁ h₂ =>
        rw [E₀.map_add, h₁, h₂, φ₁.map_add]
        have : P (φ₁ z₁ + φ₁ z₂) = P (φ₁ z₁) + P (φ₁ z₂) := by
          funext i; simp [P]
        rw [this, φ₂.symm.map_add]
  have hbij : Function.Bijective E₀ := by
    refine ⟨fun z₁ z₂ h => ?_, fun y => ⟨φ₁.symm (P' (φ₂ y)), ?_⟩⟩
    · rw [key, key] at h
      have h' := congrArg (fun u => φ₁.symm (P' (φ₂ u))) h
      simpa only [ContinuousLinearEquiv.apply_symm_apply, hP'P, ContinuousLinearEquiv.symm_apply_apply] using h'
    · rw [key]
      simp only [ContinuousLinearEquiv.apply_symm_apply, hPP', ContinuousLinearEquiv.symm_apply_apply]
  have hcE₀ : Continuous E₀ :=
    (φ₂.symm.continuous.comp (hP.comp φ₁.continuous)).congr fun z => (key z).symm
  have hinv : ∀ y, E₀ (φ₁.symm (P' (φ₂ y))) = y := fun y => by
    rw [key]
    simp only [ContinuousLinearEquiv.apply_symm_apply, hPP', ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨e, E₀, fun y => φ₁.symm (P' (φ₂ y)), he, he', healg, hbij, hcE₀,
    φ₁.symm.continuous.comp (hP'.comp φ₂.continuous), hinv, hE₀⟩

theorem main (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K) :
    ∃ (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ)
      (E : L ⊗[K] (w.comap (algebraMap K L)).Completion ≃+* ℂ ⊗[ℝ] ℝ),
      Continuous e ∧ Continuous e.symm ∧ Continuous E ∧ Continuous E.symm ∧
      (∀ z, E (sigmaTensor K L (w.comap (algebraMap K L)).Completion σ z) =
        sigmaTensor ℝ ℂ ℝ Complex.conjAe (E z)) ∧
      (∀ g : GL (Fin 2) (w.comap (algebraMap K L)).Completion,
        Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L (w.comap (algebraMap K L)).Completion g) =
          toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.map e.toRingHom g)) ∧
      (∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E (x ⊗ₜ a)) = w.embedding x * (e a : ℂ)) ∧
      (∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k)) := by
  have hσw : ∀ x, w.embedding (σ x) = (starRingEnd ℂ) (w.embedding x) := embedding_sigma h2 σ hσ w hw
  obtain ⟨e, E₀, g, he, he', healg, hbij, hcE₀, hg, hinv, hE₀⟩ := main_coords h2 σ hσ w hw
  obtain ⟨E, hEc, hEc', hEapply⟩ := exists_ringEquiv_of_bijective E₀ hbij hcE₀ g hg hinv
  refine ⟨e, E, he, he', hEc, hEc', ?_, ?_, ?_, healg⟩
  ·
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [(sigmaTensor K L _ σ).map_zero, E.map_zero, (sigmaTensor ℝ ℂ ℝ Complex.conjAe).map_zero]
    | tmul x a =>
        have hl : sigmaTensor K L (w.comap (algebraMap K L)).Completion σ (x ⊗ₜ a) = σ x ⊗ₜ a := by
          simp [sigmaTensor, Algebra.TensorProduct.map_tmul]
        have hr : sigmaTensor ℝ ℂ ℝ Complex.conjAe ((w.embedding x * (e a : ℂ)) ⊗ₜ (1 : ℝ)) =
            (Complex.conjAe (w.embedding x * (e a : ℂ))) ⊗ₜ (1 : ℝ) := by
          simp [sigmaTensor, Algebra.TensorProduct.map_tmul]
        rw [hl, hEapply, hEapply, hE₀, hE₀, hσw, hr]
        congr 1
        rw [map_mul]
        show _ = (starRingEnd ℂ) (w.embedding x) * (starRingEnd ℂ) (e a : ℂ)
        rw [Complex.conj_ofReal]
    | add z₁ z₂ h₁ h₂ =>
        rw [(sigmaTensor K L _ σ).map_add, E.map_add, h₁, h₂, E.map_add, (sigmaTensor ℝ ℂ ℝ Complex.conjAe).map_add]
  ·
    intro g
    ext i j
    simp only [toTensorGL, Matrix.GeneralLinearGroup.map_apply]
    show E (Algebra.TensorProduct.includeRight ((g : Matrix (Fin 2) (Fin 2) _) i j)) =
      Algebra.TensorProduct.includeRight (e ((g : Matrix (Fin 2) (Fin 2) _) i j))
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply, hEapply, hE₀,
      map_one, one_mul]
    have key2 : ∀ r : ℝ, (r : ℂ) ⊗ₜ[ℝ] (1 : ℝ) = (1 : ℂ) ⊗ₜ[ℝ] r := fun r => by
      have := Algebra.TensorProduct.tmul_one_eq_one_tmul (A := ℂ) (B := ℝ) (R := ℝ) r
      simpa using this
    exact key2 _
  ·
    intro x a
    rw [hEapply, hE₀]
    exact (Algebra.TensorProduct.rid_tmul (R := ℝ) (S := ℝ) (A := ℂ) (1 : ℝ) (w.embedding x * (e a : ℂ))).trans
      (one_smul _ _)

end AutomorphicForm.RamPlaceIsoSol

end

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K) :
    ∃ (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ)
      (E : L ⊗[K] (w.comap (algebraMap K L)).Completion ≃+* ℂ ⊗[ℝ] ℝ),
      Continuous e ∧ Continuous e.symm ∧ Continuous E ∧ Continuous E.symm ∧
      (∀ z, E (sigmaTensor K L (w.comap (algebraMap K L)).Completion σ z) =
        sigmaTensor ℝ ℂ ℝ Complex.conjAe (E z)) ∧
      (∀ g : GL (Fin 2) (w.comap (algebraMap K L)).Completion,
        Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L (w.comap (algebraMap K L)).Completion g) =
          toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.map e.toRingHom g)) ∧
      (∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E (x ⊗ₜ a)) = w.embedding x * (e a : ℂ)) ∧
      (∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k)) :=
  AutomorphicForm.RamPlaceIsoSol.main h2 σ hσ w hw

end S_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified
end P2MW
export P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified (solution)
