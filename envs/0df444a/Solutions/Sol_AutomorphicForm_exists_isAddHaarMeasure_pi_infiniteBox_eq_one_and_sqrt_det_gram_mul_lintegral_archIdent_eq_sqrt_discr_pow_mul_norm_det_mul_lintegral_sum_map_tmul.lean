-- Prove2me | solution 1 for AutomorphicForm.exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/042fb73f-9b29-547a-8805-8f982b9feb7a

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq
import Theorems.Thm_MeasureTheory_Measure_sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
import Theorems.Thm_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
import Theorems.Thm_AutomorphicForm_sqrt_det_gram_smul_map_volume_image_parallelepiped_tmul_integralBasis_eq_sqrt_discr_pow_mul_norm_det
import Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal SchwartzMap Classical

namespace E8A
namespace AC

theorem gram_mul_lintegral_eq_measure_image_mul_lintegral
    {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n₂ : ℕ} (e₂ : Fin n₂ → V) (he₂ : LinearIndependent ℝ e₂)
    {P : Type} [Fintype P] (f : P → V) (hf : LinearIndependent ℝ f)
    (hspan : Submodule.span ℝ (Set.range e₂) = Submodule.span ℝ (Set.range f))
    (G : V → ℝ≥0∞) (hG : Measurable G) :
    ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|) *
        ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i) =
      ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|)) •
          Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume)
        ((fun t : P → ℝ => ∑ p, t p • f p) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) *
      ∫⁻ t : P → ℝ, G (∑ p, t p • f p) := by

  set N : ℕ := Fintype.card P
  let σ : P ≃ Fin N := Fintype.equivFin P
  let f' : Fin N → V := f ∘ σ.symm
  have hf' : LinearIndependent ℝ f' := hf.comp σ.symm σ.symm.injective
  have hrange : Set.range f' = Set.range f := σ.symm.surjective.range_comp f
  have hspan' : Submodule.span ℝ (Set.range f') = Submodule.span ℝ (Set.range e₂) := by
    rw [hrange, hspan]

  have hmeas : ∀ {m : ℕ} (e : Fin m → V), Measurable (fun a : Fin m → ℝ => ∑ i, a i • e i) :=
    fun e => (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const).measurable

  have hGram := MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq B e₂ f' he₂ hf' hspan'

  have hCov := MeasureTheory.Measure.sqrt_abs_det_gram_smul_map_volume_image_pi_Ico_eq_of_span_eq
    B f' f' hf' hf' rfl

  have hF : (fun a : Fin N → ℝ => ∑ i, a i • f' i) =
      (fun t : P → ℝ => ∑ p, t p • f p) ∘ (fun a : Fin N → ℝ => a ∘ σ) := by
    funext a
    simp only [Function.comp_apply, f']
    exact (Fintype.sum_equiv σ (fun p => a (σ p) • f p) (fun i => a i • f (σ.symm i))
      (fun p => by simp only [Equiv.symm_apply_apply])).symm
  have hbox : (fun a : Fin N → ℝ => a ∘ σ) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) =
      Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
    ext t
    simp only [Set.mem_image, Set.mem_univ_pi]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun p => ha (σ p)
    · intro ht
      exact ⟨t ∘ σ.symm, fun i => ht (σ.symm i), by funext p; simp⟩
  have himg : (fun a : Fin N → ℝ => ∑ i, a i • f' i) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) =
      (fun t : P → ℝ => ∑ p, t p • f p) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
    rw [hF, Set.image_comp, hbox]

  have hint : ∫⁻ a : Fin N → ℝ, G (∑ i, a i • f' i) = ∫⁻ t : P → ℝ, G (∑ p, t p • f p) := by
    have hmp := (volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) σ).symm _
    have key := MeasurePreserving.lintegral_map_equiv (fun t : P → ℝ => G (∑ p, t p • f p))
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ).symm hmp
    have hcoe : ∀ a : Fin N → ℝ,
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ).symm a) = a ∘ σ := fun a => rfl
    rw [key]
    congr 1
    funext a
    rw [hcoe]
    exact congrArg G (congrFun hF a)
  calc ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|) *
        ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)
      = ∫⁻ x, G x ∂((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|)) •
          Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume) := by
        rw [lintegral_smul_measure, lintegral_map hG (hmeas e₂), smul_eq_mul]
    _ = ∫⁻ x, G x ∂((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin N => B (f' i) (f' j)).det|)) •
          Measure.map (fun a : Fin N → ℝ => ∑ i, a i • f' i) volume) := by rw [hGram]
    _ = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin N => B (f' i) (f' j)).det|) *
          ∫⁻ a : Fin N → ℝ, G (∑ i, a i • f' i) := by
        rw [lintegral_smul_measure, lintegral_map hG (hmeas f'), smul_eq_mul]
    _ = ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin N => B (f' i) (f' j)).det|)) •
            Measure.map (fun a : Fin N → ℝ => ∑ i, a i • f' i) volume)
          ((fun a : Fin N → ℝ => ∑ i, a i • f' i) '' Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) *
          ∫⁻ t : P → ℝ, G (∑ p, t p • f p) := by rw [hCov, hint]
    _ = _ := by rw [hGram, himg]

end E8A.AC

namespace E8A
namespace AC

section Kinf

variable (K : Type) [Field K] [NumberField K] [Algebra ℝ (InfiniteAdeleRing K)]
  (halgK : ∀ r : ℝ, algebraMap ℝ (InfiniteAdeleRing K) r =
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r))

omit [NumberField K] in
include halgK in
theorem ringEquiv_mixedSpace_smul (r : ℝ) (x : InfiniteAdeleRing K) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (r • x) =
      r • InfiniteAdeleRing.ringEquiv_mixedSpace K x := by
  rw [Algebra.smul_def, map_mul, halgK, RingEquiv.apply_symm_apply, ← Algebra.smul_def]

noncomputable def eKlin : InfiniteAdeleRing K ≃ₗ[ℝ] mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.toLinearEquiv
    (ringEquiv_mixedSpace_smul K halgK)

omit [NumberField K] in
theorem eKlin_apply (x : InfiniteAdeleRing K) :
    eKlin K halgK x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

noncomputable def omegaB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (InfiniteAdeleRing K) :=
  (mixedEmbedding.latticeBasis K).map (eKlin K halgK).symm

theorem ringEquiv_mixedSpace_omegaB (p : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (omegaB K halgK p) = mixedEmbedding.latticeBasis K p := by
  rw [omegaB, Module.Basis.map_apply, ← eKlin_apply K halgK, LinearEquiv.apply_symm_apply]

theorem omegaB_apply (p : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    omegaB K halgK p = algebraMap K (InfiniteAdeleRing K) (integralBasis K p) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
  rw [ringEquiv_mixedSpace_omegaB, mixedEmbedding.latticeBasis_apply,
    InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

variable (ι : Type) [Fintype ι]

noncomputable def Lam : (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ) ≃ₗ[ℝ] (ι → InfiniteAdeleRing K) where
  toFun t k := ∑ p, t (p, k) • omegaB K halgK p
  map_add' t s := by
    funext k
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r t := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
  invFun a q := (omegaB K halgK).repr (a q.2) q.1
  left_inv t := by
    funext q
    change (omegaB K halgK).repr (∑ p, (fun p => t (p, q.2)) p • omegaB K halgK p) q.1 = t q
    rw [Module.Basis.repr_sum_self]
  right_inv a := by
    funext k
    change ∑ p, (omegaB K halgK).repr (a k) p • omegaB K halgK p = a k
    rw [Module.Basis.sum_repr]

omit [Fintype ι] in
theorem Lam_apply (t : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ) :
    Lam K halgK ι t = fun k => ∑ p, t (p, k) • omegaB K halgK p := rfl

omit [Algebra ℝ (InfiniteAdeleRing K)] in
theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  exact (isEmbedding_prodMkLeft (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).secondCountableTopology

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]

noncomputable def LamM (hcont : Continuous (algebraMap ℝ (InfiniteAdeleRing K))) :
    (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ) ≃ᵐ (ι → InfiniteAdeleRing K) :=
  haveI : ContinuousSMul ℝ (InfiniteAdeleRing K) := continuousSMul_of_algebraMap ℝ _ hcont
  haveI := secondCountableTopology_infiniteAdeleRing K
  ((Lam K halgK ι).toContinuousLinearEquiv).toHomeomorph.toMeasurableEquiv

theorem LamM_apply (hcont : Continuous (algebraMap ℝ (InfiniteAdeleRing K)))
    (t : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ) :
    LamM K halgK ι hcont t = fun k => ∑ p, t (p, k) • omegaB K halgK p := rfl

theorem isAddHaarMeasure_map_LamM (hcont : Continuous (algebraMap ℝ (InfiniteAdeleRing K))) :
    (Measure.map (LamM K halgK ι hcont) volume).IsAddHaarMeasure := by
  haveI : ContinuousSMul ℝ (InfiniteAdeleRing K) := continuousSMul_of_algebraMap ℝ _ hcont
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI := isAddHaarMeasure_volume_pi (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι)
  have h := (Lam K halgK ι).toContinuousLinearEquiv.isAddHaarMeasure_map
    (volume : Measure (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ))
  have hcoe : ⇑(LamM K halgK ι hcont) = ⇑((Lam K halgK ι).toContinuousLinearEquiv) := rfl
  rw [hcoe]
  exact h

theorem map_LamM_piInfiniteBox (hcont : Continuous (algebraMap ℝ (InfiniteAdeleRing K))) :
    Measure.map (LamM K halgK ι hcont) volume
      {a : ι → InfiniteAdeleRing K | ∀ k, a k ∈ infiniteBox K} = 1 := by
  rw [MeasurableEquiv.map_apply]
  have key : ∀ (t : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ) (k : ι),
      (LamM K halgK ι hcont t k ∈ infiniteBox K ↔ ∀ p, t (p, k) ∈ Set.Ico (0 : ℝ) 1) := by
    intro t k
    change InfiniteAdeleRing.ringEquiv_mixedSpace K (∑ p, t (p, k) • omegaB K halgK p) ∈
        ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) ↔ _
    rw [map_sum]
    simp_rw [ringEquiv_mixedSpace_smul K halgK, ringEquiv_mixedSpace_omegaB K halgK]
    rw [ZSpan.mem_fundamentalDomain, Module.Basis.repr_sum_self]
  have hpre : (LamM K halgK ι hcont) ⁻¹' {a : ι → InfiniteAdeleRing K | ∀ k, a k ∈ infiniteBox K} =
      Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro h q
      exact (key t q.2).1 (h q.2) q.1
    · intro h k
      exact (key t k).2 fun p => h (p, k)
  rw [hpre, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

theorem lintegral_map_LamM (hcont : Continuous (algebraMap ℝ (InfiniteAdeleRing K)))
    (F : (ι → InfiniteAdeleRing K) → ℝ≥0∞) :
    ∫⁻ a, F a ∂(Measure.map (LamM K halgK ι hcont) volume) =
      ∫⁻ t : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι → ℝ,
        F (fun k => ∑ p, t (p, k) • omegaB K halgK p) :=
  lintegral_map_equiv F _

end Kinf

section E

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section alg

variable [Algebra ℝ (InfiniteAdeleRing K)] [Algebra ℝ (L ⊗[K] InfiniteAdeleRing K)]
  (halgE : ∀ r : ℝ, algebraMap ℝ (L ⊗[K] InfiniteAdeleRing K) r =
    (1 : L) ⊗ₜ[K] algebraMap ℝ (InfiniteAdeleRing K) r)

omit [NumberField K] [NumberField L] in
include halgE in
theorem tmul_smul_real (r : ℝ) (l : L) (x : InfiniteAdeleRing K) :
    l ⊗ₜ[K] (r • x) = r • (l ⊗ₜ[K] x) := by
  rw [Algebra.smul_def, Algebra.smul_def, halgE, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [NumberField K] [NumberField L] in
include halgE in
theorem map_tmul_sum_smul {P : Type} [Fintype P] (X : Matrix (Fin 2) (Fin 2) L) (c : P → ℝ)
    (w : P → InfiniteAdeleRing K) :
    X.map (fun l : L => l ⊗ₜ[K] (∑ p, c p • w p)) = ∑ p, c p • X.map (fun l : L => l ⊗ₜ[K] w p) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, TensorProduct.tmul_sum,
    tmul_smul_real K L halgE]

omit [NumberField K] [NumberField L] in
include halgE in

theorem sum_map_tmul_sum_smul {ι P : Type} [Fintype ι] [Fintype P]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (t : P × ι → ℝ) (w : P → InfiniteAdeleRing K) :
    (∑ k, (b k).map fun l : L => l ⊗ₜ[K] (∑ p, t (p, k) • w p)) =
      ∑ q : P × ι, t q • (b q.2).map (fun l : L => l ⊗ₜ[K] w q.1) := by
  rw [Fintype.sum_prod_type]
  simp only [map_tmul_sum_smul K L halgE]
  exact Finset.sum_comm

noncomputable def trB : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →ₗ[ℝ]
    Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (X * Y)))
    (fun X₁ X₂ Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by simp only [Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul])
    (fun X Y₁ Y₂ => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by simp only [Matrix.mul_smul, Matrix.trace_smul, map_smul, smul_eq_mul])

omit [NumberField K] [NumberField L] [Algebra ℝ (InfiniteAdeleRing K)] in
theorem trB_apply (X Y : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    trB K L X Y = Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (X * Y)) := rfl

end alg

theorem measurable_archIntegrand (v : Fin 2 → L) (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    [MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))]
    [BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))] :
    Measurable (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
        (AutomorphicForm.archIdent K L ((X.mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have h1 : Continuous (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      X.mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) := by
    change Continuous (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => fun i =>
      ∑ j, X i j * (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K))
    exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem i j).mul continuous_const
  have h2 : Continuous (AutomorphicForm.archIdent K L) :=
    (AutomorphicForm.archIdentHomeomorph K L).continuous.congr
      (AutomorphicForm.archIdentHomeomorph_apply K L)
  have h3 := NumberField.AdelicBox.continuous_ringEquiv_mixedSpace L
  exact (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp (g.continuous.comp
    (continuous_pi fun i => h3.comp (h2.comp ((continuous_apply i).comp h1)))))).measurable

end E

end E8A.AC

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (v : Fin 2 → L) (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ ν : Measure (ι → InfiniteAdeleRing K), ν.IsAddHaarMeasure ∧
      ν {a : ι → InfiniteAdeleRing K | ∀ k, a k ∈ infiniteBox K} = 1 ∧
      ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
          ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
            X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
      (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
            Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
          ∫⁻ cc : Fin n₂ → ℝ, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L (((∑ k, cc k • e₂ k).mulVec fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re) =
        (ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card ι *
            |((Algebra.norm ℚ (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det : ℚ) : ℝ)|)) *
          ∫⁻ a : ι → InfiniteAdeleRing K, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L
            (AutomorphicForm.archIdent K L (((∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k).mulVec
              fun j => (v j) ⊗ₜ[K] (1 : InfiniteAdeleRing K)) i)))).re ∂ν) := by

  letI algK : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI algE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  letI msV : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  have halgK : ∀ r : ℝ, algebraMap ℝ (InfiniteAdeleRing K) r =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r) :=
    fun r => rfl
  have halgE : ∀ r : ℝ, algebraMap ℝ (L ⊗[K] InfiniteAdeleRing K) r =
      (1 : L) ⊗ₜ[K] algebraMap ℝ (InfiniteAdeleRing K) r := fun r => rfl
  obtain ⟨-, -, hfinE, hcontalg, hsmulE, -, -⟩ :=
    AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det K L
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)

  refine ⟨Measure.map (E8A.AC.LamM K halgK ι hcontalg) volume,
    E8A.AC.isAddHaarMeasure_map_LamM K halgK ι hcontalg,
    E8A.AC.map_LamM_piInfiniteBox K halgK ι hcontalg, ?_⟩
  intro n₂ e₂ he₂ hspan₂

  have hM : ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
      ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2)
              (Units.map (AutomorphicForm.tensorArchHom K L).toRingHom.toMonoidHom c) :
              GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
    have h1 : AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
          Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ :=
      Matrix.GeneralLinearGroup.ext (fun i j => rfl)
    have h2 : ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.map (AutomorphicForm.tensorArchHom K L).toRingHom.toMonoidHom c) :
            GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
      change (Matrix.scalar (Fin 2) (c : L ⊗[K] AdeleRing (𝓞 K) K)).map
          (AutomorphicForm.tensorArchHom K L).toRingHom =
        Matrix.scalar (Fin 2) ((Units.map (AutomorphicForm.tensorArchHom K L).toRingHom.toMonoidHom c :
          (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K)
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
      rfl
    rw [map_mul, Units.val_mul, Units.val_mul, h1, h2]
  rw [hM] at hspan₂

  obtain ⟨hfli, hfspan⟩ :=
    AutomorphicForm.linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
      K L σ δ₀ (Units.map (AutomorphicForm.tensorArchHom K L).toRingHom.toMonoidHom c) b hb hbspan
  have hspanEq : Submodule.span ℝ (Set.range e₂) =
      Submodule.span ℝ (Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × ι =>
        (b p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1)))) :=
    SetLike.coe_injective (hspan₂.trans hfspan.symm)

  have hAC :=
    AutomorphicForm.sqrt_det_gram_smul_map_volume_image_parallelepiped_tmul_integralBasis_eq_sqrt_discr_pow_mul_norm_det
      K L σ δ₀ (Units.map (AutomorphicForm.tensorArchHom K L).toRingHom.toMonoidHom c) b hb hbspan
      n₂ e₂ he₂ hspan₂

  have hG := E8A.AC.measurable_archIntegrand K L v g
  have hgen := E8A.AC.gram_mul_lintegral_eq_measure_image_mul_lintegral (E8A.AC.trB K L) e₂ he₂ _ hfli
    hspanEq _ hG
  simp only [E8A.AC.trB_apply] at hgen
  rw [hAC] at hgen
  rw [hgen, E8A.AC.lintegral_map_LamM]
  congr 1
  congr 1
  funext t
  rw [E8A.AC.sum_map_tmul_sum_smul K L halgE b t]
  simp only [E8A.AC.omegaB_apply]

end S_AutomorphicForm_exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul
end P2MW
export P2MW.S_AutomorphicForm_exists_isAddHaarMeasure_pi_infiniteBox_eq_one_and_sqrt_det_gram_mul_lintegral_archIdent_eq_sqrt_discr_pow_mul_norm_det_mul_lintegral_sum_map_tmul (solution)
