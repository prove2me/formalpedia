-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/718b2409-ea25-5294-8742-8262fcb0c36c

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm FLT.SmoothVectors Module
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section
namespace MPresAux

theorem exists_eq_sum_apply_smul {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → X) (e : ι → (X → ℂ)),
      (∀ j, e j ∈ W) ∧ ∀ f ∈ W, f = ∑ j, f (x j) • e j := by
  classical
  let ev : X → Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ (x : X) (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  let Φ : Submodule ℂ (Dual ℂ W) := Submodule.span ℂ (Set.range ev)
  have hΦbot : Φ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have h := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at h
    simpa using h
  have hΦtop : Φ = ⊤ := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
    rw [hΦbot, finrank_bot, add_zero] at h1
    apply Submodule.eq_top_of_finrank_eq
    rw [h1, Subspace.dual_finrank_eq]
  let b := Module.finBasis ℂ W
  have hcoord : ∀ j, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord j := by
    intro j
    have hj : b.coord j ∈ Φ := by rw [hΦtop]; exact Submodule.mem_top
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp hj
  choose c hc using hcoord
  let S : Finset X := Finset.univ.biUnion fun j => (c j).support
  have hsupp : ∀ j, (c j).support ⊆ S := fun j => Finset.subset_biUnion_of_mem (fun j => (c j).support) (Finset.mem_univ j)
  refine ⟨Fin (Module.finrank ℂ W) × ↥S, inferInstance, fun p => (p.2 : X),
    fun p => c p.1 (p.2 : X) • ((b p.1 : W) : X → ℂ), fun p => W.smul_mem _ (b p.1).2, ?_⟩
  intro f hf
  have hcoordj : ∀ j, b.repr ⟨f, hf⟩ j = ∑ x ∈ S, c j x * f x := by
    intro j
    have h1 : b.repr ⟨f, hf⟩ j = b.coord j ⟨f, hf⟩ := rfl
    rw [h1, ← hc j]
    simp only [Finsupp.sum, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, hev, smul_eq_mul]
    exact Finset.sum_subset (hsupp j) (fun x _ hx => by rw [Finsupp.notMem_support_iff.mp hx, zero_mul])
  have hrepr : f = ∑ j, b.repr ⟨f, hf⟩ j • ((b j : W) : X → ℂ) := by
    have h := congrArg (fun w : W => (w : X → ℂ)) (b.sum_repr ⟨f, hf⟩).symm
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h
  calc f = ∑ j, b.repr ⟨f, hf⟩ j • ((b j : W) : X → ℂ) := hrepr
    _ = ∑ j, ∑ x ∈ S, f x • (c j x • ((b j : W) : X → ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcoordj j, Finset.sum_smul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [smul_smul, mul_comm]
    _ = ∑ j, ∑ x : ↥S, f (x : X) • (c j (x : X) • ((b j : W) : X → ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (Finset.sum_coe_sort S (fun x => f x • (c j x • ((b j : W) : X → ℂ)))).symm
    _ = ∑ p : Fin (Module.finrank ℂ W) × ↥S, f (p.2 : X) • (c p.1 (p.2 : X) • ((b p.1 : W) : X → ℂ)) := by
        rw [Fintype.sum_prod_type]

theorem eq_of_eq_on_halfPlane {O : Set ℂ} (hOc : IsPreconnected O)
    (hhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f O) (hg : AnalyticOnNhd ℂ g O)
    (h : ∀ s : ℂ, 1 / 2 < s.re → f s = g s) {s₀ : ℂ} (hs₀ : s₀ ∈ O) : f s₀ = g s₀ := by
  have hmem : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num
  have h1 : (1 : ℂ) ∈ O := hhalf hmem
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : f =ᶠ[nhds (1 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) (fun s hs => h s hs)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hOc h1 hev hs₀

theorem analyticOnNhd_const_cpow_affine {c : ℂ} (hc : c ≠ 0) (a b : ℂ) (O : Set ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => c ^ (a * s + b)) O := by
  have hd : Differentiable ℂ (fun s : ℂ => c ^ (a * s + b)) :=
    Differentiable.const_cpow ((differentiable_id.const_mul a).add_const b) (Or.inl hc)
  exact (hd.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ O)

end MPresAux
end

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (N : Ideal (𝓞 F))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φf s (g * u) = φf s g)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (t : ℝ),
    IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-((t : ℂ) * Complex.I))) (etaSnd μ αm hαm (-((t : ℂ) * Complex.I)))
        (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) ∧
    Continuous (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) ∧
    (∀ (g : AdelicGL2 (𝓞 F) F), ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
        Nφ ((t : ℂ) * Complex.I) (g * u) = Nφ ((t : ℂ) * Complex.I) g) ∧
    (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) =>
            ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk N φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflev Oφ Eφ Nφ hEφ t
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEφ
  set s₀ : ℂ := (t : ℂ) * Complex.I with hs₀def
  have hs₀ : s₀ ∈ Oφ := hOax (by simp [hs₀def])
  set V : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ with hVdef

  have hWI : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g
      = ∫ x, φf s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ∂(adelicAddHaar (𝓞 F) F) := fun s g => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro b hb g
    have hαpos : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ((αm z : ℝˣ) : ℝ) ≠ 0 := fun z => (hαm z).ne'
    have hbase : ∀ z : (AdeleRing (𝓞 F) F)ˣ, (((αm z : ℝˣ) : ℝ) : ℂ) ≠ 0 := fun z => by
      exact_mod_cast hαpos z
    set z₁ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hz₁
    set z₂ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with hz₂
    have hη : ∀ s : ℂ, ((etaFst ν αm hαm (-s) z₁ : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s) z₂ : ℂˣ) : ℂ)
        = (((ν z₁ : ℂˣ) : ℂ) * (((αm z₁ : ℝˣ) : ℝ) : ℂ) ^ ((-1) * s + 1 / 2))
          * (((μ z₂ : ℂˣ) : ℂ) * (((αm z₂ : ℝˣ) : ℝ) : ℂ) ^ ((1 : ℂ) * s + (-(1 / 2)))) := by
      intro s
      have h1 : ((etaFst ν αm hαm (-s) z₁ : ℂˣ) : ℂ) = ((ν z₁ : ℂˣ) : ℂ) * (((αm z₁ : ℝˣ) : ℝ) : ℂ) ^ (-s + 1 / 2) := rfl
      have h2 : ((etaSnd μ αm hαm (-s) z₂ : ℂˣ) : ℂ) = ((μ z₂ : ℂˣ) : ℂ) * (((αm z₂ : ℝˣ) : ℝ) : ℂ) ^ (-(-s + 1 / 2)) := rfl
      rw [h1, h2]
      congr 2 <;> ring_nf
    have hanη : AnalyticOnNhd ℂ (fun s : ℂ => ((etaFst ν αm hαm (-s) z₁ : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s) z₂ : ℂˣ) : ℂ)) Oφ := by
      simp only [hη]
      exact ((analyticOnNhd_const.mul (MPresAux.analyticOnNhd_const_cpow_affine (hbase z₁) _ _ Oφ)).mul
        (analyticOnNhd_const.mul (MPresAux.analyticOnNhd_const_cpow_affine (hbase z₂) _ _ Oφ)))
    have key : Nφ s₀ (b * g) = ((etaFst ν αm hαm (-s₀) z₁ : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s₀) z₂ : ℂˣ) : ℂ) * Nφ s₀ g := by
      refine MPresAux.eq_of_eq_on_halfPlane hOc hOhalf (f := fun s => Nφ s (b * g))
        (g := fun s => ((etaFst ν αm hαm (-s) z₁ : ℂˣ) : ℂ) * ((etaSnd μ αm hαm (-s) z₂ : ℂˣ) : ℂ) * Nφ s g)
        (hNa (b * g)) (hanη.mul (hNa g)) (fun s hs => ?_) hs₀
      rw [hN s hs (b * g), hN s hs g]
      exact (AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral F hαm μ ν s (φf s) (hφf s)) b hb g
    simp only []
    rw [key]
    ring
  ·
    have hc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) := hNjc
    have h1 : Continuous (fun g : AdelicGL2 (𝓞 F) F => Nφ s₀ g) := by
      have := hc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hs₀, Set.mem_univ _⟩)
      exact this
    exact continuous_const.mul h1
  ·
    intro g u hu
    refine MPresAux.eq_of_eq_on_halfPlane hOc hOhalf (f := fun s => Nφ s (g * u)) (g := fun s => Nφ s g)
      (hNa (g * u)) (hNa g) (fun s hs => ?_) hs₀
    rw [hN s hs (g * u), hN s hs g, hWI, hWI]
    congr 1
    funext x
    rw [← mul_assoc]
    exact hφflev s _ u hu
  ·
    intro w
    obtain ⟨W, hWfd, hWm⟩ := hφfKu w
    refine ⟨W, hWfd, fun g => ?_⟩
    haveI := hWfd
    obtain ⟨ι, hι, xs, e, heW, hrep⟩ := MPresAux.exists_eq_sum_apply_smul W

    have key : ∀ k : ↥(archRowIsometrySubgroup F w),
        Nφ s₀ (g * (k : AdelicGL2 (𝓞 F) F)) = ∑ j, Nφ s₀ (g * (xs j : AdelicGL2 (𝓞 F) F)) * e j k := by
      intro k
      refine MPresAux.eq_of_eq_on_halfPlane hOc hOhalf (f := fun s => Nφ s (g * (k : AdelicGL2 (𝓞 F) F)))
        (g := fun s => ∑ j, Nφ s (g * (xs j : AdelicGL2 (𝓞 F) F)) * e j k)
        (hNa _) (Finset.analyticOnNhd_fun_sum Finset.univ fun j _ => (hNa (g * (xs j : AdelicGL2 (𝓞 F) F))).mul analyticOnNhd_const) (fun s hs => ?_) hs₀
      rw [hN s hs, hWI]
      have hpt : ∀ x : AdeleRing (𝓞 F) F,
          φf s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (g * (k : AdelicGL2 (𝓞 F) F)))
            = ∑ j, e j k * φf s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (g * (xs j : AdelicGL2 (𝓞 F) F))) := by
        intro x
        have hm := hrep _ (hWm s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g))
        have hmk := congrFun hm k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hmk
        rw [← mul_assoc, hmk]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc, mul_comm]
      simp only [hpt]
      rw [integral_finsetSum _ (fun j _ => (Integrable.const_mul
        (AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hαm μ ν hμ hν s hs (φf s) (hφf s)
          ((hφfjc.comp (continuous_const.prodMk continuous_id))) (g * (xs j : AdelicGL2 (𝓞 F) F))) _))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, hN s hs, hWI, mul_comm]
    have hfun : (fun k : ↥(archRowIsometrySubgroup F w) =>
        ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 F) F)))
        = ∑ j, (V * Nφ s₀ (g * (xs j : AdelicGL2 (𝓞 F) F))) • e j := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [key k, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hfun]
    exact W.sum_mem fun j _ => W.smul_mem _ (heW j)

end S_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel (solution)
