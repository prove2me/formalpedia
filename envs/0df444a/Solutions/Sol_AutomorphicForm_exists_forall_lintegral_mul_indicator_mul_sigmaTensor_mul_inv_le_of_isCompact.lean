-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d499d450-3cd2-53fc-8b60-d063ea77f74f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace PccTorus
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
theorem diagUnits2_mul (a b c d : Aˣ) : diagUnits2 (a * c) (b * d) = diagUnits2 a b * diagUnits2 c d := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
theorem continuous_diagUnits2 : Continuous fun p : Aˣ × Aˣ => diagUnits2 p.1 p.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [Function.comp_def] using Units.continuous_val.comp continuous_fst
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa [Function.comp_def] using Units.continuous_val.comp continuous_snd
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_fst
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_snd
end PccTorus

namespace TVU

section Key

variable {P G : Type*} [CommGroup P] [Group G] [MeasurableSpace P] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableMul₂ P] [MeasurableInv P]
  (ι : P →* G) (hι : Measurable ι)
  (ν : Measure P) [SFinite ν] [ν.IsInvInvariant] [ν.IsMulLeftInvariant]
  (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]

include hι in

theorem lintegral_mul_lintegral_comp_eq
    (β Φ : G → ℝ≥0∞) (hβ : Measurable β) (hΦ : Measurable Φ)
    (h1 : ∀ g, ∫⁻ p, β (ι p * g) ∂ν = 1) :
    ∫⁻ g, β g * ∫⁻ p, Φ (ι p * g) ∂ν ∂μ = ∫⁻ g, Φ g ∂μ := by
  have hm1 : Measurable (Function.uncurry fun (g : G) (p : P) => β g * Φ (ι p * g)) :=
    (hβ.comp measurable_fst).mul (hΦ.comp ((hι.comp measurable_snd).mul measurable_fst))
  have hm2 : Measurable (Function.uncurry fun (p : P) (g : G) => β (ι p⁻¹ * g) * Φ g) :=
    (hβ.comp (((hι.comp (measurable_inv.comp measurable_fst))).mul measurable_snd)).mul (hΦ.comp measurable_snd)
  calc ∫⁻ g, β g * ∫⁻ p, Φ (ι p * g) ∂ν ∂μ
      = ∫⁻ g, ∫⁻ p, β g * Φ (ι p * g) ∂ν ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul _ (show Measurable (fun p : P => Φ (ι p * g)) from hΦ.comp (hι.mul_const g))]
    _ = ∫⁻ p, ∫⁻ g, β g * Φ (ι p * g) ∂μ ∂ν := lintegral_lintegral_swap hm1.aemeasurable
    _ = ∫⁻ p, ∫⁻ g, β (ι p⁻¹ * g) * Φ g ∂μ ∂ν := by
        refine lintegral_congr fun p => ?_
        rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β (ι p⁻¹ * x) * Φ x) (ι p)]
        refine lintegral_congr fun x => ?_
        simp only [map_inv, inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ p, β (ι p⁻¹ * g) * Φ g ∂ν ∂μ := (lintegral_lintegral_swap hm2.aemeasurable)
    _ = ∫⁻ g, (∫⁻ p, β (ι p⁻¹ * g) ∂ν) * Φ g ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const _ (show Measurable (fun p : P => β (ι p⁻¹ * g)) from hβ.comp ((hι.comp measurable_inv).mul_const g))]
    _ = ∫⁻ g, Φ g ∂μ := by
        refine lintegral_congr fun g => ?_
        have h : ∫⁻ p, β (ι p⁻¹ * g) ∂ν = 1 := by
          rw [lintegral_inv_eq_self (μ := ν) (fun p => β (ι p * g))]
          exact h1 g
        rw [h, one_mul]

include hι in

theorem lintegral_mul_eq_of_invariant
    (β β' : G → ℝ≥0∞) (hβ : Measurable β) (hβ' : Measurable β')
    (h1 : ∀ g, ∫⁻ p, β (ι p * g) ∂ν = 1) (h1' : ∀ g, ∫⁻ p, β' (ι p * g) ∂ν = 1)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hFι : ∀ p g, F (ι p * g) = F g) :
    ∫⁻ g, β g * F g ∂μ = ∫⁻ g, β' g * F g ∂μ := by
  have h := lintegral_mul_lintegral_comp_eq ι hι ν μ β (fun g => β' g * F g) hβ (hβ'.mul hF) h1
  have hin : ∀ g, ∫⁻ p, β' (ι p * g) * F (ι p * g) ∂ν = F g := by
    intro g
    simp_rw [hFι]
    rw [lintegral_mul_const _ (show Measurable (fun p : P => β' (ι p * g)) from hβ'.comp (hι.mul_const g)), h1' g, one_mul]
  simp_rw [hin] at h
  exact h

include hι in

theorem measure_mul_lintegral_mul_indicator_le
    (β : G → ℝ≥0∞) (hβ : Measurable β) (h1 : ∀ g, ∫⁻ p, β (ι p * g) ∂ν = 1)
    (T : Set G) (U : Set P) (hU : MeasurableSet U) (C' S : Set G) (hSm : MeasurableSet S)
    (hS : ∀ p ∈ U, ∀ c ∈ C', ι p * c ∈ S) (hT : ∀ g ∈ T, ∃ p : P, ∃ c ∈ C', g = ι p * c) :
    ν U * ∫⁻ g, β g * T.indicator 1 g ∂μ ≤ μ S := by
  have hkey := lintegral_mul_lintegral_comp_eq ι hι ν μ β (S.indicator 1) hβ (measurable_one.indicator hSm) h1
  rw [lintegral_indicator_one hSm] at hkey
  rw [← hkey]
  refine (lintegral_const_mul_le _ _).trans (lintegral_mono fun g => ?_)
  by_cases hg : g ∈ T
  · obtain ⟨p₀, c, hc, rfl⟩ := hT g hg
    rw [Set.indicator_of_mem hg, Pi.one_apply, mul_one]
    have hνU : ν U ≤ ∫⁻ p, S.indicator 1 (ι p * (ι p₀ * c)) ∂ν := by
      calc ν U = ν ((fun p => p₀ * p) ⁻¹' U) := (measure_preimage_mul ν p₀ U).symm
        _ = ∫⁻ p, ((fun p => p₀ * p) ⁻¹' U).indicator 1 p ∂ν :=
            (lintegral_indicator_one (measurable_const_mul p₀ hU)).symm
        _ ≤ ∫⁻ p, S.indicator 1 (ι p * (ι p₀ * c)) ∂ν := lintegral_mono fun p => ?_
      by_cases hp : p ∈ (fun p => p₀ * p) ⁻¹' U
      · have hmem : ι p * (ι p₀ * c) ∈ S := by
          have : ι p * (ι p₀ * c) = ι (p₀ * p) * c := by rw [← mul_assoc, ← map_mul, mul_comm p p₀]
          rw [this]
          exact hS _ hp _ hc
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hmem]
        exact le_rfl
      · rw [Set.indicator_of_notMem hp]
        exact bot_le
    calc ν U * β (ι p₀ * c) = β (ι p₀ * c) * ν U := mul_comm _ _
      _ ≤ β (ι p₀ * c) * ∫⁻ p, S.indicator 1 (ι p * (ι p₀ * c)) ∂ν := by gcongr
  · rw [Set.indicator_of_notMem hg, mul_zero, mul_zero]
    exact bot_le

end Key

section EAlg

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

local notation "E" => (L ⊗[K] InfiniteAdeleRing K)
local notation "K∞" => (InfiniteAdeleRing K)

noncomputable def inclU : K∞ˣ →* Eˣ :=
  Units.map ((Algebra.TensorProduct.includeRight : K∞ →ₐ[K] E) : K∞ →* E)

noncomputable def inclP : K∞ˣ × K∞ˣ →* Eˣ × Eˣ := MonoidHom.prodMap (inclU K L) (inclU K L)

noncomputable def twq (σ : L ≃ₐ[K] L) (a : Eˣ) : Eˣ :=
  Units.map (AutomorphicForm.sigmaTensor K L K∞ σ).toMonoidHom a * a⁻¹

noncomputable def twqP (σ : L ≃ₐ[K] L) (a : Eˣ × Eˣ) : Eˣ × Eˣ := (twq K L σ a.1, twq K L σ a.2)

theorem coe_inclU (p : K∞ˣ) : ((inclU K L p : Eˣ) : E) = (1 : L) ⊗ₜ (p : K∞) := rfl

theorem sigmaTensor_one_tmul (σ : L ≃ₐ[K] L) (x : K∞) :
    AutomorphicForm.sigmaTensor K L K∞ σ ((1 : L) ⊗ₜ x) = (1 : L) ⊗ₜ x := by
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem twq_mul (σ : L ≃ₐ[K] L) (a b : Eˣ) : twq K L σ (a * b) = twq K L σ a * twq K L σ b := by
  rw [twq, twq, twq, map_mul, mul_inv_rev]
  apply Units.ext
  simp only [Units.val_mul]
  ring

theorem twq_inclU_mul (σ : L ≃ₐ[K] L) (p : K∞ˣ) (a : Eˣ) : twq K L σ (inclU K L p * a) = twq K L σ a := by
  have h0 : Units.map (AutomorphicForm.sigmaTensor K L K∞ σ).toMonoidHom (inclU K L p) = inclU K L p := by
    apply Units.ext
    change AutomorphicForm.sigmaTensor K L K∞ σ ((1 : L) ⊗ₜ (p : K∞)) = (1 : L) ⊗ₜ (p : K∞)
    exact sigmaTensor_one_tmul K L σ p
  have h : twq K L σ (inclU K L p) = 1 := by
    rw [twq, h0, mul_inv_cancel]
  rw [twq_mul, h, one_mul]

theorem twqP_inclP_mul (σ : L ≃ₐ[K] L) (p : K∞ˣ × K∞ˣ) (a : Eˣ × Eˣ) :
    twqP K L σ (inclP K L p * a) = twqP K L σ a := by
  simp only [twqP, inclP, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, Prod.fst_mul, Prod.snd_mul, twq_inclU_mul]

theorem twqP_mul (σ : L ≃ₐ[K] L) (a b : Eˣ × Eˣ) : twqP K L σ (a * b) = twqP K L σ a * twqP K L σ b := by
  simp only [twqP, Prod.fst_mul, Prod.snd_mul, twq_mul, Prod.mk_mul_mk]

theorem twq_inv (σ : L ≃ₐ[K] L) (a : Eˣ) : twq K L σ a⁻¹ = (twq K L σ a)⁻¹ := by
  rw [twq, twq, mul_inv_rev, inv_inv, ← map_inv]
  apply Units.ext
  simp only [Units.val_mul]
  ring

theorem twqP_inv (σ : L ≃ₐ[K] L) (a : Eˣ × Eˣ) : twqP K L σ a⁻¹ = (twqP K L σ a)⁻¹ := by
  simp only [twqP, Prod.fst_inv, Prod.snd_inv, twq_inv, Prod.inv_mk]

theorem inclU_mul_comm (p : K∞ˣ) (a : Eˣ) : inclU K L p * a = a * inclU K L p := by
  apply Units.ext
  simp only [Units.val_mul]
  exact mul_comm _ _

theorem inclP_mul_comm (p : K∞ˣ × K∞ˣ) (a : Eˣ × Eˣ) : inclP K L p * a = a * inclP K L p :=
  Prod.ext (inclU_mul_comm K L p.1 a.1) (inclU_mul_comm K L p.2 a.2)

theorem toTensorGL_diagUnits2_mul (p : K∞ˣ × K∞ˣ) (a : Eˣ × Eˣ) :
    AutomorphicForm.toTensorGL K L K∞ (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2 =
      diagUnits2 (inclP K L p * a).1 (inclP K L p * a).2 := by
  apply Units.ext
  ext i j
  simp only [AutomorphicForm.toTensorGL, Units.val_mul, Matrix.GeneralLinearGroup.map_apply,
    LanglandsTunnell.CubicInduction.coe_diagUnits2, inclP, MonoidHom.prodMap, MonoidHom.prod_apply,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, Prod.fst_mul, Prod.snd_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, coe_inclU]

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
theorem secondCountableTopology_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem secondCountableTopology_E : SecondCountableTopology E :=
  haveI := secondCountableTopology_infiniteAdeleRing' L
  (AutomorphicForm.archIdentHomeomorph K L).secondCountableTopology

theorem secondCountableTopology_unitsE : SecondCountableTopology Eˣ := by
  haveI := secondCountableTopology_E K L
  haveI : SecondCountableTopology Eᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_unitsE : LocallyCompactSpace Eˣ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L K∞
  haveI := AutomorphicForm.t2Space_tensor K L K∞
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L K∞
  haveI : LocallyCompactSpace Eᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountableTopology_unitsK : SecondCountableTopology K∞ˣ := by
  haveI := secondCountableTopology_infiniteAdeleRing' K
  haveI : SecondCountableTopology K∞ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_unitsK : LocallyCompactSpace K∞ˣ := by
  haveI : LocallyCompactSpace K∞ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem continuous_includeRight :
    Continuous ((Algebra.TensorProduct.includeRight : K∞ →ₐ[K] E) : K∞ → E) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L K∞
  have h : ((Algebra.TensorProduct.includeRight : K∞ →ₐ[K] E) : K∞ → E) = fun x => x • (1 : E) := by
    funext x
    rw [AutomorphicForm.rightActions_smul_eq, mul_one]
    rfl
  rw [h]
  exact continuous_id.fun_smul continuous_const

theorem continuous_inclU : Continuous (inclU K L) :=
  Continuous.units_map _ (continuous_includeRight K L)

theorem continuous_inclP : Continuous (inclP K L) :=
  ((continuous_inclU K L).comp continuous_fst).prodMk ((continuous_inclU K L).comp continuous_snd)

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L K∞ σ) := by
  haveI hTR : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L K∞
  let f : E →ₗ[K∞] E :=
    { toFun := AutomorphicForm.sigmaTensor K L K∞ σ, map_add' := map_add _,
      map_smul' := by
        intro a z
        rw [AutomorphicForm.rightActions_smul_eq, AutomorphicForm.rightActions_smul_eq, map_mul]
        congr 1
        simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul] }
  haveI : ContinuousAdd E := hTR.toContinuousAdd
  exact (IsModuleTopology.continuous_of_linearMap f).congr (fun _ => rfl)

theorem continuous_twq (σ : L ≃ₐ[K] L) : Continuous (twq K L σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L K∞
  exact (Continuous.units_map _ (continuous_sigmaTensor K L σ)).mul continuous_inv

theorem continuous_twqP (σ : L ≃ₐ[K] L) : Continuous (twqP K L σ) :=
  ((continuous_twq K L σ).comp continuous_fst).prodMk ((continuous_twq K L σ).comp continuous_snd)

end EAlg

end TVU

set_option maxHeartbeats 3200000 in
open TVU in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (β : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ1 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2)
          ∂(νA.prod νA) = 1)
    (Ω : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ)) (hΩ : IsCompact Ω) :
    ∃ V : ℝ≥0∞, V ≠ ∞ ∧ ∀ e : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
          ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
            Ω.indicator (fun _ => (1 : ℝ≥0∞))
              (e.1 * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹, e.2 * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) ∂(ρ.prod ρ) ≤ V := by
  classical

  haveI hTR : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
  haveI : T2Space (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.t2Space_tensor K L _
  haveI := secondCountableTopology_unitsE K L
  haveI := locallyCompactSpace_unitsE K L
  haveI := secondCountableTopology_unitsK K
  haveI := locallyCompactSpace_unitsK K
  letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _
  haveI : BorelSpace ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) := Prod.borelSpace
  haveI : BorelSpace ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := Prod.borelSpace
  haveI : SigmaCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (InfiniteAdeleRing K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite ρ := Measure.IsHaarMeasure.sigmaFinite ρ
  haveI : SigmaFinite νA := Measure.IsHaarMeasure.sigmaFinite νA
  haveI : (ρ.prod ρ).IsHaarMeasure := inferInstance
  haveI : (νA.prod νA).IsHaarMeasure := inferInstance
  haveI : (νA.prod νA).Regular := by
    obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) :=
      inferInstance
    rw [Measure.isMulLeftInvariant_eq_smul (νA.prod νA) (Measure.haarMeasure K₀)]
    infer_instance
  haveI : (νA.prod νA).IsInvInvariant := inferInstance
  haveI : MeasurableMul₂ ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) :=
    ContinuousMul.measurableMul₂
  haveI : MeasurableMul₂ ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := ContinuousMul.measurableMul₂
  haveI : MeasurableInv ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := ContinuousInv.measurableInv
  haveI : SFinite (ρ.prod ρ) := inferInstance
  haveI : SFinite (νA.prod νA) := inferInstance
  haveI : (ρ.prod ρ).IsMulLeftInvariant := inferInstance
  haveI : (νA.prod νA).IsMulLeftInvariant := inferInstance

  let ι : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ :=
    inclP K L
  have hι : Measurable ι := (continuous_inclP K L).measurable
  let q : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ →
      (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ := twqP K L σ
  have hqc : Continuous q := continuous_twqP K L σ
  let βG : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ → ℝ≥0∞ :=
    fun a => ENNReal.ofReal (β (diagUnits2 a.1 a.2))
  have hdiagc : Continuous fun a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ =>
      diagUnits2 a.1 a.2 := PccTorus.continuous_diagUnits2
  have hβG : Measurable βG := ENNReal.measurable_ofReal.comp (hβm.comp hdiagc.measurable)

  have hβG1 : ∀ c g : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      ∫⁻ p, βG (c * (ι p * g)) ∂(νA.prod νA) = 1 := by
    intro c g
    have hfun : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
        β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 (c * g).1 (c * g).2) =
          β (diagUnits2 (c * (ι p * g)).1 (c * (ι p * g)).2) := by
      intro p
      have hh : inclP K L p * (c * g) = c * (ι p * g) := by
        rw [← mul_assoc, inclP_mul_comm, mul_assoc]
      rw [toTensorGL_diagUnits2_mul, hh]
    have h1 := hβ1 (c * g)
    simp_rw [hfun] at h1
    have hint : Integrable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        β (diagUnits2 (c * (ι p * g)).1 (c * (ι p * g)).2)) (νA.prod νA) := by
      by_contra h
      rw [integral_undef h] at h1
      exact zero_ne_one h1
    have h2 := (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun p => hβ0 _)).symm
    rw [h1, ENNReal.ofReal_one] at h2
    exact h2
  have hβG1' : ∀ g : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      ∫⁻ p, βG (ι p * g) ∂(νA.prod νA) = 1 := fun g => by
    have h := hβG1 1 g
    simp only [one_mul] at h
    exact h

  let C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) :=
    (fun x : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
        ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) => x.1⁻¹ * x.2) '' (Ω ×ˢ Ω)
  have hcontC : Continuous (fun x : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
      ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) => x.1⁻¹ * x.2) :=
    continuous_fst.inv.mul continuous_snd
  have hCc : IsCompact C := (hΩ.prod hΩ).image hcontC
  have hTm : MeasurableSet (q ⁻¹' C) := (hCc.isClosed.preimage hqc).measurableSet
  let V : ℝ≥0∞ := ∫⁻ a, βG a * (q ⁻¹' C).indicator 1 a ∂(ρ.prod ρ)

  have hVfin : V ≠ ∞ := by
    obtain ⟨C₁, hC₁, hC₁p⟩ :=
      AutomorphicForm.exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem
        K L σ hgen (Prod.fst '' C) (hCc.image continuous_fst)
    obtain ⟨C₂, hC₂, hC₂p⟩ :=
      AutomorphicForm.exists_isCompact_forall_exists_includeRight_mul_mem_of_sigmaTensor_mul_inv_mem
        K L σ hgen (Prod.snd '' C) (hCc.image continuous_snd)
    obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)
    have hU0 : (νA.prod νA) U ≠ 0 := (Measure.measure_pos_of_mem_nhds (νA.prod νA) hU1).ne'
    let S : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) :=
      (fun x : ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) ×
          ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) => ι x.1 * x.2) '' (U ×ˢ (C₁ ×ˢ C₂))
    have hcontS : Continuous (fun x : ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) ×
          ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) => ι x.1 * x.2) :=
      ((continuous_inclP K L).comp continuous_fst).mul continuous_snd
    have hSc : IsCompact S := (hUc.prod (hC₁.prod hC₂)).image hcontS
    have hle := measure_mul_lintegral_mul_indicator_le (P := (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)
          (G := (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ι hι (νA.prod νA) (ρ.prod ρ) βG hβG
        hβG1'
        (q ⁻¹' C) U hUc.isClosed.measurableSet (C₁ ×ˢ C₂) S hSc.isClosed.measurableSet
        (fun p hp c hc => ⟨(p, c), Set.mk_mem_prod hp hc, rfl⟩) ?_
    · intro hV
      change (νA.prod νA) U * V ≤ (ρ.prod ρ) S at hle
      rw [hV, ENNReal.mul_top hU0, top_le_iff] at hle
      exact hSc.measure_lt_top.ne hle
    · intro g hg
      obtain ⟨p₁, hp₁⟩ := hC₁p g.1 ⟨q g, hg, rfl⟩
      obtain ⟨p₂, hp₂⟩ := hC₂p g.2 ⟨q g, hg, rfl⟩
      refine ⟨(p₁⁻¹, p₂⁻¹), (inclU K L p₁ * g.1, inclU K L p₂ * g.2), Set.mk_mem_prod hp₁ hp₂, ?_⟩
      refine Prod.ext ?_ ?_
      · show g.1 = inclU K L p₁⁻¹ * (inclU K L p₁ * g.1)
        rw [map_inv, inv_mul_cancel_left]
      · show g.2 = inclU K L p₂⁻¹ * (inclU K L p₂ * g.2)
        rw [map_inv, inv_mul_cancel_left]
  refine ⟨V, hVfin, fun e => ?_⟩

  have hpt : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      (e.1 * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹,
        e.2 * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) =
        e * q a := fun a => Prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)
  rw [lintegral_congr (fun a => by rw [hpt a])]

  by_cases hS : ∃ a₀ : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, e * q a₀ ∈ Ω
  swap
  · push_neg at hS
    have h0 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ENNReal.ofReal (β (diagUnits2 a.1 a.2)) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (e * q a) = 0 := by
      intro a
      rw [Set.indicator_of_notMem (hS a), mul_zero]
    rw [lintegral_congr h0, lintegral_zero]
    exact bot_le
  obtain ⟨a₀, ha₀⟩ := hS
  have hind : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      Ω.indicator (fun _ => (1 : ℝ≥0∞)) (e * q a) ≤ (q ⁻¹' C).indicator 1 (a₀⁻¹ * a) := by
    intro a
    by_cases ha : e * q a ∈ Ω
    · have hmem : a₀⁻¹ * a ∈ q ⁻¹' C := by
        show q (a₀⁻¹ * a) ∈ C
        refine ⟨(e * q a₀, e * q a), Set.mk_mem_prod ha₀ ha, ?_⟩
        show (e * q a₀)⁻¹ * (e * q a) = q (a₀⁻¹ * a)
        have hq : q (a₀⁻¹ * a) = (q a₀)⁻¹ * q a := by
          show twqP K L σ (a₀⁻¹ * a) = (twqP K L σ a₀)⁻¹ * twqP K L σ a
          rw [twqP_mul, twqP_inv]
        rw [hq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [Set.indicator_of_mem ha, Set.indicator_of_mem hmem, Pi.one_apply]
    · rw [Set.indicator_of_notMem ha]
      exact bot_le
  calc ∫⁻ a, ENNReal.ofReal (β (diagUnits2 a.1 a.2)) * Ω.indicator (fun _ => (1 : ℝ≥0∞)) (e * q a) ∂(ρ.prod ρ)
      ≤ ∫⁻ a, βG a * (q ⁻¹' C).indicator 1 (a₀⁻¹ * a) ∂(ρ.prod ρ) :=
        lintegral_mono fun a => mul_le_mul_right (hind a) (βG a)
    _ = ∫⁻ b, βG (a₀ * b) * (q ⁻¹' C).indicator 1 b ∂(ρ.prod ρ) := by
        rw [← lintegral_mul_left_eq_self (μ := ρ.prod ρ)
          (fun b => βG (a₀ * b) * (q ⁻¹' C).indicator 1 b) a₀⁻¹]
        refine lintegral_congr fun x => ?_
        simp only [mul_inv_cancel_left]
    _ = V := by
        refine lintegral_mul_eq_of_invariant (P := (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)
          (G := (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ι hι (νA.prod νA) (ρ.prod ρ) (fun b => βG (a₀ * b)) βG
          (hβG.comp (measurable_const_mul a₀)) hβG (fun g => hβG1 a₀ g) hβG1'
          ((q ⁻¹' C).indicator 1) (measurable_one.indicator hTm) (fun p g => ?_)
        have hq : q (ι p * g) = q g := twqP_inclP_mul K L σ p g
        simp only [Set.indicator_apply, Set.mem_preimage, hq, Pi.one_apply]

end S_AutomorphicForm_exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_mul_indicator_mul_sigmaTensor_mul_inv_le_of_isCompact (solution)
