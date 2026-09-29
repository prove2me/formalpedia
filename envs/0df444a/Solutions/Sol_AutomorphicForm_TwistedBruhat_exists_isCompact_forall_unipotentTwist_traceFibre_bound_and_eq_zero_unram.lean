-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e31c112e-e01a-5662-aa6d-4ad263543d53

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
p2m_attr_erase "instance" "instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal NNReal TensorProduct Pointwise

namespace AdelicTraceCoordinates

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

section BaseChangeCoordinates

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem genuineTensorEquiv_tmul (w : AdeleRing (𝓞 K) K) (l : L) :
    M4aHerbrand.Bridge.genuineTensorEquiv K L (w ⊗ₜ[K] l) =
      M4aHerbrand.Bridge.genuineβ K L w * algebraMap L (AdeleRing (𝓞 L) L) l := by
  have h : (w ⊗ₜ[K] l : AdeleRing (𝓞 K) K ⊗[K] L) = (w ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul]

theorem sum_eq_genuineTensorEquiv {ι : Type} [Fintype ι] (c : ι → L) (w : ι → AdeleRing (𝓞 K) K) :
    (∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (c i)) =
      M4aHerbrand.Bridge.genuineTensorEquiv K L (∑ i, w i ⊗ₜ[K] c i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (genuineTensorEquiv_tmul K L (w i) (c i)).symm

end BaseChangeCoordinates

theorem act_sum_mul_algebraMap_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L) (w : ι → AdeleRing (𝓞 K) K) :
    D.act g
        (∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (b i)) =
      ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (g (b i)) := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act, sum_eq_genuineTensorEquiv K L (fun i => b i) w,
    sum_eq_genuineTensorEquiv K L (fun i => g (b i)) w]
  show M4aHerbrand.Bridge.genuineTensorEquiv K L
      ((Algebra.TensorProduct.congr AlgEquiv.refl g) ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm
        (M4aHerbrand.Bridge.genuineTensorEquiv K L (∑ i, w i ⊗ₜ[K] b i)))) = _
  rw [AlgEquiv.symm_apply_apply]
  congr 1
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom,
      AlgHom.id_apply, AlgEquiv.coe_algHom]

theorem exists_continuousAddEquiv_pi_map_eq_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K L) :
    ∃ e : (ι → AdeleRing (𝓞 K) K) ≃ₜ+ AdeleRing (𝓞 L) L,
      (∀ w : ι → AdeleRing (𝓞 K) K,
        e w = ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (b i)) ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        Measure.map e (Measure.pi fun _ : ι => adelicAddHaar (𝓞 K) K) = c • adelicAddHaar (𝓞 L) L := by
  classical
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L (M4aHerbrand.Bridge.continuous_genuineβ K L)
      (M4aHerbrand.Bridge.genuineTensorEquiv K L)
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 L) L

  let bL : Module.Basis ι (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (Algebra.TensorProduct.basis (AdeleRing (𝓞 K) K) b).map (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv
  let eL : (ι → AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L := bL.equivFun.symm
  have heL : ∀ w : ι → AdeleRing (𝓞 K) K,
      eL w = ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) * algebraMap L (AdeleRing (𝓞 L) L) (b i) := by
    intro w
    simp only [eL, bL, Module.Basis.equivFun_symm_apply, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Algebra.TensorProduct.basis_apply, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hc₁ : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hc₂ : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let e : (ι → AdeleRing (𝓞 K) K) ≃ₜ+ AdeleRing (𝓞 L) L :=
    { eL.toAddEquiv with continuous_toFun := hc₁, continuous_invFun := hc₂ }
  refine ⟨e, fun w => heL w, ?_⟩

  refine ⟨(Measure.addHaarScalarFactor (Measure.map e (Measure.pi fun _ : ι => adelicAddHaar (𝓞 K) K))
      (adelicAddHaar (𝓞 L) L) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  · rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul _ _

end

end AdelicTraceCoordinates

namespace AdelicTracePushforward

section

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem genuineTensorEquiv_tmul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : AdeleRing (𝓞 K) K) (l : L) :
    M4aHerbrand.Bridge.genuineTensorEquiv K L (w ⊗ₜ[K] l) =
      M4aHerbrand.Bridge.genuineβ K L w * algebraMap L (AdeleRing (𝓞 L) L) l := by
  have h : (w ⊗ₜ[K] l : AdeleRing (𝓞 K) K ⊗[K] L) = (w ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one, M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul]

theorem exists_eq_smul_of_isAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ' μ : Measure G) [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] :
    ∃ a : ℝ≥0∞, a ≠ 0 ∧ a ≠ ∞ ∧ μ' = a • μ :=
  ⟨μ'.addHaarScalarFactor μ, by exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ).ne',
    ENNReal.coe_ne_top, by rw [← ENNReal.smul_def]; exact Measure.isAddLeftInvariant_eq_smul μ' μ⟩

theorem isAddFundamentalDomain_pi {ι G α : Type*} [Fintype ι] [AddGroup G] [AddAction G α]
    [MeasurableSpace α] {s : Set α} {μ : Measure α} [SigmaFinite μ] (hs : MeasurableSet s)
    (h : IsAddFundamentalDomain G s μ) :
    IsAddFundamentalDomain (ι → G) (Set.pi Set.univ fun _ : ι => s) (Measure.pi fun _ : ι => μ) where
  nullMeasurableSet := (MeasurableSet.univ_pi fun _ => hs).nullMeasurableSet
  ae_covers := by
    have hi : ∀ i : ι, ∀ᵐ w ∂(Measure.pi fun _ : ι => μ), ∃ g : G, g +ᵥ w i ∈ s := fun i =>
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).tendsto_ae.eventually h.ae_covers
    filter_upwards [Filter.eventually_all.2 hi] with w hw
    choose g hg using hw
    exact ⟨g, Set.mem_univ_pi.mpr fun i => hg i⟩
  aedisjoint := by
    intro g g' hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hsub : (g +ᵥ Set.pi Set.univ fun _ : ι => s) ∩ (g' +ᵥ Set.pi Set.univ fun _ : ι => s) ⊆
        Function.eval i ⁻¹' ((g i +ᵥ s) ∩ (g' i +ᵥ s)) := by
      rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
      exact ⟨⟨x i, Set.mem_univ_pi.mp hx i, rfl⟩, ⟨y i, Set.mem_univ_pi.mp hy i, congrFun hxy i⟩⟩
    exact measure_mono_null hsub
      ((Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).preimage_null (h.aedisjoint hi))

theorem map_eq_of_isAddFundamentalDomain {Λ V : Type*} [AddGroup Λ] [Countable Λ] [AddCommGroup V]
    [AddAction Λ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [MeasurableConstVAdd Λ V]
    (μ : Measure V) [μ.IsAddHaarMeasure] [VAddInvariantMeasure Λ V μ]
    (T : V ≃ₜ+ V) (ε : Λ ≃ Λ) (hT : ∀ (l : Λ) (x : V), T (ε l +ᵥ x) = l +ᵥ T x)
    {s : Set V} (hs : IsAddFundamentalDomain Λ s μ) (h0 : μ s ≠ 0) (htop : μ s ≠ ∞) :
    Measure.map T μ = μ := by
  haveI : (Measure.map T μ).IsAddHaarMeasure := T.toAddEquiv.isAddHaarMeasure_map μ T.continuous T.symm.continuous
  haveI : (Measure.map T.symm μ).IsAddHaarMeasure :=
    T.symm.toAddEquiv.isAddHaarMeasure_map μ T.symm.continuous T.continuous
  obtain ⟨κ, -, -, hκ⟩ := exists_eq_smul_of_isAddHaarMeasure (Measure.map T μ) μ
  obtain ⟨κ', -, -, hκ'⟩ := exists_eq_smul_of_isAddHaarMeasure (Measure.map T.symm μ) μ
  have hqmp : Measure.QuasiMeasurePreserving T.toEquiv.symm μ μ := by
    refine ⟨T.symm.continuous.measurable, ?_⟩
    show Measure.map T.symm μ ≪ μ
    rw [hκ']
    exact Measure.smul_absolutelyContinuous
  have himg : IsAddFundamentalDomain Λ (T '' s) μ := hs.image_of_equiv T.toEquiv hqmp ε fun l x => hT l x
  have hme : MeasurableEmbedding (T : V → V) := T.toHomeomorph.measurableEmbedding
  have h1 : μ (T '' s) = μ s := (hs.measure_eq himg).symm
  have h2 : Measure.map T μ (T '' s) = μ s := by rw [hme.map_apply, T.injective.preimage_image]
  rw [hκ, Measure.smul_apply, smul_eq_mul, h1] at h2
  have h3 : κ * μ s = 1 * μ s := by rw [one_mul]; exact h2
  rw [hκ, (ENNReal.mul_left_inj h0 htop).mp h3, one_smul]

section AdeleProjections

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

end AdeleProjections

theorem exists_traceCoords (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ e : (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞 K) K) ≃ₜ+ AdeleRing (𝓞 L) L,
      (∀ (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        e (Fin.cons r w) = traceFibre K L r w) ∧
      (∀ (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L) (r : AdeleRing (𝓞 K) K)
        (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        D.act g (e (Fin.cons r w)) =
          M4aHerbrand.Bridge.genuineβ K L r * algebraMap L (AdeleRing (𝓞 L) L) (Module.finrank K L : L)⁻¹ +
            ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) *
              algebraMap L (AdeleRing (𝓞 L) L) (g (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i))) ∧
      (∀ k : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → K,
        e (fun j => algebraMap K (AdeleRing (𝓞 K) K) (k j)) =
          algebraMap L (AdeleRing (𝓞 L) L)
            (k 0 • (Module.finrank K L : L)⁻¹ + ∑ i, k (Fin.succ i) • (Module.finBasis K (LinearMap.ker
                  (Algebra.trace K L)) i : L))) ∧
      (∀ l : L, ∃ k : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → K,
        algebraMap L (AdeleRing (𝓞 L) L) l = e (fun j => algebraMap K (AdeleRing (𝓞 K) K) (k j))) ∧
      ∃ c₁ : ℝ≥0∞, c₁ ≠ 0 ∧ c₁ ≠ ∞ ∧
        Measure.map e (Measure.pi fun _ : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) =>
              adelicAddHaar (𝓞 K) K) =
          c₁ • adelicAddHaar (𝓞 L) L := by
  classical

  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have h1 : Algebra.trace K L (Module.finrank K L : L)⁻¹ = 1 := by
    rw [show ((Module.finrank K L : L))⁻¹ = algebraMap K L ((Module.finrank K L : K)⁻¹) by
        rw [map_inv₀, map_natCast],
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have hm : Module.finrank K (LinearMap.ker (Algebra.trace K L)) = Module.finrank K L - 1 := by
    have hr : LinearMap.range (Algebra.trace K L) = ⊤ := LinearMap.range_eq_top.mpr fun k =>
      ⟨algebraMap K L (k / Module.finrank K L), by
        rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ k hn]⟩
    have h := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have hli : LinearIndependent K
      (Fin.cons ((Module.finrank K L : L))⁻¹ (fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) :
        Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → L) := by
    refine linearIndependent_finCons.mpr ⟨?_, fun hmem => ?_⟩
    · exact (Module.finBasis K (LinearMap.ker (Algebra.trace K L))).linearIndependent.map'
        (LinearMap.ker (Algebra.trace K L)).subtype (Submodule.ker_subtype _)
    · have hle : Submodule.span K (Set.range fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) ≤
          LinearMap.ker (Algebra.trace K L) :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => (Module.finBasis K (LinearMap.ker (Algebra.trace K
              L)) i).2)
      have h0 := LinearMap.mem_ker.mp (hle hmem)
      rw [h1] at h0
      exact one_ne_zero h0
  have hcard : Fintype.card (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1)) = Module.finrank K L := by
    rw [Fintype.card_fin, hm]
    have : 0 < Module.finrank K L := Module.finrank_pos
    omega
  have hb := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  obtain ⟨e, he, c₁, hc₁0, hc₁t, hmap⟩ := AdelicTraceCoordinates.exists_continuousAddEquiv_pi_map_eq_smul K L
    (basisOfLinearIndependentOfCardEqFinrank hli hcard)
  have hek : ∀ k : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → K,
      e (fun j => algebraMap K (AdeleRing (𝓞 K) K) (k j)) =
        algebraMap L (AdeleRing (𝓞 L) L) (∑ j, k j • basisOfLinearIndependentOfCardEqFinrank hli hcard j) := by
    intro k
    rw [he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [M4aHerbrand.Bridge.genuineβ_compat, Algebra.smul_def, map_mul]
  refine ⟨e, fun r w => ?_, fun D g r w => ?_, fun k => ?_, fun l => ?_, c₁, hc₁0, hc₁t, hmap⟩
  · rw [he, Fin.sum_univ_succ]
    simp only [hb, Fin.cons_zero, Fin.cons_succ, traceFibre]
  · rw [he, AdelicTraceCoordinates.act_sum_mul_algebraMap_eq, Fin.sum_univ_succ]
    simp only [hb, Fin.cons_zero, Fin.cons_succ, map_inv₀, map_natCast]
  · rw [hek, Fin.sum_univ_succ]
    simp only [hb, Fin.cons_zero, Fin.cons_succ]
  · refine ⟨(basisOfLinearIndependentOfCardEqFinrank hli hcard).equivFun l, ?_⟩
    rw [hek]
    simp only [Module.Basis.equivFun_apply, Module.Basis.sum_repr]

end

end AdelicTracePushforward

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace G4DSupp

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

noncomputable def shape (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) : AdelicGL2 (𝓞 L) L :=
  unipotentGL2 u * diagOne a * centralScalar (𝓞 L) L s

theorem diag2 (p q : AdeleRing (𝓞 L) L) : Matrix.diagonal ![p, q] = !![p, 0; 0, q] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem scalar2 (c : AdeleRing (𝓞 L) L) : Matrix.scalar (Fin 2) c = !![c, 0; 0, c] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem shape_coe (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    ((shape L u a s : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![(a : AdeleRing (𝓞 L) L) * s, u * s; 0, s] := by
  show !![(1 : AdeleRing (𝓞 L) L), u; 0, 1] * Matrix.diagonal ![((a : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1] *
      Matrix.scalar (Fin 2) (s : AdeleRing (𝓞 L) L) = _
  simp only [diag2, scalar2, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_neg (u : AdeleRing (𝓞 L) L) :
    (unipotentGL2 (-u) : AdelicGL2 (𝓞 L) L) = (unipotentGL2 u)⁻¹ :=
  (Units.ext rfl : (unipotentGL2 u : AdelicGL2 (𝓞 L) L)⁻¹ = unipotentGL2 (-u)).symm

theorem shape_inv_coe (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    (((shape L u a s)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
      !![((a⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * ((s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L),
          -(((a⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * ((s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * u);
        0, ((s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)] := by
  unfold shape
  rw [mul_inv_rev, mul_inv_rev, ← map_inv, ← map_inv, ← unipotentGL2_neg]
  show Matrix.scalar (Fin 2) (((s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
      (Matrix.diagonal ![((a⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1] * !![(1 : AdeleRing (𝓞 L) L), -u; 0, 1]) = _
  simp only [diag2, scalar2, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem arg_eq_shape (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : AdelicGL2 (𝓞 L) L)
    (w : AdeleRing (𝓞 L) L) :
    k⁻¹ * unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
        diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
        centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) * sigmaAdelicAct K L D σ k =
      k⁻¹ * shape L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L))
        (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
        sigmaAdelicAct K L D σ k := by
  simp only [shape, mul_assoc]

theorem shape_mem_of_arg_mem {S : Set (AdelicGL2 (𝓞 L) L)} {k : AdelicGL2 (𝓞 L) L}
    {Kset : Set (AdelicGL2 (𝓞 L) L)} (hk : k ∈ Kset) (m : AdelicGL2 (𝓞 L) L)
    (h : k⁻¹ * m * sigmaAdelicAct K L D σ k ∈ S) :
    m ∈ Kset * S * (sigmaAdelicAct K L D σ '' Kset)⁻¹ := by
  refine ⟨k * (k⁻¹ * m * sigmaAdelicAct K L D σ k), Set.mul_mem_mul hk h, (sigmaAdelicAct K L D σ k)⁻¹,
    Set.inv_mem_inv.mpr ⟨k, hk, rfl⟩, by group⟩

theorem continuous_entry (i j : Fin 2) :
    Continuous fun m : AdelicGL2 (𝓞 L) L => ((m : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j :=
  Units.continuous_val.matrix_elem i j

theorem isCompact_units_of_val_mem_of_inv_mem {A B : Set (AdeleRing (𝓞 L) L)} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact {x : (AdeleRing (𝓞 L) L)ˣ | (x : AdeleRing (𝓞 L) L) ∈ A ∧ ((x⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) ∈ B} := by
  have h : {x : (AdeleRing (𝓞 L) L)ˣ | (x : AdeleRing (𝓞 L) L) ∈ A ∧ ((x⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) ∈ B} =
      Units.embedProduct (AdeleRing (𝓞 L) L) ⁻¹' (A ×ˢ (MulOpposite.op '' B)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
      MulOpposite.op_inj, exists_eq_right]
  rw [h]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hA.prod (hB.image MulOpposite.continuous_op))

end G4DSupp

namespace G4DSupp

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem shape_apply_one_one (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    ((shape L u a s : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = s := by
  rw [shape_coe]; simp

theorem shape_apply_zero_zero (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    ((shape L u a s : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = a * s := by
  rw [shape_coe]; simp

theorem shape_apply_zero_one (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    ((shape L u a s : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = u * s := by
  rw [shape_coe]; simp

theorem shape_inv_apply_one_one (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    (((shape L u a s)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 =
      ((s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
  rw [shape_inv_coe]; simp

theorem shape_inv_apply_zero_zero (u : AdeleRing (𝓞 L) L) (a s : (AdeleRing (𝓞 L) L)ˣ) :
    (((shape L u a s)⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 =
      ((a⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * ((s⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := by
  rw [shape_inv_coe]; simp

theorem continuous_diagOne : Continuous (diagOne : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 L) L), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 L) L)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

theorem continuous_unitsAct (g : L ≃ₐ[K] L) :
    Continuous (M4aHerbrand.IdeleGaloisDescent.unitsAct D g : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ => (D.act g : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) u
    exact (D.continuous_act g).comp Units.continuous_val
  · show Continuous fun u : (AdeleRing (𝓞 L) L)ˣ =>
      (D.act g : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)
    exact (D.continuous_act g).comp Units.continuous_coe_inv

theorem continuous_traceFibre :
    Continuous fun p : AdeleRing (𝓞 K) K × (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
      traceFibre K L p.1 p.2 := by
  unfold traceFibre
  refine ((M4aHerbrand.Bridge.continuous_genuineβ K L).comp continuous_fst).mul continuous_const |>.add ?_
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((M4aHerbrand.Bridge.continuous_genuineβ K L).comp ((continuous_apply i).comp continuous_snd)).mul
    continuous_const

theorem unitsAct_inv_apply (g : L ≃ₐ[K] L) (x : (AdeleRing (𝓞 L) L)ˣ) :
    M4aHerbrand.IdeleGaloisDescent.unitsAct D g⁻¹ (M4aHerbrand.IdeleGaloisDescent.unitsAct D g x) = x := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

end G4DSupp

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1)
    (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hgood : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v)) :
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        ∀ j : Fin n,
          ∃ (Ct : Set (AdeleRing (𝓞 L) L)ˣ) (Cz : Set (AdeleRing (𝓞 L) L)ˣ) (Cr : Set (AdeleRing (𝓞 K) K))
            (Cw : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K)) (M : ℝ),
            IsCompact Ct ∧ IsCompact Cz ∧ IsCompact Cr ∧ IsCompact Cw ∧ 0 ≤ M ∧
            (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              ‖φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))‖ ≤ M) ∧
            (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              ζ ∉ Cz → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
            (∀ᵐ t ∂(τ j), t ∉ Ct → ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
            (∀ t ∈ Ct, ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              (r ∉ Cr ∨ w' ∉ Cw) → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
            Continuous (fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
                ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
                  (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
              (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                  (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
                φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  intro ks js φ φf hφfac j
  classical

  have hφF : IsFactorizableTestFn L φ := ⟨φa, φf, hφfac.1, hφfac.2.1, hφfac.2.2.2.2.2⟩
  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hφF

  set uA : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ := fun x => M4aHerbrand.IdeleGaloisDescent.unitsAct D σ x with huA
  set Kset : Set (AdelicGL2 (𝓞 L) L) := (adelicMaximalCompact L : Set (AdelicGL2 (𝓞 L) L)) with hKset
  have hKc : IsCompact Kset := isCompact_adelicMaximalCompact L
  set Cm : Set (AdelicGL2 (𝓞 L) L) := Kset * tsupport φ * (sigmaAdelicAct K L D σ '' Kset)⁻¹ with hCm
  have hCmc : IsCompact Cm :=
    ((hKc.mul hφs).mul (hKc.image (continuous_sigmaAdelicAct K L D σ)).inv)
  have hCmic : IsCompact Cm⁻¹ := hCmc.inv

  set e : Fin 2 → Fin 2 → AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L := fun i j m =>
    ((m : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j with he
  have hec : ∀ i j, Continuous (e i j) := fun i j => G4DSupp.continuous_entry L i j
  set f : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L := fun p => e 0 0 p.1 * e 1 1 p.2 with hf
  have hfc : Continuous f := ((hec 0 0).comp continuous_fst).mul ((hec 1 1).comp continuous_snd)
  set g : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L → AdeleRing (𝓞 L) L := fun p => e 0 1 p.1 * e 1 1 p.2 with hg
  have hgc : Continuous g := ((hec 0 1).comp continuous_fst).mul ((hec 1 1).comp continuous_snd)

  set Es : Set (AdeleRing (𝓞 L) L)ˣ := {x | (x : AdeleRing (𝓞 L) L) ∈ e 1 1 '' Cm ∧
    ((x⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) ∈ e 1 1 '' Cm⁻¹} with hEs
  have hEsc : IsCompact Es :=
    G4DSupp.isCompact_units_of_val_mem_of_inv_mem L (hCmc.image (hec 1 1)) (hCmic.image (hec 1 1))
  set Ea : Set (AdeleRing (𝓞 L) L)ˣ := {x | (x : AdeleRing (𝓞 L) L) ∈ f '' (Cm ×ˢ Cm⁻¹) ∧
    ((x⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) ∈ f '' (Cm⁻¹ ×ˢ Cm)} with hEa
  have hEac : IsCompact Ea :=
    G4DSupp.isCompact_units_of_val_mem_of_inv_mem L ((hCmc.prod hCmic).image hfc) ((hCmic.prod hCmc).image hfc)
  set U : Set (AdeleRing (𝓞 L) L) := g '' (Cm ×ˢ Cm⁻¹) with hU
  have hUc : IsCompact U := (hCmc.prod hCmic).image hgc

  have core : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((w) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) ≠ 0 →
      G4DSupp.shape L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ) ∈ Cm := by
    intro t k ζ w hne
    rw [G4DSupp.arg_eq_shape K L D σ] at hne
    exact G4DSupp.shape_mem_of_arg_mem K L D σ k.2 _ (subset_tsupport φ hne)
  have core_s : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((w) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) ≠ 0 → uA ζ ∈ Es := by
    intro t k ζ w hne
    have hm := core t k ζ w hne
    exact ⟨⟨_, hm, G4DSupp.shape_apply_one_one L _ _ _⟩, ⟨_, Set.inv_mem_inv.mpr hm, G4DSupp.shape_inv_apply_one_one L _ _ _⟩⟩
  have core_a : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((w) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) ≠ 0 → uA t * t⁻¹ ∈ Ea := by
    intro t k ζ w hne
    have hm := core t k ζ w hne
    have h00 := G4DSupp.shape_apply_zero_zero L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ)
    have h11 := G4DSupp.shape_apply_one_one L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ)
    have hi00 := G4DSupp.shape_inv_apply_zero_zero L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ)
    have hi11 := G4DSupp.shape_inv_apply_one_one L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ)
    set m := G4DSupp.shape L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ) with hmdef
    refine ⟨⟨(m, m⁻¹), ⟨hm, Set.inv_mem_inv.mpr hm⟩, ?_⟩, ⟨(m⁻¹, m), ⟨Set.inv_mem_inv.mpr hm, hm⟩, ?_⟩⟩
    · show ((m : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 *
        (((m⁻¹ : AdelicGL2 (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = _
      rw [h00, hi11, mul_assoc, Units.mul_inv, mul_one]
    · show (((m⁻¹ : AdelicGL2 (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 *
        ((m : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = _
      rw [hi00, h11, mul_assoc, Units.inv_mul, mul_one]
  have core_u : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((w) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) ≠ 0 → w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) ∈ U := by
    intro t k ζ w hne
    have hm := core t k ζ w hne
    have h01 := G4DSupp.shape_apply_zero_one L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ)
    have hi11 := G4DSupp.shape_inv_apply_one_one L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ)
    set m := G4DSupp.shape L (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (uA t * t⁻¹) (uA ζ) with hmdef
    refine ⟨(m, m⁻¹), ⟨hm, Set.inv_mem_inv.mpr hm⟩, ?_⟩
    show ((m : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
      (((m⁻¹ : AdelicGL2 (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = _
    rw [h01, hi11, mul_assoc, Units.mul_inv, mul_one]

  obtain ⟨Ct, hCtc, hCt⟩ :=
    AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram K L D σ hgen
      Sτ n c τ τfin τarch πs hcpos hlev hτfin hτ0 hgood hgood' hbad harch hfac3 Ea hEac j

  set Cz : Set (AdeleRing (𝓞 L) L)ˣ := M4aHerbrand.IdeleGaloisDescent.unitsAct D σ⁻¹ '' Es with hCz
  have hCzc : IsCompact Cz := hEsc.image (G4DSupp.continuous_unitsAct K L D σ⁻¹)

  obtain ⟨eT, heT, -⟩ := AdelicTracePushforward.exists_traceCoords K L
  set W : Set (AdeleRing (𝓞 L) L) := (fun p : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => p.1 * (p.2 : AdeleRing (𝓞 L) L)) ''
    (U ×ˢ Ct) with hW
  have hWc : IsCompact W := (hUc.prod hCtc).image (continuous_fst.mul (Units.continuous_val.comp continuous_snd))
  set P : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞 K) K) := eT.symm '' W
    with hP
  have hPc : IsCompact P := hWc.image eT.symm.continuous
  set Cr : Set (AdeleRing (𝓞 K) K) := (fun v => v 0) '' P with hCr
  have hCrc : IsCompact Cr := hPc.image (continuous_apply 0)
  set Cw : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :=
    (fun v => Fin.tail v) '' P with hCw
  have hCwc : IsCompact Cw := hPc.image (continuous_pi fun i => continuous_apply _)

  obtain ⟨M, hM⟩ := hφs.exists_bound_of_continuous hφc
  refine ⟨Ct, Cz, Cr, Cw, max M 0, hCtc, hCzc, hCrc, hCwc, le_max_right _ _, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro t k ζ r w'
    exact (hM _).trans (le_max_left _ _)
  ·
    intro t k ζ r w' hζ
    by_contra hne
    exact hζ ⟨uA ζ, core_s t k ζ _ hne, G4DSupp.unitsAct_inv_apply K L D σ ζ⟩
  ·
    filter_upwards [hCt] with t ht
    intro htC k ζ r w'
    by_contra hne
    exact htC (ht (core_a t k ζ _ hne))
  ·
    intro t ht k ζ r w' hrw
    by_contra hne
    have hw : traceFibre K L r w' ∈ W := by
      refine ⟨(traceFibre K L r w' * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L), t), ⟨core_u t k ζ _ hne, ht⟩, ?_⟩
      show traceFibre K L r w' * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) * (t : AdeleRing (𝓞 L) L) = _
      rw [mul_assoc, Units.inv_mul, mul_one]
    have hp : (Fin.cons r w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)) + 1) → AdeleRing (𝓞 K) K) ∈ P := by
      refine ⟨traceFibre K L r w', hw, ?_⟩
      rw [← heT r w', ContinuousAddEquiv.symm_apply_apply]
    rcases hrw with hr | hw'
    · exact hr ⟨_, hp, by simp⟩
    · exact hw' ⟨_, hp, by simp⟩
  ·
    have h1 : Continuous fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
        ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
          (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
        ((p.1.2 : AdelicGL2 (𝓞 L) L))⁻¹ *
          unipotentGL2 (traceFibre K L p.2.2.1 p.2.2.2 * ((p.1.1⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ p.1.1 * p.1.1⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ p.2.1) *
          AutomorphicForm.sigmaAdelicAct K L D σ (p.1.2 : AdelicGL2 (𝓞 L) L) := by
      refine ((((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv).mul ?_).mul ?_).mul ?_ |>.mul ?_
      · refine (AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)).comp ?_
        exact ((G4DSupp.continuous_traceFibre K L).comp (continuous_snd.comp continuous_snd)).mul
          (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_fst))
      · refine (G4DSupp.continuous_diagOne L).comp ?_
        exact ((G4DSupp.continuous_unitsAct K L D σ).comp (continuous_fst.comp continuous_fst)).mul
          ((continuous_fst.comp continuous_fst).inv)
      · exact (G4DSupp.continuous_centralScalar L).comp
          ((G4DSupp.continuous_unitsAct K L D σ).comp (continuous_fst.comp continuous_snd))
      · exact (continuous_sigmaAdelicAct K L D σ).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact hφc.comp h1

end S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram (solution)
