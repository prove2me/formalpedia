-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1e55461a-74a6-504d-b564-ce98a27f6258

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
import Theorems.Thm_AutomorphicForm_exists_units_eq_inv_mul_unitsMap_sigmaTensor_of_norm_eq_one
import Theorems.Thm_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
import Theorems.Thm_MeasureTheory_Measure_exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace A1Asm

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

scoped instance topRing_E : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
scoped instance t2_E : T2Space (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.t2Space_tensor K L _
scoped instance lc_E : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.locallyCompactSpace_tensor K L _
scoped instance sc_inf : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := fun v =>
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))
scoped instance sc_E : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) :=
  (AutomorphicForm.archIdentHomeomorph K L).isEmbedding.secondCountableTopology
scoped instance sc_Eop : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_Eu : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
scoped instance lc_Eop : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
scoped instance lc_Eu : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance sc_infop : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_infu : SecondCountableTopology (InfiniteAdeleRing K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
scoped instance lc_infop : LocallyCompactSpace (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
scoped instance lc_infu : LocallyCompactSpace (InfiniteAdeleRing K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace

def sigmaLinear (σ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) where
  toFun := AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ
  map_add' := map_add _
  map_smul' := by
    intro a x
    rw [AutomorphicForm.rightActions_smul_eq, AutomorphicForm.rightActions_smul_eq, map_mul, RingHom.id_apply]
    congr 1
    show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (InfiniteAdeleRing K)) ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) :=
  IsModuleTopology.continuous_of_linearMap (sigmaLinear K L σ)

def sigmaAlgEquiv (σ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K) ≃ₐ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.congr σ (AlgEquiv.refl : InfiniteAdeleRing K ≃ₐ[K] InfiniteAdeleRing K)).toRingEquiv)
    (fun a => by
      change Algebra.TensorProduct.map (σ : L →ₐ[K] L)
          ((AlgEquiv.refl : InfiniteAdeleRing K ≃ₐ[K] InfiniteAdeleRing K) : InfiniteAdeleRing K →ₐ[K] InfiniteAdeleRing K)
          ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)

theorem norm_sigmaTensor (σ : L ≃ₐ[K] L) (x : (L ⊗[K] InfiniteAdeleRing K)) :
    Algebra.norm (InfiniteAdeleRing K) (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x) = Algebra.norm (InfiniteAdeleRing K) x :=
  Algebra.norm_eq_of_algEquiv (sigmaAlgEquiv K L σ) x

theorem continuous_algebraNorm : Continuous (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) → InfiniteAdeleRing K) := by
  classical
  let b := Module.Free.chooseBasis (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have h : (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) → InfiniteAdeleRing K) = fun s => (Algebra.leftMulMatrix b s).det := by
    funext s; exact Algebra.norm_eq_matrix_det b s
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  exact IsModuleTopology.continuous_of_linearMap
    ((Matrix.entryLinearMap (InfiniteAdeleRing K) (InfiniteAdeleRing K) i j).comp (Algebra.leftMulMatrix b).toLinearMap)

def twq (σ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ where
  toFun := fun s => s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s
  map_one' := by simp
  map_mul' := fun a b => by
    rw [map_mul, mul_inv_rev]
    apply Units.ext
    simp only [Units.val_mul]
    ring

theorem twq_apply (σ : L ≃ₐ[K] L) (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) : twq K L σ s = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s := rfl

theorem continuous_twq (σ : L ≃ₐ[K] L) : Continuous (twq K L σ) :=
  continuous_inv.mul (Continuous.units_map _ (continuous_sigmaTensor K L σ))

theorem twq_mem (σ : L ≃ₐ[K] L) (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) : twq K L σ s ∈ (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := by
  rw [MonoidHom.mem_ker, twq_apply, map_mul, map_inv]
  have : Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) (Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s) =
      Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) s := by
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.coe_coe]
    exact norm_sigmaTensor K L σ (s : (L ⊗[K] InfiniteAdeleRing K))
  rw [this, inv_mul_cancel]

def twqU (σ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K)ˣ →* ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker :=
  (twq K L σ).codRestrict _ (twq_mem K L σ)

theorem twqU_apply (σ : L ≃ₐ[K] L) (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) : ((twqU K L σ s : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) : (L ⊗[K] InfiniteAdeleRing K)ˣ) = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s := rfl

theorem continuous_normU : Continuous (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K)ˣ → (InfiniteAdeleRing K)ˣ) :=
  Continuous.units_map _ (continuous_algebraNorm K L)

theorem isClosed_U1 : IsClosed ((Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) :=
  (isClosed_singleton (x := (1 : (InfiniteAdeleRing K)ˣ))).preimage (continuous_normU K L)

scoped instance lc_U1 : LocallyCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := (isClosed_U1 K L).isClosedEmbedding_subtypeVal.locallyCompactSpace

end A1Asm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq.A1Asm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq.A1Asm"

open A1Asm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρE : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρE.IsHaarMeasure]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      (∀ (Θ : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℝ≥0∞), Measurable Θ →
        ∀ (G : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ℝ≥0∞), Measurable G →
          (∀ (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) (v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
              ((v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) : (L ⊗[K] InfiniteAdeleRing K)ˣ) = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s →
              ∫⁻ p, Θ (s * Units.map
                  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p) ∂ρ =
                G v) →
          ∫⁻ s, Θ s ∂ρE = ENNReal.ofReal c * ∫⁻ v, G v ∂θ) ∧
      (∀ (g : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℂ), Integrable g ρE →
        ∀ (G : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ℂ), AEStronglyMeasurable G θ →
          (∀ (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) (v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
              ((v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) : (L ⊗[K] InfiniteAdeleRing K)ˣ) = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s →
              ∫ p, g (s * Units.map
                  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p) ∂ρ =
                G v) →
          Integrable G θ ∧ ∫ s, g s ∂ρE = (c : ℂ) * ∫ v, G v ∂θ) := by
  classical

  set ι : (InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ := (Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)) with hι
  have hιce : Topology.IsClosedEmbedding ι := AutomorphicForm.isClosedEmbedding_unitsMap_includeRight K L
  set N : Subgroup (L ⊗[K] InfiniteAdeleRing K)ˣ := ι.range with hN
  have hNc : IsClosed (N : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
    rw [hN, MonoidHom.coe_range]; exact hιce.isClosed_range
  let eN : (InfiniteAdeleRing K)ˣ ≃ₜ* ↥N :=
    { MonoidHom.ofInjective hιce.injective with
      continuous_toFun := hιce.continuous.subtype_mk _
      continuous_invFun := by
        rw [hιce.isInducing.continuous_iff]
        convert (continuous_subtype_val : Continuous (fun x : ↥N => (x : (L ⊗[K] InfiniteAdeleRing K)ˣ))) using 1
        funext x
        exact MonoidHom.apply_ofInjective_symm hιce.injective x }
  have heN : ∀ p, ((eN p : ↥N) : (L ⊗[K] InfiniteAdeleRing K)ˣ) = ι p := fun p => rfl
  let μN : Measure ↥N := Measure.map eN ρ
  haveI : μN.IsHaarMeasure := eN.isHaarMeasure_map ρ
  haveI : μN.IsMulRightInvariant :=
    ⟨fun g => by
      rw [show (fun x : ↥N => x * g) = (fun x : ↥N => g * x) from funext fun x => mul_comm x g]
      exact map_mul_left_eq_self μN g⟩

  set f : (L ⊗[K] InfiniteAdeleRing K)ˣ →* ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := twqU K L σ with hf
  have hfc : Continuous f := (continuous_twq K L σ).subtype_mk _
  have hfs : Function.Surjective f := by
    intro v
    have hv : Algebra.norm (InfiniteAdeleRing K) ((v : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.mp v.2)
    obtain ⟨s, hs⟩ := AutomorphicForm.exists_units_eq_inv_mul_unitsMap_sigmaTensor_of_norm_eq_one K L σ hgen hdeg (v : (L ⊗[K] InfiniteAdeleRing K)ˣ) hv
    exact ⟨s, Subtype.ext (by rw [hf, twqU_apply]; exact hs.symm)⟩
  have hopen : IsOpen (Set.range f) := by rw [hfs.range_eq]; exact isOpen_univ
  have hNf : ∀ x : (L ⊗[K] InfiniteAdeleRing K)ˣ, x ∈ N ↔ f x = 1 := by
    intro x
    rw [hN, MonoidHom.mem_range]
    have h1 : (∃ y, ι y = x) ↔ x ∈ Set.range ι := Iff.rfl
    rw [h1, hι, ← AutomorphicForm.unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight K L σ hgen x]
    constructor
    · intro h
      apply Subtype.ext
      rw [hf, twqU_apply, h, inv_mul_cancel]
      rfl
    · intro h
      have h' := congrArg (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => (u : (L ⊗[K] InfiniteAdeleRing K)ˣ)) h
      simp only [hf, twqU_apply] at h'
      have h'' : x⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) x = 1 := by simpa using h'
      exact (inv_mul_eq_one.mp h'').symm

  haveI : SigmaCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite ρE := Measure.IsHaarMeasure.sigmaFinite ρE

  obtain ⟨κ, hκ, hmap⟩ :=
    MeasureTheory.Measure.exists_map_apply_out_haarQuotient_eq_smul_restrict_range_of_isOpen_range
      ρE θ f hfc hopen N hNf μN
  rw [hfs.range_eq, Measure.restrict_univ] at hmap

  have hout : ∀ g : (L ⊗[K] InfiniteAdeleRing K)ˣ, ∃ n : ↥N,
      (Quotient.mk'' g : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ).out = (n : (L ⊗[K] InfiniteAdeleRing K)ˣ) * g := by
    intro g
    have h := Quotient.mk_out (s := MulAction.orbitRel N (L ⊗[K] InfiniteAdeleRing K)ˣ) g
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by rw [← hn]; rfl⟩
  have hfout : ∀ g : (L ⊗[K] InfiniteAdeleRing K)ˣ, f ((Quotient.mk'' g : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ).out) = f g := by
    intro g
    obtain ⟨n, hn⟩ := hout g
    rw [hn, map_mul, (hNf n).mp n.2, one_mul]
  have hfm : Measurable fun q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ => f q.out := by
    rw [measurable_from_quotient]
    have : ((fun q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ => f q.out) ∘ Quotient.mk'') = f := funext hfout
    rw [this]
    exact hfc.measurable

  have hcomm : ∀ (p : (InfiniteAdeleRing K)ˣ) (g : (L ⊗[K] InfiniteAdeleRing K)ˣ), ι p * g = g * ι p := fun p g => Units.ext (mul_comm _ _)
  refine ⟨κ, hκ, ?_, ?_⟩
  · intro Θ hΘ Gf hGf hfib
    rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out ρE N hNc μN Θ hΘ]
    have hinner : ∀ q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫⁻ x : ↥N, Θ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN = Gf (f q.out) := by
      intro q
      have hF : Measurable (fun x : ↥N => Θ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out)) :=
        hΘ.comp ((continuous_subtype_val.mul continuous_const).measurable)
      have heNm : Measurable (eN : (InfiniteAdeleRing K)ˣ → ↥N) := eN.continuous.measurable
      have key : ∫⁻ x : ↥N, Θ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN =
          ∫⁻ p, Θ (((eN p : ↥N) : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂ρ := lintegral_map hF heNm
      rw [key]
      have h1 : ∀ p, Θ (((eN p : ↥N) : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) = Θ (q.out * ι p) := fun p => by rw [heN, hcomm]
      simp_rw [h1]
      exact hfib q.out (f q.out) rfl
    simp_rw [hinner]
    rw [← lintegral_map hGf hfm, hmap, lintegral_smul_measure]
    rfl
  · intro g hg Gf hGf hfib
    set HQ := HaarQuotient.measure ρE N μN with hHQ

    set g' : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℂ := hg.1.mk g with hg'
    have hg'm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
    have hgg' : g =ᵐ[ρE] g' := hg.1.ae_eq_mk
    have hg'i : ∫⁻ s, ‖g' s‖ₑ ∂ρE < ∞ := by
      have hae : (fun s => ‖g' s‖ₑ) =ᵐ[ρE] fun s => ‖g s‖ₑ := hgg'.symm.fun_comp (fun z => ‖z‖ₑ)
      rw [lintegral_congr_ae hae]
      exact hg.2
    obtain ⟨-, hint', hW'⟩ :=
      HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
        ρE N hNc μN g' hg'm hg'i

    have hnull : ∀ᵐ q ∂HQ, (fun p : (InfiniteAdeleRing K)ˣ => g (q.out * ι p)) =ᵐ[ρ] fun p => g' (q.out * ι p) := by

      obtain ⟨S, hBS, hSm, hS0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgg')

      set χ : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℂ := S.indicator (fun _ => (1 : ℂ)) with hχ
      have hχm : Measurable χ := measurable_const.indicator hSm
      have hχi : ∫⁻ s, ‖χ s‖ₑ ∂ρE < ∞ := by
        have hle : ∀ s, ‖χ s‖ₑ ≤ S.indicator (fun _ => (1 : ℝ≥0∞)) s := fun s => by
          by_cases hs : s ∈ S
          · simp [hχ, Set.indicator_of_mem hs]
          · simp [hχ, Set.indicator_of_notMem hs]
        refine lt_of_le_of_lt (lintegral_mono hle) ?_
        rw [lintegral_indicator_const hSm, hS0]; simp
      obtain ⟨hae, hint, hW⟩ :=
        HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
          ρE N hNc μN χ hχm hχi
      have hzero : ∫ s, χ s ∂ρE = 0 := by
        rw [hχ, integral_indicator_const (1 : ℂ) hSm, Measure.real, hS0]; simp

      have hinner_re : ∀ q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ,
          Integrable (fun x : ↥N => χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out)) μN →
          (∫ x : ↥N, χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN) =
            ((μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S}).toReal : ℂ) := by
        intro q hq
        have hset : MeasurableSet {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} :=
          hSm.preimage (continuous_subtype_val.mul continuous_const).measurable
        have : (fun x : ↥N => χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out)) = {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S}.indicator (fun _ => (1 : ℂ)) := by
          funext x
          by_cases hx : (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S
          · simp [hχ, Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} from hx)]
          · simp [hχ, Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} from hx)]
        rw [this, integral_indicator_const (1 : ℂ) hset, Measure.real]
        simp
      have hre : ∀ᵐ q ∂HQ, (μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S}).toReal = 0 := by
        have hI : Integrable (fun q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ =>
            (μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S}).toReal) HQ := by
          refine (hint.re).congr ?_
          filter_upwards [hae] with q hq
          show RCLike.re (∫ x : ↥N, χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN) = _
          rw [hinner_re q hq]; simp
        have hz : ∫ q, (μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S}).toReal ∂HQ = 0 := by
          have h1 : ∫ q, (∫ x : ↥N, χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN) ∂HQ = 0 := hW ▸ hzero
          have h2 : ∫ q, RCLike.re (∫ x : ↥N, χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN) ∂HQ = 0 := by
            rw [integral_re hint, h1]; simp
          rw [← h2]
          refine integral_congr_ae ?_
          filter_upwards [hae] with q hq
          show _ = RCLike.re (∫ x : ↥N, χ ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN)
          rw [hinner_re q hq]; simp
        exact (integral_eq_zero_iff_of_nonneg (fun q => ENNReal.toReal_nonneg) hI).mp hz
      filter_upwards [hre, hae] with q hq hqi

      have hfin : μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} < ∞ := by
        have hset : MeasurableSet {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} :=
          hSm.preimage (continuous_subtype_val.mul continuous_const).measurable
        have := hqi.norm.lintegral_lt_top
        refine lt_of_le_of_lt ?_ this
        rw [← lintegral_indicator_one hset]
        refine lintegral_mono fun x => ?_
        by_cases hx : (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S
        · simp [hχ, Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} from hx)]
        · simp [Set.indicator_of_notMem (show x ∉ {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} from hx)]
      have hμ0 : μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hq with h | h
        · exact h
        · exact absurd h hfin.ne

      have hρ0 : ρ {p : (InfiniteAdeleRing K)ˣ | q.out * ι p ∈ S} = 0 := by
        have hset : MeasurableSet {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} :=
          hSm.preimage (continuous_subtype_val.mul continuous_const).measurable
        have h1 : μN {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S} = ρ (eN ⁻¹' {x : ↥N | (x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out ∈ S}) :=
          Measure.map_apply eN.continuous.measurable hset
        rw [hμ0] at h1
        convert h1.symm using 2
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_preimage, heN, hcomm]
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun p hp => ?_) hρ0
      simp only [Set.mem_setOf_eq] at hp ⊢
      exact hBS (by simpa using hp)

    have hinner : ∀ᵐ q ∂HQ, ∫ x : ↥N, g' ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN = Gf (f q.out) := by
      filter_upwards [hnull] with q hq
      have hF : AEStronglyMeasurable (fun x : ↥N => g' ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out)) (Measure.map eN ρ) :=
        (hg'm.comp ((continuous_subtype_val.mul continuous_const).measurable)).aestronglyMeasurable
      have key : ∫ x : ↥N, g' ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN = ∫ p, g' (((eN p : ↥N) : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂ρ :=
        integral_map eN.continuous.measurable.aemeasurable hF
      rw [key]
      have h1 : ∀ p, g' (((eN p : ↥N) : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) = g' (q.out * ι p) := fun p => by rw [heN, hcomm]
      simp_rw [h1]
      rw [← integral_congr_ae hq]
      exact hfib q.out (f q.out) rfl
    have hGfm : AEStronglyMeasurable Gf (Measure.map (fun q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ => f q.out) HQ) := by
      rw [hmap]; exact hGf.smul_measure _
    have hcomp : Integrable (fun q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ => Gf (f q.out)) HQ :=
      hint'.congr hinner
    have hGi : Integrable Gf (ENNReal.ofReal κ • θ) := by
      rw [← hmap]
      exact (integrable_map_measure hGfm hfm.aemeasurable).mpr hcomp
    refine ⟨(integrable_smul_measure (by simpa using hκ) ENNReal.ofReal_ne_top).mp hGi, ?_⟩
    calc ∫ s, g s ∂ρE = ∫ s, g' s ∂ρE := integral_congr_ae hgg'
      _ = ∫ q, (∫ x : ↥N, g' ((x : (L ⊗[K] InfiniteAdeleRing K)ˣ) * q.out) ∂μN) ∂HQ := hW'
      _ = ∫ q, Gf (f q.out) ∂HQ := integral_congr_ae hinner
      _ = ∫ v, Gf v ∂(Measure.map (fun q : MulAction.orbitRel.Quotient N (L ⊗[K] InfiniteAdeleRing K)ˣ => f q.out) HQ) :=
          (integral_map hfm.aemeasurable hGfm).symm
      _ = (κ : ℂ) * ∫ v, Gf v ∂θ := by
          rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal hκ.le, Complex.real_smul]

end S_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq (solution)
