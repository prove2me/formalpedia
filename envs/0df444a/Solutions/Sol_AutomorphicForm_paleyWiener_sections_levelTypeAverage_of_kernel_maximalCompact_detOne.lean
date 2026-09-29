-- Prove2me | solution 1 for AutomorphicForm.paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2b5d56d7-61ed-5669-938f-be34fd982b6f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Theorems.Thm_AutomorphicForm_exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one
import Theorems.Thm_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm FLT.SmoothVectors
open scoped Pointwise

namespace PA2

theorem translate_average_mem
    (K : Type) [Field K] [NumberField K]
    (κ : ↥(adelicMaximalCompact K) → ℂ) (hκ : Continuous κ)
    (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
      P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
    (hPcomm : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
      (∀ w : InfinitePlace K, w.IsReal →
        ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
      ∀ g : AdelicGL2 (𝓞 K) K, P (fun x => φ (x * (k : AdelicGL2 (𝓞 K) K))) g = P φ (g * (k : AdelicGL2 (𝓞 K) K)))
    (w : InfinitePlace K) (W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ)) [FiniteDimensional ℂ W] :
    ∃ W' : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ), FiniteDimensional ℂ W' ∧
      ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → (∀ g : AdelicGL2 (𝓞 K) K, (fun k : ↥(archRowIsometrySubgroup K w) => u (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) →
        ∀ g : AdelicGL2 (𝓞 K) K, (fun k : ↥(archRowIsometrySubgroup K w) => P u (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W' := by
  classical

  have hKw : ∀ k : ↥(archRowIsometrySubgroup K w), (k : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K := by
    intro k
    obtain ⟨k₀, hk₀, hk⟩ := k.2
    rw [mem_adelicMaximalCompact_iff, ← hk]
    refine ⟨?_, fun w' => ?_⟩
    · show glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w k₀)) ∈ finiteIntegralGL2 (𝓞 K) K
      rw [glFin_adelicArchGLIncl]
      exact (finiteIntegralGL2 (𝓞 K) K).one_mem
    · show IsRowIsometry (archComponent K w' (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w k₀))))
      rw [glArch_adelicArchGLIncl]
      by_cases h : w' = w
      · subst h; rw [archComponent_archGLIncl_self]; exact hk₀
      · rw [archComponent_archGLIncl_of_ne K h]; exact isRowIsometry_one
  have hdec := fun k : ↥(archRowIsometrySubgroup K w) =>
    AutomorphicForm.exists_diagOne_sign_mul_centralScalar_mul_eq_of_mem_adelicMaximalCompact K (k : AdelicGL2 (𝓞 K) K) (hKw k)
  choose a z k₁ ha hz hk₁ hdet heq using hdec

  set T : Set (AdeleRing (𝓞 K) K)ˣ := {b | ((b : AdeleRing (𝓞 K) K).2 = 1 ∧
    ∀ v : InfinitePlace K, (b : AdeleRing (𝓞 K) K).1 v = 1 ∨ (b : AdeleRing (𝓞 K) K).1 v = -1)} with hT
  have hTfin : T.Finite := by
    refine Set.Finite.of_injOn (f := fun b : (AdeleRing (𝓞 K) K)ˣ => (b : AdeleRing (𝓞 K) K).1)
      (t := Set.pi Set.univ fun v : InfinitePlace K => ({1, -1} : Set v.Completion)) (fun b hb => ?_) (fun b hb c hc hbc => ?_)
      (Set.Finite.pi fun v => by simp)
    · refine Set.mem_univ_pi.mpr fun v => ?_
      show ((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v ∈ ({1, -1} : Set v.Completion)
      rcases hb.2 v with h | h
      · rw [h]; exact Set.mem_insert _ _
      · rw [h]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · apply Units.ext
      exact Prod.ext hbc (hb.1.trans hc.1.symm)
  have haT : ∀ k : ↥(archRowIsometrySubgroup K w), a k ∈ T := fun k => ha k

  let χ : (AdeleRing (𝓞 K) K)ˣ → (↥(archRowIsometrySubgroup K w) → ℂ) := fun b k => if a k = b then 1 else 0
  let Tb : (AdeleRing (𝓞 K) K)ˣ → (AdelicGL2 (𝓞 K) K → ℂ) → AdelicGL2 (𝓞 K) K → (↥(archRowIsometrySubgroup K w) → ℂ) := fun b u g k =>
    ∫ k', κ k' * u (g * NumberField.AdelicLevel.diagOne (b : (AdeleRing (𝓞 K) K)ˣ) * (k' : AdelicGL2 (𝓞 K) K) *
      (NumberField.AdelicLevel.diagOne (b : (AdeleRing (𝓞 K) K)ˣ))⁻¹ * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
  let W' : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ) := hTfin.toFinset.sup fun b => W.map (LinearMap.mulLeft ℂ (χ b))
  refine ⟨W', inferInstance, fun u hu hW g => ?_⟩

  have hTbW : ∀ b, Tb b u g ∈ W := by
    intro b
    let b' : AdelicGL2 (𝓞 K) K := NumberField.AdelicLevel.diagOne (b : (AdeleRing (𝓞 K) K)ˣ)
    let bW := Module.finBasis ℂ W
    let Fk : adelicMaximalCompact K → W := fun k' =>
      ⟨fun k : ↥(archRowIsometrySubgroup K w) => κ k' * u (g * b' * (k' : AdelicGL2 (𝓞 K) K) * b'⁻¹ * (k : AdelicGL2 (𝓞 K) K)),
        W.smul_mem (κ k') (hW (g * b' * (k' : AdelicGL2 (𝓞 K) K) * b'⁻¹))⟩
    have hFc : Continuous Fk := by
      refine Continuous.subtype_mk (continuous_pi fun k => ?_) _
      exact hκ.mul (hu.comp ((((continuous_const.mul continuous_subtype_val).mul continuous_const)).mul continuous_const))
    let c : Fin (Module.finrank ℂ W) → adelicMaximalCompact K → ℂ := fun i k' => bW.coord i (Fk k')
    have hcc : ∀ i, Continuous (c i) := fun i =>
      (LinearMap.continuous_of_finiteDimensional (bW.coord i)).comp hFc
    have hci : ∀ i, Integrable (c i) (maximalCompactHaar K) := fun i =>
      (hcc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hexp : ∀ (k' : adelicMaximalCompact K) (k : ↥(archRowIsometrySubgroup K w)),
        κ k' * u (g * b' * (k' : AdelicGL2 (𝓞 K) K) * b'⁻¹ * (k : AdelicGL2 (𝓞 K) K)) =
          ∑ i, c i k' * ((bW i : W) : ↥(archRowIsometrySubgroup K w) → ℂ) k := by
      intro k' k
      show ((Fk k' : W) : ↥(archRowIsometrySubgroup K w) → ℂ) k = ∑ i, c i k' * ((bW i : W) : ↥(archRowIsometrySubgroup K w) → ℂ) k
      have h1 := bW.sum_repr (Fk k')
      have h2 := congrArg (fun v : W => ((v : ↥(archRowIsometrySubgroup K w) → ℂ) k)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    have hfun : Tb b u g = ∑ i, (∫ k', c i k' ∂(maximalCompactHaar K)) • ((bW i : W) : ↥(archRowIsometrySubgroup K w) → ℂ) := by
      funext k
      show (∫ k', κ k' * u (g * b' * (k' : AdelicGL2 (𝓞 K) K) * b'⁻¹ * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = _
      simp only [hexp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum _ fun i _ => (hci i).mul_const _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
    rw [hfun]
    exact W.sum_mem fun i _ => W.smul_mem _ (bW i).2

  have hpt : ∀ k : ↥(archRowIsometrySubgroup K w), P u (g * (k : AdelicGL2 (𝓞 K) K)) = Tb (a k) u g k := by
    intro k
    have hcomm := hPcomm u ⟨k₁ k, hk₁ k⟩ (fun v _ => hdet k v)
      (g * NumberField.AdelicLevel.diagOne (a k) * centralScalar (𝓞 K) K (z k))
    have hgk : g * (k : AdelicGL2 (𝓞 K) K) = g * NumberField.AdelicLevel.diagOne (a k) * centralScalar (𝓞 K) K (z k) * k₁ k := by
      rw [heq k]; simp only [mul_assoc]
    rw [hgk]
    show P u (g * NumberField.AdelicLevel.diagOne (a k) * centralScalar (𝓞 K) K (z k) *
        ((⟨k₁ k, hk₁ k⟩ : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)) = _
    rw [← hcomm, hP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k' => ?_)
    show κ k' * u (g * NumberField.AdelicLevel.diagOne (a k) * centralScalar (𝓞 K) K (z k) * (k' : AdelicGL2 (𝓞 K) K) *
        ((⟨k₁ k, hk₁ k⟩ : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)) =
      κ k' * u (g * NumberField.AdelicLevel.diagOne (a k) * (k' : AdelicGL2 (𝓞 K) K) *
        (NumberField.AdelicLevel.diagOne (a k))⁻¹ * (k : AdelicGL2 (𝓞 K) K))
    rw [heq k]
    congr 2
    show g * NumberField.AdelicLevel.diagOne (a k) * centralScalar (𝓞 K) K (z k) * (k' : AdelicGL2 (𝓞 K) K) * k₁ k =
      g * NumberField.AdelicLevel.diagOne (a k) * (k' : AdelicGL2 (𝓞 K) K) * (NumberField.AdelicLevel.diagOne (a k))⁻¹ *
        (NumberField.AdelicLevel.diagOne (a k) * centralScalar (𝓞 K) K (z k) * k₁ k)
    simp only [mul_assoc]
    rw [inv_mul_cancel_left, ← mul_assoc ((k' : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K) (centralScalar (𝓞 K) K (z k)) (k₁ k),
      mul_centralScalar_comm, mul_assoc]
  have hTk : (fun k : ↥(archRowIsometrySubgroup K w) => P u (g * (k : AdelicGL2 (𝓞 K) K))) = ∑ b ∈ hTfin.toFinset, χ b * Tb b u g := by
    funext k
    rw [hpt k, Finset.sum_apply]
    rw [Finset.sum_eq_single (a k)]
    · simp only [χ, Pi.mul_apply, if_true, one_mul]
    · intro b _ hb
      simp only [χ, Pi.mul_apply, if_neg (Ne.symm hb), zero_mul]
    · intro hnot
      exact (hnot (hTfin.mem_toFinset.mpr (haT k))).elim
  rw [hTk]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hle : W.map (LinearMap.mulLeft ℂ (χ b)) ≤ W' :=
    Finset.le_sup (f := fun b => W.map (LinearMap.mulLeft ℂ (χ b))) hb
  exact hle ⟨Tb b u g, hTbW b, rfl⟩

end PA2

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (_hPrange : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        Continuous (P φ) ∧ IsArchKFinite K (P φ) ∧ (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (P φ) (g * u) = (P φ) g) ∧ P φ ∈ archCutSubmodule K tysK)
      (_hPcomm : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K, P (fun x => φ (x * (k : AdelicGL2 (𝓞 K) K))) g = P φ (g * (k : AdelicGL2 (𝓞 K) K)))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t),
    (∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (P (ψf e s))) ∧
    (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => P (ψf e p.1) p.2)) ∧
    (∀ e g, Differentiable ℂ (fun s => P (ψf e s) g)) ∧
    (∀ e s, IsArchKFinite K (P (ψf e s))) ∧
    (∀ e s, IsKfSmooth K (P (ψf e s))) ∧
    (∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => P (ψf e s) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t) ∧
    (∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, P (ψf i s) (g * u) = P (ψf i s) g) ∧
    (∀ i (s : ℂ), P (ψf i s) ∈ archCutSubmodule K tysK) := by
  intro αm hαm κ hκ P hP hPrange hPcomm ιP instP μP νP ψf hψf hψjc hψhol hψK hψsm hψKu hνc hψdec

  have hcont : ∀ e s, Continuous (ψf e s) := fun e s =>
    (hψjc e).comp (continuous_const.prodMk continuous_id)
  have hPfun : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, P φ = fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
    fun φ => funext (hP φ)
  have hR := fun e s => hPrange (ψf e s) (hcont e s) (hψK e s)
  refine ⟨?_, ?_, ?_, fun e s => (hR e s).2.1, ?_, ?_, ?_, fun i s => (hR i s).2.2.1, fun i s => (hR i s).2.2.2⟩
  ·
    intro e s b hb g
    rw [hP, hP, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show κ k * ψf e s (b * g * (k : AdelicGL2 (𝓞 K) K)) = _ * (κ k * ψf e s (g * (k : AdelicGL2 (𝓞 K) K)))
    rw [mul_assoc b g, hψf e s b hb]
    ring
  ·
    intro e
    haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
    have hf : Continuous (Function.uncurry fun (p : ℂ × AdelicGL2 (𝓞 K) K) (k : adelicMaximalCompact K) =>
        κ k * ψf e p.1 (p.2 * (k : AdelicGL2 (𝓞 K) K))) := by
      have h2 : Continuous fun a : (ℂ × AdelicGL2 (𝓞 K) K) × adelicMaximalCompact K =>
          (a.1.1, a.1.2 * (a.2 : AdelicGL2 (𝓞 K) K)) :=
        (continuous_fst.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd))
      exact (hκ.comp continuous_snd).mul ((hψjc e).comp h2)
    have h := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hf isCompact_univ
    simp only [Measure.restrict_univ] at h
    refine (continuous_congr fun p => ?_).mpr h
    rw [hP]
  ·
    intro e g
    have hfun : (fun s => P (ψf e s) g) = fun s => ∫ k, κ k * ψf e s (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      funext s; rw [hP]
    rw [hfun]
    intro s₀

    have hcont2 : Continuous (fun p : ℂ × adelicMaximalCompact K => ψf e p.1 (g * (p.2 : AdelicGL2 (𝓞 K) K))) :=
      (hψjc e).comp (continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
    obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ 2).prod isCompact_univ).bddAbove_image hcont2.norm.continuousOn
    have hMb : ∀ (z : ℂ), z ∈ Metric.closedBall s₀ 2 → ∀ k : adelicMaximalCompact K,
        ‖ψf e z (g * (k : AdelicGL2 (𝓞 K) K))‖ ≤ M := fun z hz k =>
      hM (Set.mem_image_of_mem _ (Set.mk_mem_prod hz (Set.mem_univ k)))

    set F' : ℂ → adelicMaximalCompact K → ℂ := fun s k =>
      κ k * deriv (fun z => ψf e z (g * (k : AdelicGL2 (𝓞 K) K))) s with hF'
    have hderiv : ∀ (k : adelicMaximalCompact K) (s : ℂ),
        HasDerivAt (fun z => κ k * ψf e z (g * (k : AdelicGL2 (𝓞 K) K))) (F' s k) s := fun k s =>
      ((hψhol e (g * (k : AdelicGL2 (𝓞 K) K))).differentiableAt.hasDerivAt).const_mul (κ k)

    have hbound : ∀ (k : adelicMaximalCompact K), ∀ s ∈ Metric.ball s₀ 1, ‖F' s k‖ ≤ ‖κ k‖ * M := by
      intro k s hs
      have hd : ‖deriv (fun z => ψf e z (g * (k : AdelicGL2 (𝓞 K) K))) s‖ ≤ M / 1 := by
        refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one
          (hψhol e (g * (k : AdelicGL2 (𝓞 K) K))).diffContOnCl (fun z hz => hMb z ?_ k)
        rw [Metric.mem_closedBall]
        have h1 : dist z s = 1 := hz
        have h2 : dist s s₀ < 1 := hs
        linarith [dist_triangle z s s₀]
      rw [div_one] at hd
      show ‖κ k * deriv (fun z => ψf e z (g * (k : AdelicGL2 (𝓞 K) K))) s‖ ≤ ‖κ k‖ * M
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)

    have hF'm : AEStronglyMeasurable (F' s₀) (maximalCompactHaar K) := by
      refine (stronglyMeasurable_of_tendsto (u := Filter.atTop)
        (f := fun (n : ℕ) (k : adelicMaximalCompact K) =>
          slope (fun z => κ k * ψf e z (g * (k : AdelicGL2 (𝓞 K) K))) s₀ (s₀ + ((n : ℂ) + 1)⁻¹))
        (fun n => ?_) ?_).aestronglyMeasurable
      · refine Continuous.stronglyMeasurable ?_
        simp only [slope, vsub_eq_sub]
        refine continuous_const.fun_smul ((hκ.fun_mul ((hcont e _).comp ?_)).fun_sub (hκ.fun_mul ((hcont e _).comp ?_))) <;>
          exact continuous_const.mul continuous_subtype_val
      · rw [tendsto_pi_nhds]
        intro k
        have ht : Filter.Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) Filter.atTop (nhdsWithin s₀ {s₀}ᶜ) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
          · have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) Filter.atTop (nhds 0) := by
              have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
              rw [Complex.ofReal_zero] at h
              refine (Filter.tendsto_congr (fun n => ?_)).mp h
              simp only [Function.comp_apply, one_div, Complex.ofReal_inv, Complex.ofReal_add,
                Complex.ofReal_natCast, Complex.ofReal_one]
            simpa using tendsto_const_nhds.add h0
          · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left, inv_eq_zero]
            exact Nat.cast_add_one_ne_zero n
        exact ((hasDerivAt_iff_tendsto_slope.mp (hderiv k s₀)).comp ht)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := maximalCompactHaar K)
      (F := fun s k => κ k * ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) (x₀ := s₀)
      (bound := fun k => ‖κ k‖ * M) (Metric.ball_mem_nhds s₀ zero_lt_one)
      (Filter.Eventually.of_forall fun s =>
        ((hκ.mul ((hcont e s).comp (continuous_const.mul continuous_subtype_val))).aestronglyMeasurable))
      ((hκ.mul ((hcont e s₀).comp (continuous_const.mul continuous_subtype_val))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      hF'm (Filter.Eventually.of_forall hbound)
      ((hκ.norm.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall fun k s _ => hderiv k s)
    exact key.2.differentiableAt
  ·
    intro e s
    have hsm := hψsm e s
    obtain ⟨O, hO, hOS⟩ := isOpen_induced_iff.mp hsm
    have h1O : (1 : AdelicGL2 (𝓞 K) K) ∈ O := by
      have h1 : (⟨1, one_mem _⟩ : finiteAdelicGL2Subgroup K) ∈ Subtype.val ⁻¹' O := by
        rw [hOS]; exact Subgroup.one_mem _
      exact h1
    obtain ⟨m, hm⟩ := AutomorphicForm.exists_nat_principalLevel_inf_finiteAdelicGL2Subgroup_subset_of_mem_nhds_one K O (hO.mem_nhds h1O)
    set M : Ideal (𝓞 K) := Ideal.span {((m + 1 : ℕ) : 𝓞 K)} with hMdef
    have hM : M ≠ ⊥ := by
      rw [hMdef, Ne, Ideal.span_singleton_eq_bot]
      have h : ((m + 1 : ℕ) : 𝓞 K) ≠ 0 := by
        rw [Nat.cast_add_one]
        exact Nat.cast_add_one_ne_zero m
      exact h
    have hinvψ : ∀ u ∈ principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K, ∀ x : AdelicGL2 (𝓞 K) K,
        ψf e s (x * u) = ψf e s x := by
      intro u hu x
      have hst : (⟨u, hu.2⟩ : finiteAdelicGL2Subgroup K) ∈
          MulAction.stabilizer (finiteAdelicGL2Subgroup K)
            (RightTranslationFn.mk (ψf e s) : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ) := by
        have h' : (⟨u, hu.2⟩ : finiteAdelicGL2Subgroup K) ∈ Subtype.val ⁻¹' O := hm hu
        rw [hOS] at h'
        exact h'
      have h2 := MulAction.mem_stabilizer_iff.mp hst
      have h3 := congrArg (fun F : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ => F.toFun x) h2
      simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul] at h3
      exact h3
    have hinvP : ∀ (x : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K,
        P (ψf e s) (x * u) = P (ψf e s) x := by
      intro x u hu
      rw [hP, hP]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      show κ k * ψf e s (x * u * (k : AdelicGL2 (𝓞 K) K)) = κ k * ψf e s (x * (k : AdelicGL2 (𝓞 K) K))
      have hk' := NumberField.AdelicLevel.conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
        K M ((k : AdelicGL2 (𝓞 K) K)⁻¹) (inv_mem k.2) u hu
      rw [inv_inv] at hk'
      have hx : x * u * (k : AdelicGL2 (𝓞 K) K) =
          x * (k : AdelicGL2 (𝓞 K) K) * ((k : AdelicGL2 (𝓞 K) K)⁻¹ * u * (k : AdelicGL2 (𝓞 K) K)) := by
        simp only [mul_assoc, mul_inv_cancel_left]
      rw [hx, hinvψ _ hk' (x * (k : AdelicGL2 (𝓞 K) K))]
    show IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup K)
      (RightTranslationFn.mk (P (ψf e s)) : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K))
    have hVopen : IsOpen (((principalLevel (𝓞 K) K M).subgroupOf (finiteAdelicGL2Subgroup K) :
        Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K)) :=
      (AutomorphicForm.isOpen_principalLevel K M hM).preimage continuous_subtype_val
    refine Subgroup.isOpen_mono ?_ hVopen
    intro k hk
    rw [MulAction.mem_stabilizer_iff]
    refine RightTranslationFn.ext fun x => ?_
    rw [Subgroup.smul_def, RightTranslationFn.toFun_smul]
    exact hinvP x k ⟨Subgroup.mem_subgroupOf.1 hk, k.2⟩
  ·
    intro e w
    obtain ⟨W, hWfd, hW⟩ := hψKu e w
    haveI : FiniteDimensional ℂ W := hWfd
    obtain ⟨W', hW'fd, hmem⟩ := PA2.translate_average_mem K κ hκ P hP hPcomm w W
    exact ⟨W', hW'fd, fun s g => hmem (ψf e s) (hcont e s) (hW s) g⟩
  ·
    intro e n σ₀ C hC
    have hCK : IsCompact (C * ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K))) :=
      hC.mul (isCompact_adelicMaximalCompact K)
    obtain ⟨m, hmi, ⟨B, hB⟩, hm⟩ := hψdec e n σ₀ _ hCK
    set Cκ : ℝ := ∫ k, ‖κ k‖ ∂(maximalCompactHaar K) with hCκ
    have hCκ0 : 0 ≤ Cκ := integral_nonneg fun _ => norm_nonneg _
    refine ⟨fun t => Cκ * m t, hmi.const_mul Cκ, ⟨Cκ * max B 0, fun t => ?_⟩, ?_⟩
    · have h0 : m t ≤ max B 0 := (hB t).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left h0 hCκ0
    · intro σ' hσ' t g hg
      rw [hP]
      have hmt : 0 ≤ m t := by
        obtain ⟨k₀⟩ := (inferInstance : Nonempty (adelicMaximalCompact K))
        have := hm σ' hσ' t (g * (k₀ : AdelicGL2 (𝓞 K) K)) (Set.mul_mem_mul hg k₀.2)
        exact le_trans (by positivity) this
      have hpt : ∀ k : adelicMaximalCompact K,
          (1 + |t|) ^ n * ‖κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))‖ ≤ ‖κ k‖ * m t := by
        intro k
        rw [norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hm σ' hσ' t _ (Set.mul_mem_mul hg k.2)) (norm_nonneg _)
      have hint : Integrable (fun k : adelicMaximalCompact K => ‖κ k‖ * m t) (maximalCompactHaar K) :=
        (hκ.norm.mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc (1 + |t|) ^ n * ‖∫ k, κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖
          ≤ (1 + |t|) ^ n * ∫ k, ‖κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) :=
            mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ = ∫ k, (1 + |t|) ^ n * ‖κ k * ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) :=
            (integral_const_mul _ _).symm
        _ ≤ ∫ k, ‖κ k‖ * m t ∂(maximalCompactHaar K) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => by positivity) hint
              (Filter.Eventually.of_forall hpt)
        _ = Cκ * m t := by rw [integral_mul_const, hCκ]

end S_AutomorphicForm_paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
end P2MW
export P2MW.S_AutomorphicForm_paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne (solution)
