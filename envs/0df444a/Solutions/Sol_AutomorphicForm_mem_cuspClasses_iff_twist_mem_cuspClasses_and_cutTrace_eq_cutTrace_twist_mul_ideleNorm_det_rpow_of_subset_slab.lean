-- Prove2me | solution 1 for AutomorphicForm.mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b74bea2b-756c-5a27-b677-785ae0d0b210

import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab
import Theorems.Thm_AutomorphicForm_rightConv_mul_ideleNorm_det_rpow_neg_half
import Theorems.Thm_AutomorphicForm_mul_ideleNorm_det_rpow_mem_archCutSubmodule
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace TwistIsoReduce

open NumberField IsDedekindDomain AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def mult (s : ℝ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun g => (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ s : ℝ) : ℂ)

theorem mult_mul_mult (s t : ℝ) (g : AdelicGL2 (𝓞 K) K) : mult K s g * mult K t g = mult K (s + t) g := by
  simp only [mult, ← Complex.ofReal_mul]
  rw [← Real.rpow_add (NumberField.TateGlobal.ideleNorm_pos _)]

theorem mult_zero (g : AdelicGL2 (𝓞 K) K) : mult K 0 g = 1 := by
  simp [mult]

noncomputable def U (s : ℝ) : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) where
  toFun φ := fun g => φ g * mult K s g
  map_add' φ ψ := by funext g; simp only [Pi.add_apply]; ring
  map_smul' c φ := by funext g; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[scoped simp] theorem U_apply (s : ℝ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    U K s φ g = φ g * mult K s g := rfl

theorem U_U_neg (s : ℝ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : U K (-s) (U K s φ) = φ := by
  funext g
  simp only [U_apply, mul_assoc, mult_mul_mult]
  rw [show s + -s = 0 by ring, mult_zero, mul_one]

theorem U_neg_U (s : ℝ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : U K s (U K (-s) φ) = φ := by
  have := U_U_neg K (-s) φ
  rwa [neg_neg] at this

noncomputable def E (s : ℝ) : (AdelicGL2 (𝓞 K) K → ℂ) ≃ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
  { U K s with
    invFun := U K (-s)
    left_inv := fun φ => U_U_neg K s φ
    right_inv := fun φ => U_neg_U K s φ }

@[scoped simp] theorem E_apply (s : ℝ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : E K s φ = U K s φ := rfl

theorem map_eq_of_forall {s : ℝ} {A B : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hAB : ∀ φ ∈ A, U K s φ ∈ B) (hBA : ∀ ψ ∈ B, U K (-s) ψ ∈ A) :
    A.map (E K s : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ)) = B := by
  apply le_antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hAB φ hφ
  · intro ψ hψ
    exact ⟨U K (-s) ψ, hBA ψ hψ, U_neg_U K s ψ⟩

end TwistIsoReduce
p2m_reactivate "P2MW.S_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab.TwistIsoReduce"

open AutomorphicForm TwistIsoReduce in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦdet : ∃ α β : ℝ, 0 < α ∧
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (ξK ξ₀K : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ξ₀K ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (-w) : ℝ) : ℂ))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (f' : AdelicGL2 (𝓞 K) K → ℂ) (hf' : Continuous f') (hfc' : HasCompactSupport f')
    (hff' : ∀ g : AdelicGL2 (𝓞 K) K,
      f' g = f g * (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (π : HeckeEigensystem K ℂ) :
    (π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK ↔
      π.twist (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)) ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK) ∧
    cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π tysK f hf hfc =
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ₀K N SK
        (π.twist (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ))) tysK f' hf' hfc' := by
  classical

  set P := (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) with hP
  set χ : HeightOneSpectrum (𝓞 K) → ℂ := (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(w / 2)) : ℝ) : ℂ)) with hχdef
  have hχ0 : ∀ v, χ v ≠ 0 := by
    intro v; simp only [hχdef, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _).ne'

  set χ' : HeightOneSpectrum (𝓞 K) → ℂ := (fun v : HeightOneSpectrum (𝓞 K) =>
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))) ^ (-(-w / 2)) : ℝ) : ℂ)) with hχ'def
  have hχχ' : ∀ v, χ' v * χ v = 1 := by
    intro v
    simp only [hχdef, hχ'def, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    rw [← Real.rpow_add (NumberField.TateGlobal.ideleNorm_pos _), show -(-w / 2) + -(w / 2) = (0 : ℝ) by ring,
      Real.rpow_zero]
  have htwist_back : (π.twist χ).twist χ' = π := by
    rcases π with ⟨lvl, hlvl, a, b⟩
    simp only [HeckeEigensystem.twist, HeckeEigensystem.mk.injEq, true_and]
    refine ⟨funext fun v => ?_, funext fun v => ?_⟩
    · rw [← mul_assoc, hχχ' v, one_mul]
    · rw [← mul_assoc, ← mul_pow, hχχ' v, one_pow, one_mul]

  have hξ₀' : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((ξ₀K ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (((NumberField.TateGlobal.ideleNorm K z) ^ (-(-w)) : ℝ) : ℂ) := by
    intro z
    rw [hξ₀ z, mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (NumberField.TateGlobal.ideleNorm_pos _)]
    norm_num

  have hfwd : ∀ φ, IsIsotypicCuspFormAt K P ξK N SK π φ →
      IsIsotypicCuspFormAt K P ξ₀K N SK (π.twist χ) (U K (-(w / 2)) φ) := fun φ hφ =>
    AutomorphicForm.isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab K Φ hΦdet SK N ξK ξ₀K w hξ₀ π φ hφ
  have hbwd : ∀ ψ, IsIsotypicCuspFormAt K P ξ₀K N SK (π.twist χ) ψ →
      IsIsotypicCuspFormAt K P ξK N SK π (U K (-(-w / 2)) ψ) := by
    intro ψ hψ
    have := AutomorphicForm.isIsotypicCuspFormAt_twist_mul_ideleNorm_det_rpow_of_subset_slab K Φ hΦdet SK N ξ₀K ξK (-w) hξ₀' (π.twist χ) ψ hψ
    rwa [htwist_back] at this
  have hs : -(-(w / 2)) = -(-w / 2) := by ring

  set V := isotypicCuspSubmodule K P ξK N SK π with hV
  set V' := isotypicCuspSubmodule K P ξ₀K N SK (π.twist χ) with hV'
  set W := archCutSubmodule K tysK with hW
  have hVmap : V.map (E K (-(w / 2)) : _ →ₗ[ℂ] _) = V' := by
    apply map_eq_of_forall K
    · intro φ hφ
      refine Submodule.span_induction (p := fun φ _ => U K (-(w / 2)) φ ∈ V') ?_ ?_ ?_ ?_ hφ
      · exact fun φ h => Submodule.subset_span (hfwd φ h)
      · simp only [map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy
      · intro c x _ hx; simpa only [map_smul] using Submodule.smul_mem _ c hx
    · intro ψ hψ
      refine Submodule.span_induction (p := fun ψ _ => U K (-(-(w / 2))) ψ ∈ V) ?_ ?_ ?_ ?_ hψ
      · intro ψ h
        have := hbwd ψ h
        rw [← hs] at this
        exact Submodule.subset_span this
      · simp only [map_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy
      · intro c x _ hx; simpa only [map_smul] using Submodule.smul_mem _ c hx
  have hWmap : W.map (E K (-(w / 2)) : _ →ₗ[ℂ] _) = W := by
    apply map_eq_of_forall K
    · exact fun φ hφ => AutomorphicForm.mul_ideleNorm_det_rpow_mem_archCutSubmodule K tysK w φ hφ
    · intro ψ hψ
      have := AutomorphicForm.mul_ideleNorm_det_rpow_mem_archCutSubmodule K tysK (-w) ψ hψ
      rwa [← hs] at this
  have hVWmap : (V ⊓ W).map (E K (-(w / 2)) : _ →ₗ[ℂ] _) = V' ⊓ W := by
    rw [Submodule.map_inf _ (E K (-(w / 2))).injective, hVmap, hWmap]

  have hconv : ∀ u, convOp K f' (U K (-(w / 2)) u) = U K (-(w / 2)) (convOp K f u) := by
    intro u; funext g
    rw [convOp_apply, convOp_apply, U_apply]
    exact AutomorphicForm.rightConv_mul_ideleNorm_det_rpow_neg_half K w u f f' hff' g
  have hne : V ≠ ⊥ ↔ V' ≠ ⊥ := by
    rw [← hVmap, Ne, Ne, Submodule.map_eq_bot_iff]
  refine ⟨?_, ?_⟩
  ·
    rw [mem_cuspClasses_iff, mem_cuspClasses_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun v hv => ?_, hne.mp h3⟩
      obtain ⟨ha, hb⟩ := h2 v hv
      exact ⟨by rw [HeckeEigensystem.twist_a, ha, mul_zero], by rw [HeckeEigensystem.twist_b, hb, mul_zero]⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun v hv => ?_, hne.mpr h3⟩
      obtain ⟨ha, hb⟩ := h2 v hv
      rw [HeckeEigensystem.twist_a] at ha
      rw [HeckeEigensystem.twist_b] at hb
      exact ⟨(mul_eq_zero.mp ha).resolve_left (hχ0 v),
        (mul_eq_zero.mp hb).resolve_left (pow_ne_zero 2 (hχ0 v))⟩
  ·
    rw [cutTrace_eq, cutTrace_eq]
    by_cases hmaps : ∀ u ∈ V ⊓ W, convOp K f u ∈ V ⊓ W
    · have hmaps' : ∀ u' ∈ V' ⊓ W, convOp K f' u' ∈ V' ⊓ W := by
        intro u' hu'
        rw [← hVWmap] at hu' ⊢
        obtain ⟨u, hu, rfl⟩ := hu'
        exact ⟨convOp K f u, hmaps u hu, (hconv u).symm⟩
      rw [convTraceOn_eq_traceOn K (continuous_of_mem_isotypicCuspSubmodule_inf K) hf hfc hmaps,
        convTraceOn_eq_traceOn K (continuous_of_mem_isotypicCuspSubmodule_inf K) hf' hfc' hmaps',
        traceOn_eq, traceOn_eq]
      set eX : ↥(V ⊓ W) ≃ₗ[ℂ] ↥(V' ⊓ W) :=
        (LinearEquiv.submoduleMap (E K (-(w / 2))) (V ⊓ W)).trans (LinearEquiv.ofEq _ _ hVWmap) with heX
      have hconj : (isStableLinearOn_convOp K (continuous_of_mem_isotypicCuspSubmodule_inf K) hf' hfc' hmaps').toEnd =
          eX.conj (isStableLinearOn_convOp K (continuous_of_mem_isotypicCuspSubmodule_inf K) hf hfc hmaps).toEnd := by
        refine LinearMap.ext fun u' => Subtype.ext ?_
        rw [IsStableLinearOn.coe_toEnd_apply, LinearEquiv.conj_apply]
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, heX, LinearEquiv.trans_apply,
          LinearEquiv.trans_symm, LinearEquiv.coe_ofEq_apply, LinearEquiv.submoduleMap_apply,
          LinearEquiv.ofEq_symm, LinearEquiv.submoduleMap_symm_apply, IsStableLinearOn.coe_toEnd_apply, E_apply]

        have hsymm : ((E K (-(w / 2))).symm (u' : AdelicGL2 (𝓞 K) K → ℂ)) = U K (-(-(w / 2))) u' := rfl
        rw [hsymm, ← hconv, U_neg_U]
      rw [hconj, LinearMap.trace_conj']
    · have hmaps' : ¬ ∀ u' ∈ V' ⊓ W, convOp K f' u' ∈ V' ⊓ W := by
        intro h
        apply hmaps
        intro u hu
        have hu' : U K (-(w / 2)) u ∈ V' ⊓ W := hVWmap ▸ ⟨u, hu, rfl⟩
        have h2 := h _ hu'
        rw [hconv u, ← hVWmap] at h2
        obtain ⟨u₂, hu₂, he⟩ := h2
        have : u₂ = convOp K f u := (E K (-(w / 2))).injective he
        exact this ▸ hu₂
      rw [convTraceOn_eq_zero K (continuous_of_mem_isotypicCuspSubmodule_inf K) hf hfc hmaps,
        convTraceOn_eq_zero K (continuous_of_mem_isotypicCuspSubmodule_inf K) hf' hfc' hmaps']

end S_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab
end P2MW
export P2MW.S_AutomorphicForm_mem_cuspClasses_iff_twist_mem_cuspClasses_and_cutTrace_eq_cutTrace_twist_mul_ideleNorm_det_rpow_of_subset_slab (solution)
