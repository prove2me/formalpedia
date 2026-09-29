-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/891e5275-014c-5537-8ee7-2abed6925e91

import Mathlib
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_normalizedIntertwining_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_of_flat
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
import Theorems.Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace F2BD

open Complex Filter Topology
open scoped ComplexConjugate

theorem conj_ofReal_cpow {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    conj ((r : ℂ) ^ w) = (r : ℂ) ^ conj w := by
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (r : ℂ) (conj w) harg
  rw [conj_conj, Complex.conj_ofReal] at h
  exact h.symm

theorem conj_natCast_cpow (n : ℕ) (w : ℂ) :
    conj ((n : ℂ) ^ w) = (n : ℂ) ^ conj w := by
  have h := conj_ofReal_cpow (Nat.cast_nonneg n) w
  rwa [Complex.ofReal_natCast] at h

theorem conj_Gammaℝ (s : ℂ) : conj (Gammaℝ s) = Gammaℝ (conj s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, conj_ofReal_cpow Real.pi_pos.le]
  congr 2
  · rw [map_div₀, map_neg, map_ofNat]
  · rw [map_div₀, map_ofNat]

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))

theorem conj_Gammaℂ (s : ℂ) : conj (Gammaℂ s) = Gammaℂ (conj s) := by
  have h2π : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, ← Complex.Gamma_conj, map_ofNat, h2π,
    conj_ofReal_cpow (by positivity), map_neg]

theorem norm_axis_eq_sqrt_mul (Nf : ℝ) (hNf : 0 < Nf) (Z G : ℂ → ℂ) (A ε : ℂ)
    (hZ : Differentiable ℂ Z) (hA : A ≠ 0) (hε : ‖ε‖ = 1)
    (hZG : ∀ s : ℂ, 1 < s.re → Z s = A * G s)
    (hFE : ∀ s : ℂ, 1 < s.re →
      Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) * conj (G (conj s))) (t : ℝ) :
    ‖Z (2 * ((t : ℂ) * I))‖ = Real.sqrt Nf * ‖Z (2 * ((t : ℂ) * I) + 1)‖ := by
  set f : ℂ → ℂ := fun s => Z (1 - s) with hf
  set g : ℂ → ℂ := fun s => A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) * (conj (Z (conj s)) / conj A)
    with hg
  have hfd : Differentiable ℂ f := hZ.comp ((differentiable_const _).sub differentiable_id)
  have hconjZ : Differentiable ℂ (fun s => conj (Z (conj s))) := by
    intro s
    have h := (hZ (conj s)).conj_conj
    rw [conj_conj] at h
    exact h
  have hNf0 : (Nf : ℂ) ≠ 0 := ofReal_ne_zero.mpr hNf.ne'
  have hgd : Differentiable ℂ g := by
    refine ((differentiable_const _).mul ?_).mul (hconjZ.div_const _)
    exact (differentiable_id.sub_const _).const_cpow (Or.inl hNf0)
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfg : f = g := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (Complex.analyticOnNhd_univ_iff_differentiable.mpr hfd)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hgd) (z₀ := 2) ?_
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    have hs' : 1 < (conj s).re := by rwa [conj_re]
    have hcA : conj A ≠ 0 := (map_ne_zero _).mpr hA
    simp only [hf, hg]
    rw [hFE s hs, hZG (conj s) hs', map_mul]
    field_simp
  have key := congrFun hfg (1 - 2 * ((t : ℂ) * I))
  simp only [hf, hg] at key
  have h1 : (1 : ℂ) - (1 - 2 * ((t : ℂ) * I)) = 2 * ((t : ℂ) * I) := by ring
  have h2 : conj (1 - 2 * ((t : ℂ) * I)) = 2 * ((t : ℂ) * I) + 1 := by
    simp only [map_sub, map_one, map_mul, map_ofNat, conj_ofReal, conj_I]; ring
  rw [h1, h2] at key
  rw [key, norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_conj, Complex.norm_conj, hε, mul_one,
    norm_cpow_eq_rpow_re_of_pos hNf]
  have hre : ((1 : ℂ) - 2 * ((t : ℂ) * I) - 1 / 2).re = 1 / 2 := by simp; norm_num
  rw [hre, Real.sqrt_eq_rpow]
  field_simp

theorem eventually_ne_zero_axis (g : ℂ → ℂ) (hg : Differentiable ℂ g) (z₁ : ℂ) (hz₁ : g z₁ ≠ 0)
    (t : ℝ) : ∀ᶠ t' : ℝ in 𝓝[≠] t, g ((t' : ℂ) * I) ≠ 0 := by
  have han : AnalyticAt ℂ g ((t : ℂ) * I) := hg.analyticAt _
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    apply hz₁
    have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) isPreconnected_univ (Set.mem_univ _) h
    exact h0 (Set.mem_univ z₁)
  · have hc : Continuous fun t' : ℝ => (t' : ℂ) * I := continuous_ofReal.mul continuous_const
    have htend : Tendsto (fun t' : ℝ => (t' : ℂ) * I) (𝓝[≠] t) (𝓝[≠] ((t : ℂ) * I)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((hc.tendsto t).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t' ht'
      intro h'
      apply ht'
      have h'' := mul_right_cancel₀ I_ne_zero h'
      exact_mod_cast h''
    exact htend.eventually h

theorem norm_sub_one_eq_norm_add_one_of_re_eq_zero {a : ℂ} (ha : a.re = 0) :
    ‖a - 1‖ = ‖a + 1‖ := by
  have h : a - 1 = -conj (a + 1) := by
    apply Complex.ext
    · simp [ha]
    · simp
  rw [h, norm_neg, Complex.norm_conj]

end F2BD

namespace F2BD

open Complex Filter Topology NumberField IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate

open scoped Classical in

theorem conj_archFactor (K : Type) [Field K] [NumberField K]
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (s : ℂ) :
    conj (∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (conj s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (conj s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)))
    = ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs with hv
  · rw [conj_Gammaℝ]
    congr 1
    simp only [map_add, conj_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  · rw [conj_Gammaℂ]
    congr 1
    simp only [map_add, conj_conj, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I,
      map_natCast, map_ofNat]
    ring

open scoped Classical in

theorem conj_eulerProduct (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (w : ℂ) :
    conj (∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-conj w)))⁻¹)
    = ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by
  rw [Function.LeftInverse.map_tprod _ (g := starRingEnd ℂ) Complex.continuous_conj Complex.continuous_conj
    (fun z => conj_conj z)]
  refine tprod_congr fun v => ?_
  rw [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow, map_neg, conj_conj]
  congr 3
  split_ifs with h
  · rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hχu _)]
  · rw [map_zero]

section QuotientChar

variable (K : Type) [Field K] [NumberField K]

theorem coe_mul_inv_apply (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (((μ * ν⁻¹) z : ℂˣ) : ℂ) = ((μ z : ℂˣ) : ℂ) * (((ν z : ℂˣ) : ℂ))⁻¹ := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]

theorem continuous_coe_mul_inv (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
    (hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) :
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((μ * ν⁻¹) z : ℂˣ) : ℂ) := by
  simp only [coe_mul_inv_apply]
  exact hμc.mul (hνc.inv₀ fun z => Units.ne_zero _)

theorem continuous_units_of_continuous_coe (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) :
    Continuous χ := by
  rw [Units.continuous_iff]
  refine ⟨hχc, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hχc.inv₀ fun z => Units.ne_zero _

theorem isUnitaryChar_mul_inv (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsUnitaryChar (𝓞 K) K μ) (hν : AutomorphicForm.IsUnitaryChar (𝓞 K) K ν) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (μ * ν⁻¹) := by
  intro z
  rw [coe_mul_inv_apply, norm_mul, norm_inv, hμ z, hν z, inv_one, mul_one]

theorem isIdeleClassChar_mul_inv (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (hν : AutomorphicForm.IsIdeleClassChar (𝓞 K) K ν) :
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (μ * ν⁻¹) := by
  intro u
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ u, hν u, inv_one, mul_one]

theorem localChar_mul_inv_apply (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    NumberField.TateGlobal.localChar (μ * ν⁻¹) v u =
      NumberField.TateGlobal.localChar μ v u * (NumberField.TateGlobal.localChar ν v u)⁻¹ := rfl

theorem archLocalChar_mul_inv_apply (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) :
    NumberField.TateGlobal.archLocalChar (μ * ν⁻¹) w x =
      NumberField.TateGlobal.archLocalChar μ w x * (NumberField.TateGlobal.archLocalChar ν w x)⁻¹ := rfl

theorem isUnramifiedCharAt_mul_inv (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hμ : NumberField.TateGlobal.IsUnramifiedCharAt μ v) (hν : NumberField.TateGlobal.IsUnramifiedCharAt ν v) :
    NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v := by
  intro t ht ht'
  rw [localChar_mul_inv_apply, hμ t ht ht', hν t ht ht', inv_one, mul_one]

theorem archLocalChar_mul_inv_of_pins (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τμ τν : InfinitePlace K → ℝ)
    (hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τμ v : ℝ) : ℂ) * Complex.I))
    (hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
        (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
          (((τν v : ℝ) : ℂ) * Complex.I))
    (v : InfinitePlace K) (x : (v.Completion)ˣ)
    (h1 : 0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re)
    (h2 : (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0) :
    ((NumberField.TateGlobal.archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
      (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
        ((((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I) := by
  have hN : (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (NumberField.TateGlobal.ideleNorm_pos _).ne'
  rw [archLocalChar_mul_inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hτμ v x h1 h2, hτν v x h1 h2,
    show (((fun v => τμ v - τν v) v : ℝ) : ℂ) * Complex.I
      = ((τμ v : ℝ) : ℂ) * Complex.I - ((τν v : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.cpow_sub _ _ hN, div_eq_mul_inv]

theorem archLocalChar_mul_inv_of_weight_pins (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (mμ mν : InfinitePlace K → ℤ)
    (hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
    (hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
    (v : InfinitePlace K) (x : (v.Completion)ˣ)
    (h1 : ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1) :
    ((NumberField.TateGlobal.archLocalChar (μ * ν⁻¹) v x : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ ((fun v => mμ v - mν v) v) := by
  have hne : InfinitePlace.Completion.extensionEmbedding v (x : v.Completion) ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  rw [archLocalChar_mul_inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hmμ v x h1, hmν v x h1,
    show (fun v => mμ v - mν v) v = mμ v - mν v from rfl, zpow_sub₀ hne, div_eq_mul_inv]

end QuotientChar

end F2BD

namespace F2BD

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

def F1ZPack (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (Nf : ℝ) : Prop :=
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    let P' : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    ∀ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
      (_hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
      (_hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)),
    let γ : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))
    let γ' : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))
    ((∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀) →
      ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
        (∀ s : ℂ, 1 < s.re → Z s = A * (γ s * P s)) ∧
        (∀ s : ℂ, 1 < s.re → Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) * (γ' s * P' s))) ∧
    (∀ τ₀ : ℝ, χ = normPowChar K τ₀ →
      ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
        (∀ s : ℂ, 1 < s.re →
          Z s = A * ((s + ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ s * P s)))) ∧
        (∀ s : ℂ, 1 < s.re →
          Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) *
            ((s - ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ' s * P' s)))))

end F2BD

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g)),
    let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ * ν⁻¹
    let P : ℂ → ℂ := fun w' => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w')))⁻¹
    let γ : ℂ → ℂ := fun w' => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs : ℕ) : ℂ) / 2))
    let c : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹
    let D : ℝ → ℝ := fun y => ∑ v : InfinitePlace K, (|y + τμ v| + |y - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))
    ∀ (δ : ℝ) (R : ℂ → adelicMaximalCompact K → ℂ), 0 < δ →
      (∀ k : adelicMaximalCompact K, AnalyticOnNhd ℂ (fun s => R s k) {s : ℂ | -δ < s.re}) →
      ContinuousOn (fun p : ℂ × adelicMaximalCompact K => R p.1 p.2) ({s : ℂ | -δ < s.re} ×ˢ Set.univ) →
      ((∀ τ₀ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar K τ₀) →
        ∀ (Λ : ℂ → ℂ), Differentiable ℂ Λ → (∀ w' : ℂ, 1 < w'.re → Λ w' = γ w' * P w') →
          ∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
            Λ (2 * s) * R s k = Λ (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K))) →
      (∀ τ₀ : ℝ, χ = NumberField.TateGlobal.normPowChar K τ₀ →
        ∀ (ΛQ : ℂ → ℂ), Differentiable ℂ ΛQ →
          (∀ w' : ℂ, 1 < w'.re → ΛQ w' = (w' + ((τ₀ : ℝ) : ℂ) * Complex.I) * (w' - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ w' * P w')) →
          ∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
            (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * ΛQ (2 * s) * R s k
              = (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * ΛQ (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K))) →
      ∀ t : ℝ, (∫ k, ‖R ((t : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K)) ≤ (C * (1 + D t) ^ A) ^ 2 := by
  intro αm
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K

  obtain ⟨n, ρs, hnρ⟩ :=
    AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
      K SK N hN
  let ρpair : Fin n × Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ :=
    fun p v => ρs p.1 v * (ρs p.2 v)⁻¹
  choose Nf hNfpos hNf using fun p : Fin n × Fin n =>
    NumberField.TateGlobal.exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
      K SK (ρpair p)
  set C : ℝ := 1 + ∑ p : Fin n × Fin n, (Real.sqrt (Nf p))⁻¹ with hC
  have hCsum : ∀ p : Fin n × Fin n, (Real.sqrt (Nf p))⁻¹ ≤ C := fun p => by
    have h := Finset.single_le_sum (f := fun q : Fin n × Fin n => (Real.sqrt (Nf q))⁻¹)
      (fun q _ => by positivity) (Finset.mem_univ p)
    have h1 : (0 : ℝ) ≤ 1 := zero_le_one
    simp only [hC]
    linarith
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ p : Fin n × Fin n, (Real.sqrt (Nf p))⁻¹ := Finset.sum_nonneg fun q _ => by positivity
    simp only [hC]; linarith
  refine ⟨C, 0, hC0, ?_⟩
  intro hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν τμ τν _hτμ _hτν mμ mν _hmμ _hmν ψf _hψf _hψfK _hψff _hψfjc
    _hψfhol _hψfKu _hψfflat _hψflev _hψfty _hψfn Oψ Eψ Nψ _hEψ χ P γ c D δ R hδ hRan hRc hpin hpinQ t
  simp only [pow_zero, mul_one]

  have hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ) :=
    F2BD.continuous_coe_mul_inv K μ ν _hμc _hνc
  have hχu : IsUnitaryChar (𝓞 K) K χ := F2BD.isUnitaryChar_mul_inv K μ ν _hμ _hν
  have hχic : IsIdeleClassChar (𝓞 K) K χ := F2BD.isIdeleClassChar_mul_inv K μ ν _hμic _hνic
  have hχτ := F2BD.archLocalChar_mul_inv_of_pins K μ ν τμ τν _hτμ _hτν
  have hχm := F2BD.archLocalChar_mul_inv_of_weight_pins K μ ν mμ mν _hmμ _hmν

  set I₀ : ℝ := ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) with hI₀
  have hI₀nn : 0 ≤ I₀ := integral_nonneg fun _ => by positivity
  have hI₀le : I₀ ≤ 1 := _hψfn

  obtain ⟨Nf₀, hNf₀, hbd, hFZ⟩ : ∃ Nf₀ : ℝ, 0 < Nf₀ ∧ Nf₀⁻¹ * I₀ ≤ C ^ 2 ∧ F2BD.F1ZPack K χ Nf₀ := by
    by_cases h0 : ψf 0 = 0
    · obtain ⟨S₀, hS₀⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous K χ
        (F2BD.continuous_units_of_continuous_coe K χ hχc)
      obtain ⟨Nf₀, hNf₀, hFZ₀⟩ :=
        NumberField.TateGlobal.exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
          K S₀ (fun v => NumberField.TateGlobal.localChar χ v)
      refine ⟨Nf₀, hNf₀, ?_, hFZ₀ χ hχc hχu hχic hS₀ (fun v _ u _ _ => rfl)⟩
      have hI00 : I₀ = 0 := by simp [hI₀, h0]
      rw [hI00, mul_zero]; positivity
    · obtain ⟨hunr2, r, r', hrr'⟩ := hnρ hαm μ ν 0 (ψf 0) (_hψf 0) h0 (_hψflev 0)
      have hunr : ∀ v, v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt χ v := fun v hv =>
        F2BD.isUnramifiedCharAt_mul_inv K μ ν v (hunr2 v hv).1 (hunr2 v hv).2
      have hram : ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ,
          (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar χ v u = ρpair (r, r') v u := by
        intro v hv u hu hu'
        rw [F2BD.localChar_mul_inv_apply, (hrr' v hv u hu hu').1, (hrr' v hv u hu hu').2]
        rfl
      refine ⟨Nf (r, r'), hNfpos _, ?_, hNf (r, r') χ hχc hχu hχic hunr hram⟩
      have hle : (Real.sqrt (Nf (r, r')))⁻¹ ≤ C := hCsum (r, r')
      have hnn : 0 ≤ (Real.sqrt (Nf (r, r')))⁻¹ := by positivity
      calc (Nf (r, r'))⁻¹ * I₀ ≤ (Nf (r, r'))⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hI₀le (inv_pos.mpr (hNfpos _)).le
        _ = ((Real.sqrt (Nf (r, r')))⁻¹) ^ 2 := by
            rw [mul_one, inv_pow, Real.sq_sqrt (hNfpos _).le]
        _ ≤ C ^ 2 := by
            gcongr

  obtain ⟨δ₀, R₀, hδ₀, hR₀an, hR₀c, hgen, hnp⟩ :=
    AutomorphicForm.exists_analyticOnNhd_normalizedIntertwining_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_of_flat
      K SK ξK hξc hξt N hN tysK w hξw hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν τμ τν _hτμ _hτν mμ mν
      _hmμ _hmν ψf _hψf _hψfK _hψff _hψfjc _hψfhol _hψfKu _hψfflat _hψflev _hψfty _hψfn Oψ Eψ Nψ _hEψ

  have hIax : ∀ t' : ℝ,
      ∫ k, ‖c * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) = I₀ := by
    intro t'
    have hU :=
      AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
        K hαm μ ν _hμ _hν _hμic _hνic _hμc _hνc ψf _hψf _hψfK _hψff _hψfjc _hψfhol _hψfKu
        ψf _hψf _hψfK _hψff _hψfjc _hψfhol _hψfKu Oψ Eψ Nψ _hEψ Oψ Eψ Nψ _hEψ t'
    have hU2 : ∫ k, (c * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
          conj (c * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
        = ∫ k, ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := hU
    simp only [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal] at hU2
    have hU3 := Complex.ofReal_injective hU2
    rw [hU3, hI₀]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_hψfflat]

  have hcont : Continuous fun t' : ℝ => ∫ k, ‖R ((t' : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K) := by
    haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
    have h1 : Continuous fun p : ℝ × adelicMaximalCompact K => (((p.1 : ℂ) * Complex.I), p.2) := by
      fun_prop
    have h3 : Continuous fun p : ℝ × adelicMaximalCompact K => R ((p.1 : ℂ) * Complex.I) p.2 :=
      hRc.comp_continuous h1 (fun p => ⟨by simp [hδ], Set.mem_univ _⟩)
    have hf : Continuous (Function.uncurry
        fun (t' : ℝ) (k : adelicMaximalCompact K) => ‖R ((t' : ℂ) * Complex.I) k‖ ^ 2) :=
      h3.norm.pow 2
    have h4 := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K) hf isCompact_univ
    simpa only [Measure.restrict_univ] using h4

  have hγ2 : γ 2 ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun v _ => ?_
    split_ifs with hv
    · refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, Complex.natCast_re, mul_zero, zero_mul, sub_zero]
      norm_num
      positivity
    · refine F2BD.Gammaℂ_ne_zero_of_re_pos ?_
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.div_ofNat_re, Complex.natCast_re]
      norm_num
      positivity
  have hP2 : P 2 ≠ 0 := by
    have hz : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))},
        ‖(if NumberField.TateGlobal.IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ)
          else 0)‖ ≤ 1 := by
      intro v
      split_ifs
      · exact (hχu _).le
      · simp
    have h := (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K ∅ _ hz).2.2
      2 (by norm_num)
    intro h0
    apply h
    exact (Equiv.tprod_eq
      (Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v) :
        {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))} ≃ HeightOneSpectrum (𝓞 K))
      fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 : ℂ))))⁻¹).trans h0
  have hax : ∀ t' : ℝ, ((t' : ℂ) * Complex.I) ∈ Oψ := fun t' => _hEψ.2.2.1 (by simp)

  have hγc : ∀ s : ℂ, conj (γ (conj s)) = ∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (s - ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s - ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs : ℕ) : ℂ) / 2)) :=
    fun s => F2BD.conj_archFactor K (fun v => τμ v - τν v) (fun v => mμ v - mν v) s
  have hPc : ∀ s : ℂ, conj (P (conj s)) = ∏' v : HeightOneSpectrum (𝓞 K),
      (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ :=
    fun s => F2BD.conj_eulerProduct K χ hχu s

  have core : ∀ (L a b : ℂ → ℂ), Differentiable ℂ L → Continuous a →
      (∀ t' : ℝ, ‖a ((t' : ℂ) * Complex.I)‖ = ‖b ((t' : ℂ) * Complex.I)‖) →
      (∀ t' : ℝ, a ((t' : ℂ) * Complex.I) ≠ 0) →
      a 1 * L 2 ≠ 0 →
      (∀ t' : ℝ, ‖L (2 * ((t' : ℂ) * Complex.I))‖ = Real.sqrt Nf₀ * ‖L (2 * ((t' : ℂ) * Complex.I) + 1)‖) →
      (∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
        a s * L (2 * s) * R s k =
          b s * L (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s)
            (k : AdelicGL2 (𝓞 K) K))) →
      (∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
        a s * L (2 * s) * R₀ s k =
          b s * L (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s)
            (k : AdelicGL2 (𝓞 K) K))) →
      (∀ s ∈ Oψ, -δ₀ < s.re → ∀ k : adelicMaximalCompact K,
        b s * L (2 * s + 1) * (c * Nψ s (k : AdelicGL2 (𝓞 K) K)) = a s * L (2 * s) * R₀ s k) →
      ∀ t' : ℝ, L (2 * ((t' : ℂ) * Complex.I)) ≠ 0 →
        ∫ k, ‖R ((t' : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K) = Nf₀⁻¹ * I₀ := by
    intro L a b hL ha hab ha0 haL2 hmod hpinR hpinR₀ haxis t' hLt

    have hRR₀ : ∀ k : adelicMaximalCompact K, ∀ s : ℂ, -min δ δ₀ < s.re → R s k = R₀ s k := by
      intro k
      have hpre : IsPreconnected {s : ℂ | -min δ δ₀ < s.re} := (convex_halfSpace_re_gt _).isPreconnected
      have hRk : AnalyticOnNhd ℂ (fun s => R s k) {s : ℂ | -min δ δ₀ < s.re} := fun s hs =>
        hRan k s (show -δ < s.re by
          have h1 : -min δ δ₀ < s.re := hs
          have h2 := min_le_left δ δ₀
          linarith)
      have hR₀k : AnalyticOnNhd ℂ (fun s => R₀ s k) {s : ℂ | -min δ δ₀ < s.re} := fun s hs =>
        hR₀an k s (show -δ₀ < s.re by
          have h1 : -min δ δ₀ < s.re := hs
          have h2 := min_le_right δ δ₀
          linarith)
      have h1mem : (1 : ℂ) ∈ {s : ℂ | -min δ δ₀ < s.re} := by
        show -min δ δ₀ < (1 : ℂ).re
        simp only [Complex.one_re]
        have := lt_min hδ hδ₀; linarith

      have hUopen : IsOpen {s : ℂ | 1 / 2 < s.re ∧ a s * L (2 * s) ≠ 0} := by
        refine (isOpen_lt continuous_const Complex.continuous_re).inter ?_
        exact isOpen_ne_fun (ha.mul (hL.continuous.comp (continuous_const.mul continuous_id))) continuous_const
      have h1U : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re ∧ a s * L (2 * s) ≠ 0} := by
        refine ⟨by simp only [Complex.one_re]; norm_num, ?_⟩
        simpa using haL2
      have hev : (fun s => R s k) =ᶠ[nhds (1 : ℂ)] fun s => R₀ s k := by
        filter_upwards [hUopen.mem_nhds h1U] with s hs
        have e1 := hpinR s hs.1 k
        have e2 := hpinR₀ s hs.1 k
        rw [← e2] at e1
        exact mul_left_cancel₀ hs.2 e1
      intro s hs
      exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hRk hR₀k hpre h1mem hev hs

    set s₀ : ℂ := (t' : ℂ) * Complex.I with hs₀
    have hs₀re : s₀.re = 0 := by simp [hs₀]
    have hs₀O : s₀ ∈ Oψ := hax t'
    have hs₀δ : -δ₀ < s₀.re := by rw [hs₀re]; linarith
    have hs₀m : -min δ δ₀ < s₀.re := by rw [hs₀re]; have := lt_min hδ hδ₀; linarith
    have hpt : ∀ k : adelicMaximalCompact K,
        R s₀ k = (b s₀ * L (2 * s₀ + 1)) / (a s₀ * L (2 * s₀)) * (c * Nψ s₀ (k : AdelicGL2 (𝓞 K) K)) := by
      intro k
      have h := haxis s₀ hs₀O hs₀δ k
      rw [← hRR₀ k s₀ hs₀m] at h
      have hne : a s₀ * L (2 * s₀) ≠ 0 := mul_ne_zero (ha0 t') hLt
      rw [div_mul_eq_mul_div, eq_div_iff hne]
      linear_combination -h

    have hLt1 : L (2 * s₀ + 1) ≠ 0 := by
      intro h0
      have h := hmod t'
      rw [h0, norm_zero, mul_zero, norm_eq_zero] at h
      exact hLt h
    have hab' : ‖a s₀‖ = ‖b s₀‖ := hab t'
    have hmod' : ‖L (2 * s₀)‖ = Real.sqrt Nf₀ * ‖L (2 * s₀ + 1)‖ := hmod t'
    have hratio : ‖(b s₀ * L (2 * s₀ + 1)) / (a s₀ * L (2 * s₀))‖ = (Real.sqrt Nf₀)⁻¹ := by
      rw [norm_div, norm_mul, norm_mul, ← hab', hmod']
      have h1 : ‖a s₀‖ ≠ 0 := norm_ne_zero_iff.mpr (ha0 t')
      have h2 : ‖L (2 * s₀ + 1)‖ ≠ 0 := norm_ne_zero_iff.mpr hLt1
      have h3 : Real.sqrt Nf₀ ≠ 0 := (Real.sqrt_pos.mpr hNf₀).ne'
      field_simp

    have hptn : ∀ k : adelicMaximalCompact K,
        ‖R s₀ k‖ ^ 2 = Nf₀⁻¹ * ‖c * Nψ s₀ (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 := by
      intro k
      rw [hpt k, norm_mul, hratio, mul_pow, inv_pow, Real.sq_sqrt hNf₀.le]
    calc ∫ k, ‖R s₀ k‖ ^ 2 ∂(maximalCompactHaar K)
        = ∫ k, Nf₀⁻¹ * ‖c * Nψ s₀ (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) :=
          integral_congr_ae (Filter.Eventually.of_forall hptn)
      _ = Nf₀⁻¹ * ∫ k, ‖c * Nψ s₀ (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) := integral_const_mul _ _
      _ = Nf₀⁻¹ * I₀ := by rw [hs₀, hIax t']

  have conclude : ∀ (L : ℂ → ℂ), Differentiable ℂ L → L 2 ≠ 0 →
      (∀ t' : ℝ, L (2 * ((t' : ℂ) * Complex.I)) ≠ 0 →
        ∫ k, ‖R ((t' : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K) = Nf₀⁻¹ * I₀) →
      ∫ k, ‖R ((t : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K) ≤ C ^ 2 := by
    intro L hL hL2 hgood
    have hev := F2BD.eventually_ne_zero_axis (fun s => L (2 * s)) (hL.comp (differentiable_id.const_mul _))
      1 (by simpa using hL2) t
    have hev' : ∀ᶠ t' : ℝ in nhdsWithin t {t}ᶜ,
        ∫ k, ‖R ((t' : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K) ≤ C ^ 2 := by
      filter_upwards [hev] with t' ht'
      rw [hgood t' ht']
      exact hbd
    exact le_of_tendsto ((hcont.tendsto t).mono_left nhdsWithin_le_nhds) hev'

  by_cases hnpc : ∃ τ₀ : ℝ, χ = NumberField.TateGlobal.normPowChar K τ₀
  ·
    obtain ⟨τ₀, hτ₀⟩ := hnpc
    obtain ⟨Z, A, ε, hZd, hA, hε, hZ1, hZ2⟩ :=
      (hFZ (fun v => τμ v - τν v) (fun v => mμ v - mν v) hχτ hχm).2 τ₀ hτ₀
    beta_reduce at hZ1 hZ2

    set ΛQ : ℂ → ℂ := fun w' => Z w' / A with hΛQ
    have hΛQd : Differentiable ℂ ΛQ := hZd.div_const A
    have hΛQ1 : ∀ w' : ℂ, 1 < w'.re →
        ΛQ w' = (w' + ((τ₀ : ℝ) : ℂ) * Complex.I) * (w' - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ w' * P w') := by
      intro w' hw'
      simp only [hΛQ]
      rw [hZ1 w' hw', mul_div_cancel_left₀ _ hA, mul_assoc]
    have hmod : ∀ t' : ℝ, ‖ΛQ (2 * ((t' : ℂ) * Complex.I))‖ =
        Real.sqrt Nf₀ * ‖ΛQ (2 * ((t' : ℂ) * Complex.I) + 1)‖ := by
      intro t'
      have h := F2BD.norm_axis_eq_sqrt_mul Nf₀ hNf₀ Z
        (fun s => (s + ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ s * P s)))
        A ε hZd hA hε hZ1 ?_ t'
      · simp only [hΛQ, norm_div]
        rw [h]; ring
      · intro s hs
        rw [hZ2 s hs]
        simp only [map_mul, hγc, hPc, map_add, map_sub, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I,
          map_one]
        ring
    obtain ⟨haxis, hpinR₀⟩ := hnp τ₀ hτ₀ ΛQ hΛQd hΛQ1
    have hpinR := hpinQ τ₀ hτ₀ ΛQ hΛQd hΛQ1
    have hΛQ2 : ΛQ 2 ≠ 0 := by
      rw [hΛQ1 2 (by norm_num)]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero hγ2 hP2)
      · intro h; have := congrArg Complex.re h; simp at this
      · intro h; have := congrArg Complex.re h; norm_num at this
    refine conclude ΛQ hΛQd hΛQ2 ?_
    refine core ΛQ (fun s => 2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) (fun s => 2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1)
      hΛQd (by fun_prop) ?_ ?_ ?_ hmod hpinR hpinR₀ haxis
    · intro t'
      exact (F2BD.norm_sub_one_eq_norm_add_one_of_re_eq_zero (by simp)).symm
    · intro t' h
      have := congrArg Complex.re h
      simp at this
    · refine mul_ne_zero ?_ hΛQ2
      intro h; have := congrArg Complex.re h; norm_num at this
  ·
    push Not at hnpc
    obtain ⟨Z, A, ε, hZd, hA, hε, hZ1, hZ2⟩ :=
      (hFZ (fun v => τμ v - τν v) (fun v => mμ v - mν v) hχτ hχm).1 hnpc
    beta_reduce at hZ1 hZ2
    set Λ₀ : ℂ → ℂ := fun w' => Z w' / A with hΛ₀
    have hΛ₀d : Differentiable ℂ Λ₀ := hZd.div_const A
    have hΛ₀1 : ∀ w' : ℂ, 1 < w'.re → Λ₀ w' = γ w' * P w' := by
      intro w' hw'
      simp only [hΛ₀]
      rw [hZ1 w' hw', mul_div_cancel_left₀ _ hA]
    have hmod : ∀ t' : ℝ, ‖Λ₀ (2 * ((t' : ℂ) * Complex.I))‖ =
        Real.sqrt Nf₀ * ‖Λ₀ (2 * ((t' : ℂ) * Complex.I) + 1)‖ := by
      intro t'
      have h := F2BD.norm_axis_eq_sqrt_mul Nf₀ hNf₀ Z (fun s => γ s * P s) A ε hZd hA hε hZ1 ?_ t'
      · simp only [hΛ₀, norm_div]
        rw [h]; ring
      · intro s hs
        rw [hZ2 s hs]
        simp only [map_mul, hγc, hPc]
    obtain ⟨haxis, hpinR₀⟩ := hgen hnpc Λ₀ hΛ₀d hΛ₀1
    have hpinR := hpin hnpc Λ₀ hΛ₀d hΛ₀1
    have hΛ₀2 : Λ₀ 2 ≠ 0 := by
      rw [hΛ₀1 2 (by norm_num)]
      exact mul_ne_zero hγ2 hP2
    refine conclude Λ₀ hΛ₀d hΛ₀2 ?_
    refine core Λ₀ (fun _ => 1) (fun _ => 1) hΛ₀d continuous_const (fun _ => rfl) (fun _ => one_ne_zero)
      (by rwa [one_mul]) hmod ?_ ?_ ?_
    · intro s hs k; rw [one_mul, one_mul]; exact hpinR s hs k
    · intro s hs k; rw [one_mul, one_mul]; exact hpinR₀ s hs k
    · intro s hs hs' k; rw [one_mul, one_mul]; exact haxis s hs hs' k

end S_AutomorphicForm_exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat (solution)
