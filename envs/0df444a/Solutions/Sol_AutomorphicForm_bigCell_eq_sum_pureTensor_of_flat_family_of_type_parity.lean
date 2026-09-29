-- Prove2me | solution 1 for AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1e45559f-36de-5a8b-9da4-867a37a9f38e

import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option Elab.async false
set_option autoImplicit false

noncomputable section

section Height

set_option autoImplicit false

noncomputable section

open NumberField.AdelicHeight

namespace BigCellExpansion
namespace Height

section Local

variable {K : Type*} [NormedField K]

private theorem _root_.BigCellExpansion.Height.coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

p2m_export "BigCellExpansion.Height" "coe_mul"
variable [IsUltrametricDist K]

private theorem rowMaxNorm_mul_le (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hentry : ∀ j : Fin 2,
      ‖((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j‖
        ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

private theorem rowMaxNorm_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  refine le_antisymm (rowMaxNorm_mul_le g k hk) ?_
  have h := rowMaxNorm_mul_le (g * k) k⁻¹ hk'
  rwa [mul_inv_cancel_right] at h

private theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

private theorem finLocalHeight_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_mul_integral g k hk hk', coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k hk hk', mul_one]

end Local

end BigCellExpansion.Height

end

end Height

section Transport

set_option autoImplicit false

noncomputable section

p2m_open "Matrix NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open AutomorphicForm AutomorphicForm.WindowedSiegel

open scoped ComplexConjugate

namespace BigCellExpansion
namespace Transport

section RCLike

variable {L : Type} [RCLike L]

end RCLike

section Transport

variable {K L : Type} [NormedField K] [NormedField L]

private theorem IsRowIsometry.map_ringEquiv (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : IsRowIsometry (glEquivOfRingEquiv e k) := by
  obtain ⟨hd, hiso⟩ := hk
  refine ⟨?_, fun x y => ?_⟩
  · change ‖(RingEquiv.mapMatrix (m := Fin 2) e (k : Matrix (Fin 2) (Fin 2) K)).det‖ = 1
    rw [← RingEquiv.map_det, he, hd]
  · have hes : ∀ z : L, ‖e.symm z‖ = ‖z‖ := fun z => by rw [← he (e.symm z), e.apply_symm_apply]
    have hent : ∀ i j, ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
    simp only [hent]
    calc ‖x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 0) + y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
          + ‖x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 1) + y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2
        = ‖e (e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
          + ‖e (e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2 := by
          simp only [map_add, map_mul, e.apply_symm_apply]
      _ = ‖e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
          + ‖e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 := by
          rw [he, he]
      _ = ‖e.symm x‖ ^ 2 + ‖e.symm y‖ ^ 2 := hiso (e.symm x) (e.symm y)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [hes, hes]

end Transport

section Places

variable {F : Type} [Field F]

private theorem norm_ringEquivComplexOfIsComplex {w : InfinitePlace F} (hw : w.IsComplex) (x : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

end Places

end BigCellExpansion.Transport

end

end Transport

noncomputable section

namespace BigCellExpansion
namespace RealPlaces

open MeasureTheory AddCircle Submodule

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in

private theorem fourier_arg_add (n : ℤ) (u v : AddCircle T) :
    fourier n (u + v) = fourier n u * fourier n v := by
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

omit hT in

private theorem fourier_neg_neg (n : ℤ) (v : AddCircle T) :
    fourier (-n) (-v) = fourier n v := by
  have hsm : (-n : ℤ) • (-v) = n • v := by rw [neg_zsmul, zsmul_neg, neg_neg]
  rw [fourier_apply, hsm, ← fourier_apply]

omit hT in

private theorem continuous_of_mem_span {s : Set (AddCircle T → ℂ)}
    (hs : ∀ f ∈ s, Continuous f) {v : AddCircle T → ℂ}
    (hv : v ∈ span ℂ s) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => exact continuous_const
  | add f g _ _ ihf ihg => exact ihf.add ihg
  | smul c f _ ih => exact ih.const_smul c

private theorem integrable_of_continuous {v : AddCircle T → ℂ} (hv : Continuous v) :
    Integrable v (@haarAddCircle T hT) :=
  hv.integrable_of_hasCompactSupport (isClosed_tsupport v).isCompact

section Core

variable (h : C(AddCircle T, ℂ))

private theorem fourierCoeff_translate (c : AddCircle T) (n : ℤ) :
    fourierCoeff (fun θ => h (θ + c)) n = fourier n c * fourierCoeff (⇑h) n := by
  have h1 : (fun u : AddCircle T => fourier (-n) u • h (u + c))
      = fun u : AddCircle T =>
        (fun z : AddCircle T => fourier (-n) (z + -c) • h z) (c + u) := by
    funext u
    show fourier (-n) u • h (u + c) = fourier (-n) (c + u + -c) • h (c + u)
    rw [add_comm c u, add_neg_cancel_right]
  have h2 : ∀ z : AddCircle T, fourier (-n) (z + -c) • h z
      = fourier n c • (fourier (-n) z • h z) := by
    intro z
    rw [fourier_arg_add, fourier_neg_neg, mul_comm, ← smul_smul]
  calc fourierCoeff (fun θ => h (θ + c)) n
      = ∫ u, fourier (-n) u • h (u + c) ∂haarAddCircle := rfl
    _ = ∫ u, (fun z : AddCircle T => fourier (-n) (z + -c) • h z) (c + u) ∂haarAddCircle := by
        rw [h1]
    _ = ∫ z, fourier (-n) (z + -c) • h z ∂haarAddCircle :=
        integral_add_left_eq_self (μ := haarAddCircle)
          (fun z : AddCircle T => fourier (-n) (z + -c) • h z) c
    _ = ∫ z, fourier n c • (fourier (-n) z • h z) ∂haarAddCircle := by
        simp_rw [h2]
    _ = fourier n c • ∫ z, fourier (-n) z • h z ∂haarAddCircle := integral_smul _ _
    _ = fourier n c • fourierCoeff (⇑h) n := rfl
    _ = fourier n c * fourierCoeff (⇑h) n := by rw [smul_eq_mul]

private theorem support_fourierCoeff_finite (s : Finset (AddCircle T → ℂ))
    (hsp : ∀ c : AddCircle T, (fun θ => h (θ + c)) ∈ span ℂ (s : Set (AddCircle T → ℂ))) :
    (Function.support fun n : ℤ => fourierCoeff (⇑h) n).Finite := by
  classical
  by_contra hinfin
  have hinf : (Function.support fun n : ℤ => fourierCoeff (⇑h) n).Infinite := hinfin

  have hWle : span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))
      ≤ span ℂ (s : Set (AddCircle T → ℂ)) := by
    rw [span_le]
    rintro _ ⟨c, rfl⟩
    exact hsp c
  haveI hfd : FiniteDimensional ℂ
      (span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))) :=
    Submodule.finiteDimensional_of_le hWle
  have hWcont : ∀ v ∈ span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c)),
      Continuous v := by
    intro v hv
    refine continuous_of_mem_span ?_ hv
    rintro f ⟨c, rfl⟩
    exact (map_continuous h).comp (continuous_add_const c)
  obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq
    (Module.finrank ℂ
      (span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))) + 1)

  let Φ : (span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c))) →ₗ[ℂ]
      (↥t → ℂ) :=
    { toFun := fun v j => fourierCoeff (v : AddCircle T → ℂ) (j : ℤ)
      map_add' := by
        intro v w
        funext j
        show fourierCoeff ((v : AddCircle T → ℂ) + (w : AddCircle T → ℂ)) (j : ℤ) = _
        rw [fourierCoeff.add (integrable_of_continuous (hWcont v v.2))
          (integrable_of_continuous (hWcont w w.2))]
        rfl
      map_smul' := by
        intro cc v
        funext j
        show fourierCoeff (cc • (v : AddCircle T → ℂ)) (j : ℤ) = _
        rw [fourierCoeff.const_smul (v : AddCircle T → ℂ) cc (j : ℤ)]
        rfl }
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨g, hg0, hker⟩ :=
      (LinearMap.range Φ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)

    have hzero : ∀ c : AddCircle T,
        (∑ j : ↥t, (fourier (j : ℤ) c * fourierCoeff (⇑h) (j : ℤ))
          • g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) = 0 := by
      intro c
      have hmem : (fun θ => h (θ + c))
          ∈ span ℂ (Set.range fun c : AddCircle T => fun θ => h (θ + c)) :=
        subset_span ⟨c, rfl⟩
      have hval : Φ ⟨_, hmem⟩
          = fun j : ↥t => fourier (j : ℤ) c * fourierCoeff (⇑h) (j : ℤ) := by
        funext j
        exact fourierCoeff_translate h c (j : ℤ)
      have hgv : g (Φ ⟨_, hmem⟩) = 0 := LinearMap.mem_ker.mp (hker ⟨_, rfl⟩)
      rw [hval, LinearMap.pi_apply_eq_sum_univ] at hgv
      exact hgv

    have hfun0 : (fun c : AddCircle T =>
        ∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) c)
        = fun _ : AddCircle T => (0 : ℂ) := by
      funext c
      show (∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
          * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) c) = 0
      have hre : (∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
          * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) c)
          = ∑ j : ↥t, (fourier (j : ℤ) c * fourierCoeff (⇑h) (j : ℤ))
              • g fun j' : ↥t => if j = j' then (1 : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_mul]
        ring
      rw [hre]
      exact hzero c

    have hcoeffZero : ∀ i : ↥t,
        fourierCoeff (⇑h) (i : ℤ)
          * g (fun j' : ↥t => if i = j' then (1 : ℂ) else 0) = 0 := by
      intro i
      have hint : ∀ j : ↥t, Integrable (fun cc : AddCircle T =>
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc)
          (@haarAddCircle T hT) := fun j =>
        integrable_of_continuous (continuous_const.mul (map_continuous (fourier (j : ℤ))))
      have hfn : (fun cc : AddCircle T => ∑ j : ↥t,
            (fourierCoeff (⇑h) (j : ℤ)
              * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc)
          = ∑ j : ↥t, fun cc : AddCircle T =>
              (fourierCoeff (⇑h) (j : ℤ)
                * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc := by
        funext cc
        rw [Finset.sum_apply]
      have hzfn : (fun _ : AddCircle T => (0 : ℂ))
          = ∑ j : ↥t, fun cc : AddCircle T =>
              (fourierCoeff (⇑h) (j : ℤ)
                * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc :=
        hfun0.symm.trans hfn
      have hsum := fourierCoeff.sum (Finset.univ : Finset ↥t)
        (fun j : ↥t => fun cc : AddCircle T =>
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0) * fourier (j : ℤ) cc)
        (fun j _ => hint j)
      have hz : fourierCoeff (fun _ : AddCircle T => (0 : ℂ)) (i : ℤ) = 0 := by
        simp [fourierCoeff]
      have hstep : (0 : ℂ) = ∑ j : ↥t,
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
            * fourierCoeff (T := T) (⇑(fourier (T := T) (j : ℤ))) (i : ℤ) := by
        calc (0 : ℂ)
            = fourierCoeff (fun _ : AddCircle T => (0 : ℂ)) (i : ℤ) := hz.symm
          _ = fourierCoeff (∑ j : ↥t, fun cc : AddCircle T =>
                (fourierCoeff (⇑h) (j : ℤ)
                  * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                  * fourier (j : ℤ) cc) (i : ℤ) := by rw [← hzfn]
          _ = (∑ j : ↥t, fourierCoeff fun cc : AddCircle T =>
                (fourierCoeff (⇑h) (j : ℤ)
                  * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                  * fourier (j : ℤ) cc) (i : ℤ) := by rw [hsum]
          _ = ∑ j : ↥t, fourierCoeff (fun cc : AddCircle T =>
                (fourierCoeff (⇑h) (j : ℤ)
                  * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                  * fourier (j : ℤ) cc) (i : ℤ) := by rw [Finset.sum_apply]
          _ = ∑ j : ↥t, (fourierCoeff (⇑h) (j : ℤ)
                * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
                * fourierCoeff (T := T) (⇑(fourier (T := T) (j : ℤ))) (i : ℤ) :=
              Finset.sum_congr rfl fun j _ => fourierCoeff.const_mul _ _ _
      have hcollapse : (∑ j : ↥t,
          (fourierCoeff (⇑h) (j : ℤ)
            * g fun j' : ↥t => if j = j' then (1 : ℂ) else 0)
            * fourierCoeff (T := T) (⇑(fourier (T := T) (j : ℤ))) (i : ℤ))
          = fourierCoeff (⇑h) (i : ℤ)
            * g fun j' : ↥t => if i = j' then (1 : ℂ) else 0 := by
        rw [Finset.sum_eq_single i]
        · rw [congrFun (fourierCoeff_fourier (T := T) (i : ℤ)) (i : ℤ),
            Pi.single_eq_same, mul_one]
        · intro b _ hbi
          have hbne : (i : ℤ) ≠ (b : ℤ) := fun hc => hbi (Subtype.coe_injective hc.symm)
          rw [congrFun (fourierCoeff_fourier (T := T) (b : ℤ)) (i : ℤ),
            Pi.single_eq_of_ne hbne, mul_zero]
        · intro hni
          exact absurd (Finset.mem_univ i) hni
      exact (hstep.trans hcollapse).symm

    have hgeq : g = 0 := by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ g x, LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have haj : g (fun j' : ↥t => if j = j' then (1 : ℂ) else 0) = 0 := by
        have hj := hcoeffZero j
        have hne : fourierCoeff (⇑h) (j : ℤ) ≠ 0 := Function.mem_support.mp (hts j.2)
        exact (mul_eq_zero.mp hj).resolve_left hne
      rw [haj, smul_zero]
    exact hg0 hgeq
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_pi, Fintype.card_coe, htcard] at hle
  omega

private theorem eq_finite_sum_fourier (s : Finset (AddCircle T → ℂ))
    (hsp : ∀ c : AddCircle T, (fun θ => h (θ + c)) ∈ span ℂ (s : Set (AddCircle T → ℂ))) :
    ∃ tfin : Finset ℤ, ∀ θ : AddCircle T,
      h θ = ∑ n ∈ tfin, fourierCoeff (⇑h) n * fourier n θ := by
  classical
  have hfin := support_fourierCoeff_finite h s hsp
  refine ⟨hfin.toFinset, fun θ => ?_⟩
  have hvanish : ∀ n : ℤ, n ∉ hfin.toFinset → fourierCoeff (⇑h) n = 0 := by
    intro n hn
    by_contra hne
    exact hn (hfin.mem_toFinset.mpr (Function.mem_support.mpr hne))
  have hsummable : Summable (fourierCoeff (⇑h)) :=
    summable_of_ne_finset_zero hvanish
  have h1 := has_pointwise_sum_fourier_series_of_summable (f := h) hsummable θ
  have h2 : HasSum (fun n : ℤ => fourierCoeff (⇑h) n • fourier n θ)
      (∑ n ∈ hfin.toFinset, fourierCoeff (⇑h) n • fourier n θ) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [hvanish n hn, zero_smul]
  have heq := h1.unique h2
  simpa [smul_eq_mul] using heq

end Core

open Matrix AutomorphicForm AutomorphicForm.WindowedSiegel

private theorem rotGL_det_val (θ : ℝ) :
    (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]).det = 1 := by
  rw [Matrix.det_fin_two_of]
  linear_combination Real.sin_sq_add_cos_sq θ

private def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
    (by rw [rotGL_det_val]; exact one_ne_zero)

private theorem rotGL_coe (θ : ℝ) : (rotGL θ : Matrix (Fin 2) (Fin 2) ℝ)
    = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  rw [rotGL, GeneralLinearGroup.val_mkOfDetNeZero]

private theorem rotGL_add (θ₁ θ₂ : ℝ) : rotGL (θ₁ + θ₂) = rotGL θ₁ * rotGL θ₂ := by
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [rotGL_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.mk_one, Real.cos_add, Real.sin_add] <;>
    ring

private theorem rotGL_zero : rotGL 0 = 1 := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rotGL_coe, Real.cos_zero, Real.sin_zero, Units.val_one]

private theorem rotGL_periodic : Function.Periodic rotGL (2 * Real.pi) := by
  intro θ
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rotGL_coe, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem rotGL_neg (θ : ℝ) : rotGL (-θ) = (rotGL θ)⁻¹ := by
  have h : rotGL θ * rotGL (-θ) = 1 := by
    rw [← rotGL_add, add_neg_cancel, rotGL_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

private theorem isRowIsometry_rotGL (θ : ℝ) : IsRowIsometry (rotGL θ) := by
  constructor
  · rw [rotGL_coe, rotGL_det_val, norm_one]
  · intro x y
    simp only [rotGL_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.sin_sq_add_cos_sq θ

private theorem continuous_rotGL_val :
    Continuous fun θ : ℝ => (rotGL θ : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp only [rotGL_coe]
  refine continuous_matrix ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
  · exact Real.continuous_cos
  · exact Real.continuous_sin.neg
  · exact Real.continuous_sin
  · exact Real.continuous_cos

private theorem continuous_rotGL : Continuous rotGL := by
  rw [Units.continuous_iff]
  refine ⟨continuous_rotGL_val, ?_⟩
  have hinv : (fun θ : ℝ => (((rotGL θ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
      = fun θ : ℝ => ((rotGL (-θ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext θ
    rw [rotGL_neg]
  rw [hinv]
  exact continuous_rotGL_val.comp continuous_neg

section Transport

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.Transport"

private theorem continuous_glEquivOfRingEquiv {K L : Type} [NormedField K] [NormedField L]
    (e : K ≃+* L) (he : Continuous e) :
    Continuous (glEquivOfRingEquiv e) := by
  have hval : Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) :=
    Units.continuous_val
  have hcoeinv : Continuous fun k : GL (Fin 2) K =>
      ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Units.continuous_coe_inv
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) i :=
      (continuous_apply i).comp hval
    have h2 : Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) i j :=
      (continuous_apply j).comp h1
    exact he.comp h2
  · have h : (fun k : GL (Fin 2) K =>
        (((glEquivOfRingEquiv e k)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
        = fun k : GL (Fin 2) K =>
          ((glEquivOfRingEquiv e (k⁻¹) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      funext k
      rw [← map_inv]
    rw [h]
    refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun k : GL (Fin 2) K =>
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i :=
      (continuous_apply i).comp hcoeinv
    have h2 : Continuous fun k : GL (Fin 2) K =>
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j :=
      (continuous_apply j).comp h1
    exact he.comp h2

variable {F : Type} [Field F]

private def rotAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) : GL (Fin 2) w.Completion :=
  glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (rotGL θ)

private theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal) (θ₁ θ₂ : ℝ) :
    rotAt hw (θ₁ + θ₂) = rotAt hw θ₁ * rotAt hw θ₂ := by
  rw [rotAt, rotAt, rotAt, rotGL_add, map_mul]

private theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal) : rotAt hw 0 = 1 := by
  rw [rotAt, rotGL_zero, map_one]

private theorem rotAt_periodic {w : InfinitePlace F} (hw : w.IsReal) :
    Function.Periodic (rotAt hw) (2 * Real.pi) := by
  intro θ
  rw [rotAt, rotAt, rotGL_periodic θ]

private theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x),
    RingEquiv.apply_symm_apply]

private theorem isRowIsometry_rotAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    IsRowIsometry (rotAt hw θ) :=
  IsRowIsometry.map_ringEquiv _ (norm_ringEquivRealOfIsReal_symm hw) (isRowIsometry_rotGL θ)

private theorem continuous_rotAt {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (rotAt hw) := by
  have hcont : Continuous ((ringEquivRealOfIsReal hw).symm : ℝ → w.Completion) :=
    (AddMonoidHomClass.isometry_of_norm _ (norm_ringEquivRealOfIsReal_symm hw)).continuous
  exact (continuous_glEquivOfRingEquiv _ hcont).comp continuous_rotGL

end Transport

section InclContinuity

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField IsDedekindDomain"

variable (F : Type) [Field F] [NumberField F]

private def inclMatrixMap (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (archMatrixUpdate F w m i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private theorem adelicArchGLInclAt_val_eq (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = inclMatrixMap F w (k : Matrix (Fin 2) (Fin 2) w.Completion) := rfl

private theorem continuous_inclMatrixMap (w : InfinitePlace F) :
    Continuous (inclMatrixMap F w) := by
  refine continuous_matrix fun i j => ?_
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    have h : (fun m : Matrix (Fin 2) (Fin 2) v.Completion => archMatrixUpdate F v m i j v)
        = fun m => m i j :=
      funext fun m => archMatrixUpdate_apply_self F v m i j
    rw [h]
    exact (continuous_apply j).comp (continuous_apply i)
  · have h : (fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixUpdate F w m i j v)
        = fun _ => (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j :=
      funext fun m => archMatrixUpdate_apply_of_ne F w m i j hv
    rw [h]
    exact continuous_const

private theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) :
    Continuous (adelicArchGLInclAt F w) := by
  have hval : Continuous fun k : GL (Fin 2) w.Completion =>
      (k : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val
  have hcoeinv : Continuous fun k : GL (Fin 2) w.Completion =>
      ((k⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_coe_inv
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ ⇑(adelicArchGLInclAt F w) :
        GL (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = fun k : GL (Fin 2) w.Completion =>
          inclMatrixMap F w (k : Matrix (Fin 2) (Fin 2) w.Completion) :=
      funext fun k => adelicArchGLInclAt_val_eq F w k
    rw [h]
    exact (continuous_inclMatrixMap F w).comp hval
  · have h : (fun k : GL (Fin 2) w.Completion =>
        (((adelicArchGLInclAt F w k)⁻¹ : AdelicGL2 (𝓞 F) F) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
        = fun k : GL (Fin 2) w.Completion =>
          inclMatrixMap F w ((k⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
      funext k
      rw [← map_inv]
      exact adelicArchGLInclAt_val_eq F w k⁻¹
    rw [h]
    exact (continuous_inclMatrixMap F w).comp hcoeinv

private theorem rotAt_incl_mem_archRowIsometrySubgroup {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    adelicArchGLInclAt F w (rotAt hw θ) ∈ AutomorphicForm.archRowIsometrySubgroup F w :=
  Subgroup.mem_map_of_mem _
    ((AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff).mpr (isRowIsometry_rotAt hw θ))

end InclContinuity

section CircleFn

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace IsDedekindDomain"

private theorem _root_.BigCellExpansion.RealPlaces.two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

p2m_export "BigCellExpansion.RealPlaces" "two_pi_pos"
private scoped instance fact_two_pi_pos : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨two_pi_pos⟩

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

private theorem periodic_phi_rot (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) :
    Function.Periodic (fun θ : ℝ => φ (y * adelicArchGLInclAt F w (rotAt hw θ)))
      (2 * Real.pi) := by
  intro θ
  show φ (y * adelicArchGLInclAt F w (rotAt hw (θ + 2 * Real.pi)))
      = φ (y * adelicArchGLInclAt F w (rotAt hw θ))
  rw [rotAt_periodic hw θ]

private def circleFn (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) :
    AddCircle (2 * Real.pi) → ℂ :=
  (periodic_phi_rot hw φ y).lift

private theorem circleFn_coe (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) (θ : ℝ) :
    circleFn hw φ y ↑θ = φ (y * adelicArchGLInclAt F w (rotAt hw θ)) :=
  (periodic_phi_rot hw φ y).lift_coe θ

private theorem continuous_circleFn (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (y : AdelicGL2 (𝓞 F) F) :
    Continuous (circleFn hw φ y) := by
  have hqm : Topology.IsQuotientMap ((↑) : ℝ → AddCircle (2 * Real.pi)) :=
    QuotientAddGroup.isQuotientMap_mk _
  rw [hqm.continuous_iff]
  have h : (circleFn hw φ y ∘ ((↑) : ℝ → AddCircle (2 * Real.pi)))
      = fun θ : ℝ => φ (y * adelicArchGLInclAt F w (rotAt hw θ)) :=
    funext fun θ => circleFn_coe hw φ y θ
  rw [h]
  exact hφc.comp (continuous_const.mul
    ((continuous_adelicArchGLInclAt F w).comp (continuous_rotAt hw)))

private def circleRestrict (hw : w.IsReal) (y : AdelicGL2 (𝓞 F) F) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AddCircle (2 * Real.pi) → ℂ) where
  toFun ψ := circleFn hw ψ y
  map_add' ψ₁ ψ₂ := by
    funext θq
    induction θq using QuotientAddGroup.induction_on with
    | H θ =>
      show circleFn hw (ψ₁ + ψ₂) y ↑θ = circleFn hw ψ₁ y ↑θ + circleFn hw ψ₂ y ↑θ
      rw [circleFn_coe, circleFn_coe, circleFn_coe]
      rfl
  map_smul' cc ψ := by
    funext θq
    induction θq using QuotientAddGroup.induction_on with
    | H θ =>
      show circleFn hw (cc • ψ) y ↑θ = cc • circleFn hw ψ y ↑θ
      rw [circleFn_coe, circleFn_coe]
      rfl

private theorem circleFn_translate_eq (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) (c : ℝ) :
    (fun θq : AddCircle (2 * Real.pi) => circleFn hw φ y (θq + ↑c))
      = circleFn hw (fun x => φ (x * adelicArchGLInclAt F w (rotAt hw c))) y := by
  funext θq
  induction θq using QuotientAddGroup.induction_on with
  | H θ =>
    have h1 : ((θ : AddCircle (2 * Real.pi)) + ↑c)
        = ((θ + c : ℝ) : AddCircle (2 * Real.pi)) := rfl
    show circleFn hw φ y ((θ : AddCircle (2 * Real.pi)) + ↑c) = _
    rw [h1, circleFn_coe, circleFn_coe, rotAt_add, map_mul, ← mul_assoc]

private theorem circleFn_translates_mem_span (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hK : AutomorphicForm.IsArchKFiniteAt F w φ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ s' : Finset (AddCircle (2 * Real.pi) → ℂ),
      ∀ cq : AddCircle (2 * Real.pi),
        (fun θq => circleFn hw φ y (θq + cq))
          ∈ Submodule.span ℂ (s' : Set (AddCircle (2 * Real.pi) → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hK
  refine ⟨s.image fun ψ => circleFn hw ψ y, ?_⟩
  intro cq
  induction cq using QuotientAddGroup.induction_on with
  | H c =>
    rw [circleFn_translate_eq hw φ y c]
    have hmem := hs (adelicArchGLInclAt F w (rotAt hw c))
      (rotAt_incl_mem_archRowIsometrySubgroup F hw c)
    have hmap := Submodule.mem_map_of_mem (f := circleRestrict hw y) hmem
    rw [Submodule.map_span] at hmap
    have himg : (circleRestrict hw y) '' (s : Set (AdelicGL2 (𝓞 F) F → ℂ))
        = ((s.image fun ψ => circleFn hw ψ y : Finset (AddCircle (2 * Real.pi) → ℂ)) :
            Set (AddCircle (2 * Real.pi) → ℂ)) := by
      rw [Finset.coe_image]
      rfl
    rw [himg] at hmap
    exact hmap

private theorem phi_rot_expansion (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hK : AutomorphicForm.IsArchKFiniteAt F w φ)
    (y : AdelicGL2 (𝓞 F) F) :
    ∃ tfin : Finset ℤ, ∀ θ : ℝ,
      φ (y * adelicArchGLInclAt F w (rotAt hw θ))
        = ∑ n ∈ tfin,
            fourierCoeff (circleFn hw φ y) n * fourier n (θ : AddCircle (2 * Real.pi)) := by
  obtain ⟨s', hs'⟩ := circleFn_translates_mem_span hw hK y
  obtain ⟨tfin, ht⟩ := eq_finite_sum_fourier
    (⟨circleFn hw φ y, continuous_circleFn hw hφc y⟩ : C(AddCircle (2 * Real.pi), ℂ)) s' hs'
  refine ⟨tfin, fun θ => ?_⟩
  have hθ := ht ↑θ
  rw [← circleFn_coe hw φ y θ]
  exact hθ

end CircleFn

section Projections

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField IsDedekindDomain"

variable (F : Type) [Field F] [NumberField F]

private def projArch (v : InfinitePlace F) : AdeleRing (𝓞 F) F →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def projFin : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem projArch_apply (v : InfinitePlace F) (a : AdeleRing (𝓞 F) F) :
    projArch F v a = a.1 v := rfl

private theorem projFin_apply (a : AdeleRing (𝓞 F) F) : projFin F a = a.2 := rfl

private theorem matrix_ext_of_proj {A B : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : ∀ v : InfinitePlace F, (projArch F v).mapMatrix A = (projArch F v).mapMatrix B)
    (hfin : (projFin F).mapMatrix A = (projFin F).mapMatrix B) : A = B := by
  ext i j
  refine Prod.ext ?_ ?_
  · funext v
    have h : (projArch F v).mapMatrix A i j = (projArch F v).mapMatrix B i j :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) v.Completion => M i j) (harch v)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply] at h
    exact h
  · have h : (projFin F).mapMatrix A i j = (projFin F).mapMatrix B i j :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) => M i j) hfin
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projFin_apply] at h
    exact h

private theorem projArch_mapMatrix_inclMatrixMap_self (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    (projArch F w).mapMatrix (inclMatrixMap F w m) = m := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply, inclMatrixMap,
    Matrix.of_apply]
  exact archMatrixUpdate_apply_self F w m i j

private theorem projArch_mapMatrix_inclMatrixMap_of_ne {w v : InfinitePlace F} (hv : v ≠ w)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    (projArch F v).mapMatrix (inclMatrixMap F w m) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply, inclMatrixMap,
    Matrix.of_apply]
  exact archMatrixUpdate_apply_of_ne F w m i j hv

private theorem projFin_mapMatrix_inclMatrixMap (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    (projFin F).mapMatrix (inclMatrixMap F w m) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projFin_apply, inclMatrixMap,
    Matrix.of_apply]

private theorem projArch_incl_self (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    (projArch F w).mapMatrix
        ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (k : Matrix (Fin 2) (Fin 2) w.Completion) := by
  rw [adelicArchGLInclAt_val_eq, projArch_mapMatrix_inclMatrixMap_self]

private theorem projArch_incl_of_ne {w v : InfinitePlace F} (hv : v ≠ w) (k : GL (Fin 2) w.Completion) :
    (projArch F v).mapMatrix
        ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = 1 := by
  rw [adelicArchGLInclAt_val_eq, projArch_mapMatrix_inclMatrixMap_of_ne F hv]

private theorem projFin_incl (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) :
    (projFin F).mapMatrix
        ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = 1 := by
  rw [adelicArchGLInclAt_val_eq, projFin_mapMatrix_inclMatrixMap]

private theorem incl_comm {w w' : InfinitePlace F} (hne : w ≠ w')
    (k : GL (Fin 2) w.Completion) (k' : GL (Fin 2) w'.Completion) :
    adelicArchGLInclAt F w k * adelicArchGLInclAt F w' k'
      = adelicArchGLInclAt F w' k' * adelicArchGLInclAt F w k := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply matrix_ext_of_proj
  · intro v
    rw [map_mul, map_mul]
    by_cases hvw : v = w
    · subst hvw
      rw [projArch_incl_self, projArch_incl_of_ne F hne, mul_one, one_mul]
    · by_cases hvw' : v = w'
      · subst hvw'
        rw [projArch_incl_self, projArch_incl_of_ne F hvw, mul_one, one_mul]
      · rw [projArch_incl_of_ne F hvw, projArch_incl_of_ne F hvw']
  · rw [map_mul, map_mul, projFin_incl, projFin_incl]

open scoped Classical in

private theorem projArch_list_prod_incl (k : ∀ u : InfinitePlace F, GL (Fin 2) u.Completion)
    (v : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup →
      (projArch F v).mapMatrix
          (((L.map fun u => adelicArchGLInclAt F u (k u)).prod : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = if v ∈ L then (k v : Matrix (Fin 2) (Fin 2) v.Completion) else 1 := by
  intro L
  induction L with
  | nil =>
    intro _
    have h0 : v ∉ ([] : List (InfinitePlace F)) := by simp
    rw [List.map_nil, List.prod_nil, Units.val_one, map_one, if_neg h0]
  | cons u L ih =>
    intro hL
    obtain ⟨huL, hLnd⟩ := List.nodup_cons.mp hL
    rw [List.map_cons, List.prod_cons, Units.val_mul, map_mul, ih hLnd]
    by_cases hvu : v = u
    · subst hvu
      have hmem : v ∈ v :: L := by simp
      rw [projArch_incl_self, if_neg huL, mul_one, if_pos hmem]
    · rw [projArch_incl_of_ne F hvu, one_mul]
      by_cases hvL : v ∈ L
      · have hmem : v ∈ u :: L := by simp [hvL]
        rw [if_pos hvL, if_pos hmem]
      · have hnmem : v ∉ u :: L := by simp [hvu, hvL]
        rw [if_neg hvL, if_neg hnmem]

private theorem projFin_list_prod_incl (k : ∀ u : InfinitePlace F, GL (Fin 2) u.Completion) :
    ∀ L : List (InfinitePlace F),
      (projFin F).mapMatrix
          (((L.map fun u => adelicArchGLInclAt F u (k u)).prod : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = 1 := by
  intro L
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, Units.val_one, map_one]
  | cons u L ih => rw [List.map_cons, List.prod_cons, Units.val_mul, map_mul, ih, projFin_incl, one_mul]

private theorem eq_list_prod_incl (g : AdelicGL2 (𝓞 F) F)
    (k : ∀ u : InfinitePlace F, GL (Fin 2) u.Completion)
    (L : List (InfinitePlace F)) (hL : L.Nodup) (hall : ∀ u : InfinitePlace F, u ∈ L)
    (harch : ∀ v : InfinitePlace F,
      (projArch F v).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = (k v : Matrix (Fin 2) (Fin 2) v.Completion))
    (hfin : (projFin F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = 1) :
    g = (L.map fun u => adelicArchGLInclAt F u (k u)).prod := by
  apply Units.ext
  apply matrix_ext_of_proj
  · intro v
    rw [harch v, projArch_list_prod_incl F k v L hL, if_pos (hall v)]
  · rw [hfin, projFin_list_prod_incl]

end Projections

section EvalCoords

variable {G : Type}

private def evalAt (V : Submodule ℂ (G → ℂ)) (t : Finset G) : V →ₗ[ℂ] (↥t → ℂ) where
  toFun v := fun z => (v : G → ℂ) (z : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalAt_apply (V : Submodule ℂ (G → ℂ)) (t : Finset G) (v : V) (z : ↥t) :
    evalAt V t v z = (v : G → ℂ) (z : G) := rfl

private theorem mem_ker_evalAt {V : Submodule ℂ (G → ℂ)} {t : Finset G} {v : V} :
    v ∈ LinearMap.ker (evalAt V t) ↔ ∀ z ∈ t, (v : G → ℂ) z = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h z hz
    exact congrFun h ⟨z, hz⟩
  · intro h
    funext z
    exact h z z.2

private theorem exists_finset_ker_evalAt_eq_bot (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] :
    ∃ t : Finset G, LinearMap.ker (evalAt V t) = ⊥ := by
  classical
  have hex : ∃ n : ℕ, ∃ t : Finset G, Module.finrank ℂ (LinearMap.ker (evalAt V t)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨t₀, ht₀⟩ := Nat.find_spec hex
  refine ⟨t₀, ?_⟩
  by_contra hne
  obtain ⟨v, hvK, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hvz : ∃ z : G, (v : G → ℂ) z ≠ 0 := by
    by_contra hall
    exact hv0 (Subtype.ext (funext fun z => not_not.mp fun hz => hall ⟨z, hz⟩))
  obtain ⟨z, hz⟩ := hvz
  have hlt : LinearMap.ker (evalAt V (insert z t₀)) < LinearMap.ker (evalAt V t₀) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro u hu
      rw [mem_ker_evalAt] at hu ⊢
      exact fun z' hz' => hu z' (Finset.mem_insert_of_mem hz')
    · intro heq
      have hvmem : v ∈ LinearMap.ker (evalAt V (insert z t₀)) := heq ▸ hvK
      rw [mem_ker_evalAt] at hvmem
      exact hz (hvmem z (Finset.mem_insert_self z t₀))
  have hrank := Submodule.finrank_lt_finrank_of_lt hlt
  rw [ht₀] at hrank
  exact absurd hrank (not_lt.mpr (Nat.find_min' hex ⟨insert z t₀, rfl⟩))

private theorem exists_eval_coords (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (t : Finset G) (e : ↥t → (G → ℂ)), (∀ z : ↥t, e z ∈ V) ∧
      ∀ v ∈ V, v = ∑ z : ↥t, v (z : G) • e z := by
  classical
  obtain ⟨t, ht⟩ := exists_finset_ker_evalAt_eq_bot V
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (evalAt V t) ht
  refine ⟨t, fun z => (L fun z' : ↥t => if z = z' then (1 : ℂ) else 0 : V), fun z => (L _).2, ?_⟩
  intro v hv
  have hid : L (evalAt V t ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hL ⟨v, hv⟩
  have hexp : evalAt V t ⟨v, hv⟩
      = ∑ z : ↥t, v (z : G) • fun z' : ↥t => if z = z' then (1 : ℂ) else 0 := by
    have h := pi_eq_sum_univ (evalAt V t ⟨v, hv⟩)
    exact h
  have hsum : (⟨v, hv⟩ : V)
      = ∑ z : ↥t, v (z : G) • (L fun z' : ↥t => if z = z' then (1 : ℂ) else 0 : V) := by
    rw [← hid, hexp, map_sum]
    exact Finset.sum_congr rfl fun z _ => map_smul L _ _
  have hval := congrArg (fun u : V => (u : G → ℂ)) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
  exact hval

end EvalCoords

section Uniform

variable {G : Type}

private theorem coeff_mem_and_exists_uniform_support (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (C : G → C(AddCircle T, ℂ))
    (hV : ∀ cq : AddCircle T, (fun y : G => C y cq) ∈ V)
    (hfin : ∀ y : G, (Function.support fun n : ℤ => fourierCoeff (⇑(C y)) n).Finite) :
    (∀ n : ℤ, (fun y : G => fourierCoeff (⇑(C y)) n) ∈ V) ∧
    ∃ tfin : Finset ℤ, ∀ (y : G) (n : ℤ), n ∉ tfin → fourierCoeff (⇑(C y)) n = 0 := by
  classical
  obtain ⟨t, e, heV, hcoord⟩ := exists_eval_coords V

  have hCy : ∀ y : G,
      (⇑(C y) : AddCircle T → ℂ) = fun cq : AddCircle T => ∑ z : ↥t, e z y * C (z : G) cq := by
    intro y
    funext cq
    have h := congrFun (hcoord (fun y' : G => C y' cq) (hV cq)) y
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    exact Finset.sum_congr rfl fun z _ => mul_comm _ _

  have hcoeff : ∀ (y : G) (n : ℤ),
      fourierCoeff (⇑(C y)) n = ∑ z : ↥t, e z y * fourierCoeff (⇑(C (z : G))) n := by
    intro y n
    have hfn : (fun cq : AddCircle T => ∑ z : ↥t, e z y * C (z : G) cq)
        = ∑ z : ↥t, fun cq : AddCircle T => e z y * C (z : G) cq := by
      funext cq
      rw [Finset.sum_apply]
    have hint : ∀ z : ↥t,
        Integrable (fun cq : AddCircle T => e z y * C (z : G) cq) (@haarAddCircle T hT) :=
      fun z => integrable_of_continuous (continuous_const.mul (map_continuous (C (z : G))))
    have hsum := fourierCoeff.sum (Finset.univ : Finset ↥t)
      (fun z : ↥t => fun cq : AddCircle T => e z y * C (z : G) cq) (fun z _ => hint z)
    calc fourierCoeff (⇑(C y)) n
        = fourierCoeff (fun cq : AddCircle T => ∑ z : ↥t, e z y * C (z : G) cq) n := by
          rw [hCy y]
      _ = fourierCoeff (∑ z : ↥t, fun cq : AddCircle T => e z y * C (z : G) cq) n := by
          rw [hfn]
      _ = (∑ z : ↥t, fourierCoeff fun cq : AddCircle T => e z y * C (z : G) cq) n := by
          rw [hsum]
      _ = ∑ z : ↥t, fourierCoeff (fun cq : AddCircle T => e z y * C (z : G) cq) n := by
          rw [Finset.sum_apply]
      _ = ∑ z : ↥t, e z y * fourierCoeff (⇑(C (z : G))) n :=
          Finset.sum_congr rfl fun z _ => fourierCoeff.const_mul _ _ _
  refine ⟨fun n => ?_, ?_⟩
  · have hfun : (fun y : G => fourierCoeff (⇑(C y)) n)
        = ∑ z : ↥t, fourierCoeff (⇑(C (z : G))) n • e z := by
      funext y
      rw [hcoeff y n, Finset.sum_apply]
      exact Finset.sum_congr rfl fun z _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hfun]
    exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (heV z)
  · refine ⟨(Finset.univ : Finset ↥t).biUnion fun z => (hfin (z : G)).toFinset, ?_⟩
    intro y n hn
    rw [hcoeff y n]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hz : fourierCoeff (⇑(C (z : G))) n = 0 := by
      by_contra hne
      exact hn (Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ z,
        (hfin (z : G)).mem_toFinset.mpr (Function.mem_support.mpr hne)⟩)
    rw [hz, mul_zero]

end Uniform

section SpanGeneric

variable {X : Type} [TopologicalSpace X]

private theorem continuous_of_mem_span' {s : Set (X → ℂ)} (hs : ∀ f ∈ s, Continuous f)
    {v : X → ℂ} (hv : v ∈ span ℂ s) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => exact continuous_const
  | add f g _ _ ihf ihg => exact ihf.add ihg
  | smul c f _ ihf => exact ihf.const_smul c

end SpanGeneric

private theorem eq_sum_fourier_of_vanish (h : C(AddCircle T, ℂ)) (tfin : Finset ℤ)
    (hvan : ∀ n : ℤ, n ∉ tfin → fourierCoeff (⇑h) n = 0) (θ : AddCircle T) :
    h θ = ∑ n ∈ tfin, fourierCoeff (⇑h) n * fourier n θ := by
  have hsummable : Summable (fourierCoeff (⇑h)) := summable_of_ne_finset_zero hvan
  have h1 := has_pointwise_sum_fourier_series_of_summable (f := h) hsummable θ
  have h2 : HasSum (fun n : ℤ => fourierCoeff (⇑h) n • fourier n θ)
      (∑ n ∈ tfin, fourierCoeff (⇑h) n • fourier n θ) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [hvan n hn, zero_smul]
  have heq := h1.unique h2
  simpa [smul_eq_mul] using heq

section GenericClosure

variable {G : Type} [Group G]

private theorem rightTranslatesSpanFinite_add {K : Subgroup G} {f₁ f₂ : G → ℂ}
    (h₁ : RightTranslatesSpanFinite K f₁) (h₂ : RightTranslatesSpanFinite K f₂) :
    RightTranslatesSpanFinite K (f₁ + f₂) := by
  classical
  obtain ⟨s₁, hs₁⟩ := h₁
  obtain ⟨s₂, hs₂⟩ := h₂
  refine ⟨s₁ ∪ s₂, fun k hk => ?_⟩
  have e : (fun x => (f₁ + f₂) (x * k)) = (fun x => f₁ (x * k)) + fun x => f₂ (x * k) := rfl
  rw [e, Finset.coe_union]
  exact Submodule.add_mem _
    (Submodule.span_mono (fun x hx => Or.inl hx) (hs₁ k hk))
    (Submodule.span_mono (fun x hx => Or.inr hx) (hs₂ k hk))

private theorem rightTranslatesSpanFinite_smul {K : Subgroup G} (c : ℂ) {f : G → ℂ}
    (h : RightTranslatesSpanFinite K f) : RightTranslatesSpanFinite K (c • f) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun k hk => ?_⟩
  have e : (fun x => (c • f) (x * k)) = c • fun x => f (x * k) := rfl
  rw [e]
  exact Submodule.smul_mem _ c (hs k hk)

private theorem rightTranslatesSpanFinite_zero (K : Subgroup G) :
    RightTranslatesSpanFinite K (0 : G → ℂ) :=
  rightTranslatesSpanFinite_const K 0

end GenericClosure

section TranslateSpan

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace IsDedekindDomain"

variable {F : Type} [Field F] [NumberField F]

private def rTrans (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => ψ (y * g)

private def rTransₗ (g : AdelicGL2 (𝓞 F) F) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun := rTrans g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rTransₗ_apply (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    rTransₗ g ψ = rTrans g ψ := rfl

private theorem continuous_rTrans (g : AdelicGL2 (𝓞 F) F) {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : Continuous ψ) : Continuous (rTrans g ψ) :=
  hψ.comp (continuous_id.mul continuous_const)

private theorem isArchKFinite_add {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : IsArchKFinite F φ₁) (h₂ : IsArchKFinite F φ₂) : IsArchKFinite F (φ₁ + φ₂) :=
  fun w => rightTranslatesSpanFinite_add (h₁ w) (h₂ w)

private theorem isArchKFinite_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsArchKFinite F φ) :
    IsArchKFinite F (c • φ) :=
  fun w => rightTranslatesSpanFinite_smul c (h w)

private theorem isArchKFinite_zero' : IsArchKFinite F (0 : AdelicGL2 (𝓞 F) F → ℂ) :=
  fun w => rightTranslatesSpanFinite_zero (archRowIsometrySubgroup F w)

private theorem isArchKFinite_rTrans {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφK : IsArchKFinite F φ)
    {w : InfinitePlace F} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ archRowIsometrySubgroup F w) :
    IsArchKFinite F (rTrans g φ) := by
  classical
  intro w'
  by_cases hww' : w' = w
  · rw [hww']
    obtain ⟨s, hs⟩ := hφK w
    refine ⟨s, fun k hk => ?_⟩
    have e : (fun x => rTrans g φ (x * k)) = fun x => φ (x * (k * g)) := by
      funext x
      simp only [rTrans, mul_assoc]
    rw [e]
    exact hs (k * g) (Subgroup.mul_mem _ hk hg)
  · obtain ⟨s', hs'⟩ := hφK w'
    refine ⟨s'.image (rTransₗ g), fun k hk => ?_⟩
    have hcomm : k * g = g * k := by
      obtain ⟨k₀, -, rfl⟩ := Subgroup.mem_map.mp hk
      obtain ⟨g₀, -, rfl⟩ := Subgroup.mem_map.mp hg
      exact incl_comm F hww' k₀ g₀
    have e : (fun x => rTrans g φ (x * k)) = rTransₗ g (fun x => φ (x * k)) := by
      funext x
      simp only [rTransₗ_apply, rTrans, mul_assoc, hcomm]
    rw [e, Finset.coe_image]
    have hm := Submodule.mem_map_of_mem (f := rTransₗ g) (hs' k hk)
    rw [Submodule.map_span] at hm
    exact hm

private def transSpan (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ
    (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ)

private theorem finiteDimensional_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hK : IsArchKFiniteAt F w φ) : FiniteDimensional ℂ (transSpan w φ) := by
  obtain ⟨s, hs⟩ := hK
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  have hle : transSpan w φ ≤ Submodule.span ℂ (s : Set (AdelicGL2 (𝓞 F) F → ℂ)) := by
    rw [transSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hs (g : AdelicGL2 (𝓞 F) F) g.2
  exact Submodule.finiteDimensional_of_le hle

private theorem continuous_of_mem_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ transSpan w φ) :
    Continuous v := by
  have hv' : v ∈ Submodule.span ℂ
      (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ) := hv
  refine continuous_of_mem_span' ?_ hv'
  rintro _ ⟨g, rfl⟩
  exact continuous_rTrans _ hφc

private theorem isArchKFinite_of_mem_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφK : IsArchKFinite F φ) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ transSpan w φ) :
    IsArchKFinite F v := by
  have hv' : v ∈ Submodule.span ℂ
      (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact isArchKFinite_rTrans hφK g.2
  | zero => exact isArchKFinite_zero'
  | add f₁ f₂ _ _ ih₁ ih₂ => exact isArchKFinite_add ih₁ ih₂
  | smul c f _ ih => exact isArchKFinite_smul c ih

end TranslateSpan

section UniformExpansion

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace IsDedekindDomain"

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

private def coeffFn (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) (n : ℤ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => fourierCoeff (circleFn hw φ y) n

private theorem uniform_expansion (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hφK : IsArchKFinite F φ) :
    (∀ n : ℤ, Continuous (coeffFn hw φ n) ∧ IsArchKFinite F (coeffFn hw φ n)) ∧
    ∃ tfin : Finset ℤ, ∀ (y : AdelicGL2 (𝓞 F) F) (θ : ℝ),
      φ (y * adelicArchGLInclAt F w (rotAt hw θ))
        = ∑ n ∈ tfin, coeffFn hw φ n y * fourier n (θ : AddCircle (2 * Real.pi)) := by
  haveI : FiniteDimensional ℂ (transSpan w φ) := finiteDimensional_transSpan (hφK w)
  let C : AdelicGL2 (𝓞 F) F → C(AddCircle (2 * Real.pi), ℂ) :=
    fun y => ⟨circleFn hw φ y, continuous_circleFn hw hφc y⟩
  have hV : ∀ cq : AddCircle (2 * Real.pi), (fun y => C y cq) ∈ transSpan w φ := by
    intro cq
    induction cq using QuotientAddGroup.induction_on with
    | H c =>
      have e : (fun y => C y (c : AddCircle (2 * Real.pi)))
          = rTrans (adelicArchGLInclAt F w (rotAt hw c)) φ := by
        funext y
        exact circleFn_coe hw φ y c
      rw [e]
      exact Submodule.subset_span ⟨⟨_, rotAt_incl_mem_archRowIsometrySubgroup F hw c⟩, rfl⟩
  have hfin : ∀ y : AdelicGL2 (𝓞 F) F,
      (Function.support fun n : ℤ => fourierCoeff (⇑(C y)) n).Finite := by
    intro y
    obtain ⟨s', hs'⟩ := circleFn_translates_mem_span hw (hφK w) y
    exact support_fourierCoeff_finite (C y) s' hs'
  obtain ⟨hmem, tfin, htfin⟩ := coeff_mem_and_exists_uniform_support (transSpan w φ) C hV hfin
  refine ⟨fun n => ?_, tfin, fun y θ => ?_⟩
  · have hn : coeffFn hw φ n ∈ transSpan w φ := hmem n
    exact ⟨continuous_of_mem_transSpan hφc hn, isArchKFinite_of_mem_transSpan hφK hn⟩
  · have h := eq_sum_fourier_of_vanish (C y) tfin (htfin y) (θ : AddCircle (2 * Real.pi))
    rw [← circleFn_coe hw φ y θ]
    exact h

end UniformExpansion

section MultiPlace

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace IsDedekindDomain"

private theorem list_prod_map_congr {α : Type} {f g : α → ℂ} :
    ∀ L : List α, (∀ a ∈ L, f a = g a) → (L.map f).prod = (L.map g).prod := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a L ih =>
    intro h
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, h a (by simp),
      ih (fun b hb => h b (by simp [hb]))]

variable {F : Type} [Field F] [NumberField F]

private def rotProd (L : List {w : InfinitePlace F // w.IsReal}) (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    AdelicGL2 (𝓞 F) F :=
  (L.map fun w => adelicArchGLInclAt F w.1 (rotAt w.2 (θ w))).prod

private def charProd (L : List {w : InfinitePlace F // w.IsReal})
    (kd : {w : InfinitePlace F // w.IsReal} → ℤ) (θ : {w : InfinitePlace F // w.IsReal} → ℝ) : ℂ :=
  (L.map fun w => (fourier (kd w) ((θ w : ℝ) : AddCircle (2 * Real.pi)) : ℂ)).prod

private theorem rotProd_nil (θ : {w : InfinitePlace F // w.IsReal} → ℝ) : rotProd [] θ = 1 := by
  unfold rotProd
  rw [List.map_nil, List.prod_nil]

private theorem rotProd_cons (w : {w : InfinitePlace F // w.IsReal}) (L : List {w : InfinitePlace F // w.IsReal})
    (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    rotProd (w :: L) θ = adelicArchGLInclAt F w.1 (rotAt w.2 (θ w)) * rotProd L θ := by
  unfold rotProd
  rw [List.map_cons, List.prod_cons]

omit [NumberField F] in
private theorem charProd_nil (kd : {w : InfinitePlace F // w.IsReal} → ℤ)
    (θ : {w : InfinitePlace F // w.IsReal} → ℝ) : charProd [] kd θ = 1 := by
  unfold charProd
  rw [List.map_nil, List.prod_nil]

omit [NumberField F] in
private theorem charProd_cons (w : {w : InfinitePlace F // w.IsReal}) (L : List {w : InfinitePlace F // w.IsReal})
    (kd : {w : InfinitePlace F // w.IsReal} → ℤ) (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    charProd (w :: L) kd θ
      = (fourier (kd w) ((θ w : ℝ) : AddCircle (2 * Real.pi)) : ℂ) * charProd L kd θ := by
  unfold charProd
  rw [List.map_cons, List.prod_cons]

private theorem multi_real_expansion {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφK : IsArchKFinite F φ) :
    ∀ L : List {w : InfinitePlace F // w.IsReal}, L.Nodup →
      ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ)
        (kd : ι → {w : InfinitePlace F // w.IsReal} → ℤ),
        (∀ j : ι, Continuous (Cf j) ∧ IsArchKFinite F (Cf j)) ∧
        ∀ (y : AdelicGL2 (𝓞 F) F) (θ : {w : InfinitePlace F // w.IsReal} → ℝ),
          φ (y * rotProd L θ) = ∑ j : ι, Cf j y * charProd L (kd j) θ := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨Unit, inferInstance, fun _ => φ, fun _ _ => 0, fun _ => ⟨hφc, hφK⟩, fun y θ => ?_⟩
    rw [rotProd_nil, mul_one]
    simp [charProd_nil]
  | cons w₀ L ih =>
    intro hL
    obtain ⟨hw₀L, hLnd⟩ := List.nodup_cons.mp hL
    obtain ⟨ι, hι, Cf, kd, hCf, hexp⟩ := ih hLnd
    choose tfin htfin using fun j : ι => (uniform_expansion w₀.2 (hCf j).1 (hCf j).2).2
    have hcoef : ∀ (j : ι) (n : ℤ),
        Continuous (coeffFn w₀.2 (Cf j) n) ∧ IsArchKFinite F (coeffFn w₀.2 (Cf j) n) :=
      fun j n => (uniform_expansion w₀.2 (hCf j).1 (hCf j).2).1 n
    refine ⟨(Σ j : ι, ↥(tfin j)), inferInstance,
      fun p => coeffFn w₀.2 (Cf p.1) (p.2 : ℤ),
      fun p w => if w = w₀ then (p.2 : ℤ) else kd p.1 w,
      fun p => hcoef p.1 p.2, fun y θ => ?_⟩
    rw [rotProd_cons, ← mul_assoc, hexp (y * adelicArchGLInclAt F w₀.1 (rotAt w₀.2 (θ w₀))) θ]
    simp_rw [htfin]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_coe_sort (s := tfin j)]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [charProd_cons, if_pos rfl, mul_assoc]
    congr 2
    unfold charProd
    refine list_prod_map_congr L fun w hw => ?_
    have hne : ¬ w = w₀ := fun h => hw₀L (h ▸ hw)
    dsimp only
    rw [if_neg hne]

end MultiPlace

end BigCellExpansion.RealPlaces
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

noncomputable section

namespace BigCellExpansion
namespace Iwasawa

p2m_open "Matrix NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open AutomorphicForm AutomorphicForm.WindowedSiegel BigCellExpansion.RealPlaces

open scoped ComplexConjugate

section UnitaryRowIso

private theorem norm_eq_one_of_mul_conj_eq_one {d : ℂ} (h : d * conj d = 1) : ‖d‖ = 1 := by
  have h1 : ((Complex.normSq d : ℝ) : ℂ) = 1 := by rw [← Complex.mul_conj]; exact h
  have h2 : Complex.normSq d = 1 := by exact_mod_cast h1
  have h3 : ‖d‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h2
  nlinarith [norm_nonneg d, h3]

private theorem norm_sq_coe_eq_mul_conj (w : ℂ) : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

private theorem unitary_entry_eqs {u : Matrix (Fin 2) (Fin 2) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (i l : Fin 2) :
    u i 0 * conj (u l 0) + u i 1 * conj (u l 1) = if i = l then 1 else 0 := by
  have hmul : u * star u = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have h := congrFun (congrFun hmul i) l
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply] using h

private theorem isRowIsometry_of_mem_unitaryGroup {u : Matrix (Fin 2) (Fin 2) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) {g : GL (Fin 2) ℂ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = u) : IsRowIsometry g := by
  have h00 : u 0 0 * conj (u 0 0) + u 0 1 * conj (u 0 1) = 1 := by
    simpa using unitary_entry_eqs hu 0 0
  have h11 : u 1 0 * conj (u 1 0) + u 1 1 * conj (u 1 1) = 1 := by
    simpa using unitary_entry_eqs hu 1 1
  have h01 : u 0 0 * conj (u 1 0) + u 0 1 * conj (u 1 1) = 0 := by
    simpa using unitary_entry_eqs hu 0 1
  have h10 : u 1 0 * conj (u 0 0) + u 1 1 * conj (u 0 1) = 0 := by
    simpa using unitary_entry_eqs hu 1 0
  refine ⟨?_, ?_⟩
  · rw [hg]
    have hd : u.det ∈ unitary ℂ := Matrix.det_of_mem_unitary hu
    have hd' : u.det * conj u.det = 1 := by
      have h := Unitary.mul_star_self_of_mem hd
      simpa [Complex.star_def] using h
    exact norm_eq_one_of_mul_conj_eq_one hd'
  · intro x y
    rw [hg]
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_add, Complex.ofReal_pow]
    rw [norm_sq_coe_eq_mul_conj, norm_sq_coe_eq_mul_conj, norm_sq_coe_eq_mul_conj,
      norm_sq_coe_eq_mul_conj]
    simp only [map_add, map_mul]
    linear_combination (x * conj x) * h00 + (y * conj y) * h11 + (x * conj y) * h01
      + (y * conj x) * h10

private theorem isRowIsometry_of_coe_eq {K : Type} [NormedField K] {g g' : GL (Fin 2) K}
    (h : (g : Matrix (Fin 2) (Fin 2) K) = (g' : Matrix (Fin 2) (Fin 2) K)) (hg' : IsRowIsometry g') :
    IsRowIsometry g := by
  unfold IsRowIsometry at hg' ⊢
  rw [h]
  exact hg'

end UnitaryRowIso
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section ExplicitUnitary

private def bR (ζ : ℂ) : ℝ := 1 + ‖ζ‖ ^ 2

private theorem bR_pos (ζ : ℂ) : 0 < bR ζ := by unfold bR; positivity

private def ρR (ζ : ℂ) : ℝ := bR ζ ^ (-(1 / 2 : ℝ))

private theorem ρR_pos (ζ : ℂ) : 0 < ρR ζ := Real.rpow_pos_of_pos (bR_pos ζ) _

private theorem ρR_sq_mul_bR (ζ : ℂ) : ρR ζ ^ 2 * bR ζ = 1 := by
  unfold ρR
  rw [← Real.rpow_natCast, ← Real.rpow_mul (bR_pos ζ).le]
  have h : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by norm_num
  rw [h, Real.rpow_neg_one]
  exact inv_mul_cancel₀ (bR_pos ζ).ne'

private theorem ρR_key (ζ : ℂ) : ((ρR ζ : ℝ) : ℂ) ^ 2 * (ζ * conj ζ + 1) = 1 := by
  have h := ρR_sq_mul_bR ζ
  unfold bR at h
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h' : ((ρR ζ ^ 2 * (1 + ‖ζ‖ ^ 2) : ℝ) : ℂ) = (1 : ℂ) := by rw [h]; norm_num
  push_cast at h' ⊢
  linear_combination h'

private def uMat (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((ρR ζ : ℝ) : ℂ) * conj ζ, -((ρR ζ : ℝ) : ℂ); ((ρR ζ : ℝ) : ℂ), ((ρR ζ : ℝ) : ℂ) * ζ]

private theorem uMat_mul_star (ζ : ℂ) : uMat ζ * star (uMat ζ) = 1 := by
  have key := ρR_key ζ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] <;>
    first | linear_combination key | ring1

private theorem uMat_mem (ζ : ℂ) : uMat ζ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (uMat_mul_star ζ)

private def uUnit (ζ : ℂ) : ↥(Matrix.unitaryGroup (Fin 2) ℂ) := ⟨uMat ζ, uMat_mem ζ⟩

private def unitToGL (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : GL (Fin 2) ℂ := Unitary.toUnits k

private theorem unitToGL_coe (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) :
    ((unitToGL k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) := rfl

private theorem unitToGL_inv_coe (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) :
    (((unitToGL k)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [unitToGL_coe]
  exact Matrix.mem_unitaryGroup_iff.mp k.2

private theorem isRowIsometry_unitToGL (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : IsRowIsometry (unitToGL k) :=
  isRowIsometry_of_mem_unitaryGroup k.2 (unitToGL_coe k)

private theorem continuous_unitToGL : Continuous unitToGL := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val.congr fun k => ?_,
    continuous_subtype_val.matrix_conjTranspose.congr fun k => ?_⟩
  · exact (unitToGL_coe k).symm
  · show ((k : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = (((unitToGL k)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    rw [unitToGL_inv_coe, Matrix.star_eq_conjTranspose]

private theorem star_uMat_apply_zero_zero (ζ : ℂ) :
    star (uMat ζ) 0 0 = ((ρR ζ : ℝ) : ℂ) * ζ := by
  simp [uMat]

private theorem star_uMat_apply_one_zero (ζ : ℂ) :
    star (uMat ζ) 1 0 = -((ρR ζ : ℝ) : ℂ) := by
  simp [uMat]

end ExplicitUnitary
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section ComplexTransport

variable {F : Type} [Field F]

private theorem norm_ringEquivComplexOfIsComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
  rw [← BigCellExpansion.Transport.norm_ringEquivComplexOfIsComplex hw ((ringEquivComplexOfIsComplex hw).symm z),
    RingEquiv.apply_symm_apply]

private def unitAt {w : InfinitePlace F} (hw : w.IsComplex) (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) :
    GL (Fin 2) w.Completion :=
  glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (unitToGL k)

private def uAt {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂ) : GL (Fin 2) w.Completion :=
  unitAt hw (uUnit ζ)

private theorem isRowIsometry_unitAt {w : InfinitePlace F} (hw : w.IsComplex)
    (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : IsRowIsometry (unitAt hw k) :=
  BigCellExpansion.Transport.IsRowIsometry.map_ringEquiv _ (norm_ringEquivComplexOfIsComplex_symm hw)
    (isRowIsometry_unitToGL k)

private theorem isRowIsometry_uAt {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂ) :
    IsRowIsometry (uAt hw ζ) :=
  isRowIsometry_unitAt hw (uUnit ζ)

private theorem continuous_unitAt {w : InfinitePlace F} (hw : w.IsComplex) : Continuous (unitAt hw) := by
  have hcont : Continuous ((ringEquivComplexOfIsComplex hw).symm : ℂ → w.Completion) :=
    (AddMonoidHomClass.isometry_of_norm _ (norm_ringEquivComplexOfIsComplex_symm hw)).continuous
  exact (continuous_glEquivOfRingEquiv _ hcont).comp continuous_unitToGL

private theorem uAt_inv_apply {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂ) (i j : Fin 2) :
    (((uAt hw ζ)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (ringEquivComplexOfIsComplex hw).symm (star (uMat ζ) i j) := by
  unfold uAt unitAt
  rw [← map_inv, glEquivOfRingEquiv_apply_entry, unitToGL_inv_coe]
  rfl

private def θR (t : ℝ) : ℝ := Complex.arg ⟨t, 1⟩

private theorem zc_ne_zero (t : ℝ) : (⟨t, 1⟩ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem cos_θR (t : ℝ) : Real.cos (θR t) = t / ‖(⟨t, 1⟩ : ℂ)‖ := by
  unfold θR
  simp only [Complex.cos_arg (zc_ne_zero t)]

private theorem sin_θR (t : ℝ) : Real.sin (θR t) = 1 / ‖(⟨t, 1⟩ : ℂ)‖ := by
  unfold θR
  simp only [Complex.sin_arg]

private theorem cos_θR_sub_mul_sin_θR (t : ℝ) : Real.cos (θR t) - t * Real.sin (θR t) = 0 := by
  rw [cos_θR, sin_θR]
  ring

private theorem rotAt_inv_apply {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) (i j : Fin 2) :
    (((rotAt hw θ)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (ringEquivRealOfIsReal hw).symm
          ((!![Real.cos (-θ), -Real.sin (-θ); Real.sin (-θ), Real.cos (-θ)]) i j) := by
  unfold rotAt
  rw [← map_inv, ← rotGL_neg, glEquivOfRingEquiv_apply_entry, rotGL_coe]

end ComplexTransport
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section InclProd

variable (F : Type) [Field F] [NumberField F]

variable {α : Type} (p : α → InfinitePlace F) (k : ∀ a : α, GL (Fin 2) (p a).Completion)

private def inclProd (L : List α) : AdelicGL2 (𝓞 F) F :=
  (L.map fun a => adelicArchGLInclAt F (p a) (k a)).prod

private theorem inclProd_nil : inclProd F p k [] = 1 := by
  unfold inclProd; rw [List.map_nil, List.prod_nil]

private theorem inclProd_cons (a : α) (L : List α) :
    inclProd F p k (a :: L) = adelicArchGLInclAt F (p a) (k a) * inclProd F p k L := by
  unfold inclProd; rw [List.map_cons, List.prod_cons]

private theorem projFin_inclProd : ∀ L : List α,
    (projFin F).mapMatrix ((inclProd F p k L : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = 1 := by
  intro L
  induction L with
  | nil => rw [inclProd_nil, Units.val_one, map_one]
  | cons a L ih => rw [inclProd_cons, Units.val_mul, map_mul, ih, projFin_incl, one_mul]

private theorem projArch_inclProd_of_forall_ne (v : InfinitePlace F) : ∀ L : List α, (∀ a ∈ L, p a ≠ v) →
    (projArch F v).mapMatrix ((inclProd F p k L : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = 1 := by
  intro L
  induction L with
  | nil => intro _; rw [inclProd_nil, Units.val_one, map_one]
  | cons a L ih =>
    intro h
    have ha : v ≠ p a := fun hv => h a (by simp) hv.symm
    rw [inclProd_cons, Units.val_mul, map_mul, projArch_incl_of_ne F ha, one_mul]
    exact ih fun b hb => h b (by simp [hb])

private theorem projArch_inclProd_of_mem (hp : Function.Injective p) :
    ∀ (L : List α), L.Nodup → ∀ a ∈ L,
    (projArch F (p a)).mapMatrix ((inclProd F p k L : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (k a : Matrix (Fin 2) (Fin 2) (p a).Completion) := by
  intro L
  induction L with
  | nil => intro _ a ha; simp at ha
  | cons b L ih =>
    intro hL a ha
    obtain ⟨hbL, hLnd⟩ := List.nodup_cons.mp hL
    rw [inclProd_cons, Units.val_mul, map_mul]
    by_cases hab : a = b
    · subst hab
      rw [projArch_incl_self]
      have hrest : ∀ c ∈ L, p c ≠ p a := fun c hc hpc => hbL (hp hpc ▸ hc)
      rw [projArch_inclProd_of_forall_ne F p k (p a) L hrest, mul_one]
    · have haL : a ∈ L := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h hab
        · exact h
      have hne : p a ≠ p b := fun h => hab (hp h)
      rw [projArch_incl_of_ne F hne, one_mul]
      exact ih hLnd a haL

end InclProd
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section UProd

variable {F : Type} [Field F] [NumberField F]

private def uProd (L : List {w : InfinitePlace F // w.IsComplex}) (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    AdelicGL2 (𝓞 F) F :=
  (L.map fun w => adelicArchGLInclAt F w.1 (uAt w.2 (ζ w))).prod

private theorem uProd_eq_inclProd (L : List {w : InfinitePlace F // w.IsComplex})
    (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    uProd L ζ = inclProd F (fun w : {w : InfinitePlace F // w.IsComplex} => w.1)
      (fun w => uAt w.2 (ζ w)) L := rfl

private theorem rotProd_eq_inclProd (L : List {w : InfinitePlace F // w.IsReal})
    (θ : {w : InfinitePlace F // w.IsReal} → ℝ) :
    rotProd L θ = inclProd F (fun w : {w : InfinitePlace F // w.IsReal} => w.1)
      (fun w => rotAt w.2 (θ w)) L := rfl

private theorem uProd_nil (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) : uProd [] ζ = 1 := by
  unfold uProd; rw [List.map_nil, List.prod_nil]

private theorem uProd_cons (w : {w : InfinitePlace F // w.IsComplex}) (L : List {w : InfinitePlace F // w.IsComplex})
    (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    uProd (w :: L) ζ = adelicArchGLInclAt F w.1 (uAt w.2 (ζ w)) * uProd L ζ := by
  unfold uProd; rw [List.map_cons, List.prod_cons]

end UProd
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section Bridges

variable (F : Type) [Field F] [NumberField F]

open NumberField.AdelicLevel IsDedekindDomain

private theorem archComponent_glArch_coe (v : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) :
    ((archComponent F v (glArch (𝓞 F) F g) : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion)
      = (projArch F v).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j; rfl

private theorem glFin_coe (g : AdelicGL2 (𝓞 F) F) :
    ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = (projFin F).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j; rfl

private theorem adele_eq_zero_of_proj (a : AdeleRing (𝓞 F) F) (harch : ∀ v : InfinitePlace F, projArch F v a = 0)
    (hfin : projFin F a = 0) : a = 0 := by
  refine Prod.ext ?_ ?_
  · funext v
    exact harch v
  · exact hfin

private theorem finmat_ext {A B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (finAdeleEval (𝓞 F) F v).mapMatrix A = (finAdeleEval (𝓞 F) F v).mapMatrix B) :
    A = B := by
  ext i j v
  have hv := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M i j) (h v)
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply] using hv

private theorem finAdeleEval_matrix_entry (v : HeightOneSpectrum (𝓞 F))
    (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (i j : Fin 2) : (A i j) v = ((finAdeleEval (𝓞 F) F v).mapMatrix A) i j := rfl

end Bridges
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section FinPart

open NumberField.AdelicLevel IsDedekindDomain

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable (xf : FiniteAdeleRing (𝓞 F) F)

private def locK (v : HeightOneSpectrum (𝓞 F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  if xf v ∈ v.adicCompletionIntegers F then !![0, 1; 1, xf v] else !![-1, 0; (xf v)⁻¹, 1]

private def locKinv (v : HeightOneSpectrum (𝓞 F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) :=
  if xf v ∈ v.adicCompletionIntegers F then !![-(xf v), 1; 1, 0] else !![-1, 0; (xf v)⁻¹, 1]

private theorem inv_mem_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (h : xf v ∉ v.adicCompletionIntegers F) :
    (xf v)⁻¹ ∈ v.adicCompletionIntegers F :=
  ((v.adicCompletionIntegers F).mem_or_inv_mem (xf v)).resolve_left h

private theorem ne_zero_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (h : xf v ∉ v.adicCompletionIntegers F) :
    xf v ≠ 0 := by
  intro h0
  apply h
  rw [h0]
  exact zero_mem _

private theorem locK_mul_locKinv (v : HeightOneSpectrum (𝓞 F)) : locK xf v * locKinv xf v = 1 := by
  unfold locK locKinv
  split_ifs with h
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem locKinv_mul_locK (v : HeightOneSpectrum (𝓞 F)) : locKinv xf v * locK xf v = 1 := by
  unfold locK locKinv
  split_ifs with h
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem locK_mem (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) : locK xf v i j ∈ v.adicCompletionIntegers F := by
  unfold locK
  split_ifs with h
  · fin_cases i <;> fin_cases j <;> simp [h, zero_mem, one_mem]
  · have h' := inv_mem_of_not_mem xf h
    fin_cases i <;> fin_cases j <;> simp [h', zero_mem, one_mem]

private theorem locKinv_mem (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    locKinv xf v i j ∈ v.adicCompletionIntegers F := by
  unfold locKinv
  split_ifs with h
  · fin_cases i <;> fin_cases j <;> simp [h, zero_mem, one_mem]
  · have h' := inv_mem_of_not_mem xf h
    fin_cases i <;> fin_cases j <;> simp [h', zero_mem, one_mem]

private theorem locK_borel (v : HeightOneSpectrum (𝓞 F)) :
    (!![(0 : v.adicCompletion F), 1; 1, xf v] * locKinv xf v) 1 0 = 0 := by
  unfold locKinv
  split_ifs with h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hx := ne_zero_of_not_mem xf h
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx]

private def entryF (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

private theorem entryF_apply (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : entryF f hf v = f v := rfl

private def kffVal : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => entryF (fun v => locK xf v i j) (fun v => locK_mem xf v i j)

private def kffInv : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => entryF (fun v => locKinv xf v i j) (fun v => locKinv_mem xf v i j)

private theorem eval_kffVal (v : HeightOneSpectrum (𝓞 F)) :
    (finAdeleEval (𝓞 F) F v).mapMatrix (kffVal xf) = locK xf v := by
  ext i j; rfl

private theorem eval_kffInv (v : HeightOneSpectrum (𝓞 F)) :
    (finAdeleEval (𝓞 F) F v).mapMatrix (kffInv xf) = locKinv xf v := by
  ext i j; rfl

private theorem kffVal_mul_kffInv : kffVal xf * kffInv xf = 1 :=
  finmat_ext F fun v => by rw [map_mul, eval_kffVal, eval_kffInv, locK_mul_locKinv, map_one]

private theorem kffInv_mul_kffVal : kffInv xf * kffVal xf = 1 :=
  finmat_ext F fun v => by rw [map_mul, eval_kffVal, eval_kffInv, locKinv_mul_locK, map_one]

private def kff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  ⟨kffVal xf, kffInv xf, kffVal_mul_kffInv xf, kffInv_mul_kffVal xf⟩

private theorem kff_coe :
    ((kff xf : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = kffVal xf := rfl

private theorem kff_inv_coe :
    (((kff xf)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = kffInv xf := rfl

private theorem kff_mem : kff xf ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j v => ?_, fun i j v => ?_⟩
  · exact locK_mem xf v i j
  · exact locKinv_mem xf v i j

private theorem zero_eval (v : HeightOneSpectrum (𝓞 F)) : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 :=
  map_zero (finAdeleEval (𝓞 F) F v)

private theorem one_eval (v : HeightOneSpectrum (𝓞 F)) : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 :=
  map_one (finAdeleEval (𝓞 F) F v)

private theorem eval_finW (v : HeightOneSpectrum (𝓞 F)) :
    (finAdeleEval (𝓞 F) F v).mapMatrix (!![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, xf])
      = !![(0 : v.adicCompletion F), 1; 1, xf v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finAdeleEval_apply, zero_eval, one_eval]

private theorem fin_borel : ((!![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, xf]) * kffInv xf) 1 0 = 0 := by
  apply DFunLike.ext
  intro v
  rw [finAdeleEval_matrix_entry F v, map_mul, eval_finW, eval_kffInv, locK_borel]
  rfl

end FinPart
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section Global

open NumberField.AdelicLevel IsDedekindDomain

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

private def bigCell (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x

private theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  unfold adelicWeyl
  rw [← map_inv, gl2Weyl_inv]

private theorem projArch_adelicWeyl (v : InfinitePlace F) :
    (projArch F v).mapMatrix ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(0 : v.Completion), 1; 1, 0] := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold adelicWeyl
  rw [globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem projFin_adelicWeyl :
    (projFin F).mapMatrix ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, 0] := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  unfold adelicWeyl
  rw [globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem adele_one_fst_apply (v : InfinitePlace F) : (1 : AdeleRing (𝓞 F) F).1 v = 1 := map_one (projArch F v)

private theorem adele_zero_fst_apply (v : InfinitePlace F) : (0 : AdeleRing (𝓞 F) F).1 v = 0 := map_zero (projArch F v)

private theorem adele_one_snd : (1 : AdeleRing (𝓞 F) F).2 = 1 := map_one (projFin F)

private theorem adele_zero_snd : (0 : AdeleRing (𝓞 F) F).2 = 0 := map_zero (projFin F)

private theorem projArch_bigCell (x : AdeleRing (𝓞 F) F) (v : InfinitePlace F) :
    (projArch F v).mapMatrix ((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(0 : v.Completion), 1; 1, x.1 v] := by
  unfold bigCell
  rw [adelicWeyl_inv, Units.val_mul, map_mul, projArch_adelicWeyl]
  have hn : (projArch F v).mapMatrix
      ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(1 : v.Completion), x.1 v; 0, 1] := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [projArch_apply, adele_one_fst_apply, adele_zero_fst_apply]
  rw [hn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem projFin_bigCell (x : AdeleRing (𝓞 F) F) :
    (projFin F).mapMatrix ((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, x.2] := by
  unfold bigCell
  rw [adelicWeyl_inv, Units.val_mul, map_mul, projFin_adelicWeyl]
  have hn : (projFin F).mapMatrix ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(1 : FiniteAdeleRing (𝓞 F) F), x.2; 0, 1] := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [projFin_apply, adele_one_snd, adele_zero_snd]
  rw [hn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def xr (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) : ℝ :=
  extensionEmbeddingOfIsReal i.2 (x.1 i.1)

private def zC (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) : ℂ :=
  extensionEmbedding w.1 (x.1 w.1)

private def θx (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) : ℝ := θR (xr F x i)

private def Lr : List {w : InfinitePlace F // w.IsReal} :=
  (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}).toList

private def Lc : List {w : InfinitePlace F // w.IsComplex} :=
  (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex}).toList

private theorem Lr_nodup : (Lr F).Nodup := Finset.nodup_toList _

private theorem Lc_nodup : (Lc F).Nodup := Finset.nodup_toList _

private theorem mem_Lr (i : {w : InfinitePlace F // w.IsReal}) : i ∈ Lr F := Finset.mem_toList.mpr (Finset.mem_univ i)

private theorem mem_Lc (w : {w : InfinitePlace F // w.IsComplex}) : w ∈ Lc F :=
  Finset.mem_toList.mpr (Finset.mem_univ w)

private def kInf (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F := uProd (Lc F) (zC F x) * rotProd (Lr F) (θx F x)

private theorem projFin_kInf (x : AdeleRing (𝓞 F) F) :
    (projFin F).mapMatrix ((kInf F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = 1 := by
  unfold kInf
  rw [Units.val_mul, map_mul, uProd_eq_inclProd, rotProd_eq_inclProd, projFin_inclProd, projFin_inclProd,
    one_mul]

private theorem projArch_kInf_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    (projArch F i.1).mapMatrix ((kInf F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (rotAt i.2 (θx F x i) : Matrix (Fin 2) (Fin 2) i.1.Completion) := by
  unfold kInf
  rw [Units.val_mul, map_mul, uProd_eq_inclProd, rotProd_eq_inclProd]
  have hc : ∀ w ∈ Lc F, (w : {w : InfinitePlace F // w.IsComplex}).1 ≠ i.1 := by
    intro w _ hw
    have h1 : i.1.IsComplex := hw ▸ w.2
    exact (not_isReal_iff_isComplex.mpr h1) i.2
  rw [projArch_inclProd_of_forall_ne F _ _ i.1 (Lc F) hc, one_mul]
  exact projArch_inclProd_of_mem F _ _ Subtype.val_injective (Lr F) (Lr_nodup F) i (mem_Lr F i)

private theorem projArch_kInf_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (projArch F w.1).mapMatrix ((kInf F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (uAt w.2 (zC F x w) : Matrix (Fin 2) (Fin 2) w.1.Completion) := by
  unfold kInf
  rw [Units.val_mul, map_mul, uProd_eq_inclProd, rotProd_eq_inclProd]
  have hr : ∀ i ∈ Lr F, (i : {w : InfinitePlace F // w.IsReal}).1 ≠ w.1 := by
    intro i _ hi
    have h1 : w.1.IsReal := hi ▸ i.2
    exact (not_isReal_iff_isComplex.mpr w.2) h1
  rw [projArch_inclProd_of_forall_ne F _ _ w.1 (Lr F) hr, mul_one]
  exact projArch_inclProd_of_mem F _ _ Subtype.val_injective (Lc F) (Lc_nodup F) w (mem_Lc F w)

private def kFval (x : AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, kffVal x.2 i j)

private def kFinv (x : AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, kffInv x.2 i j)

private theorem projArch_kFval (x : AdeleRing (𝓞 F) F) (v : InfinitePlace F) :
    (projArch F v).mapMatrix (kFval F x) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, kFval, Matrix.of_apply, projArch_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem projArch_kFinv (x : AdeleRing (𝓞 F) F) (v : InfinitePlace F) :
    (projArch F v).mapMatrix (kFinv F x) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, kFinv, Matrix.of_apply, projArch_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem projFin_kFval (x : AdeleRing (𝓞 F) F) : (projFin F).mapMatrix (kFval F x) = kffVal x.2 := by
  ext i j; rfl

private theorem projFin_kFinv (x : AdeleRing (𝓞 F) F) : (projFin F).mapMatrix (kFinv F x) = kffInv x.2 := by
  ext i j; rfl

private theorem kFval_mul_kFinv (x : AdeleRing (𝓞 F) F) : kFval F x * kFinv F x = 1 := by
  apply matrix_ext_of_proj
  · intro v
    rw [map_mul, projArch_kFval, projArch_kFinv, one_mul, map_one]
  · rw [map_mul, projFin_kFval, projFin_kFinv, kffVal_mul_kffInv, map_one]

private theorem kFinv_mul_kFval (x : AdeleRing (𝓞 F) F) : kFinv F x * kFval F x = 1 := by
  apply matrix_ext_of_proj
  · intro v
    rw [map_mul, projArch_kFval, projArch_kFinv, one_mul, map_one]
  · rw [map_mul, projFin_kFval, projFin_kFinv, kffInv_mul_kffVal, map_one]

private def kF (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  ⟨kFval F x, kFinv F x, kFval_mul_kFinv F x, kFinv_mul_kFval F x⟩

private theorem kF_coe (x : AdeleRing (𝓞 F) F) :
    ((kF F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = kFval F x := rfl

private theorem glArch_kF (x : AdeleRing (𝓞 F) F) : glArch (𝓞 F) F (kF F x) = 1 := by
  apply Units.ext
  ext i j
  rfl

private theorem glFin_kF (x : AdeleRing (𝓞 F) F) : glFin (𝓞 F) F (kF F x) = kff x.2 := by
  apply Units.ext
  ext i j
  rfl

private theorem glFin_kF_mem (x : AdeleRing (𝓞 F) F) : glFin (𝓞 F) F (kF F x) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [glFin_kF]
  exact kff_mem x.2

private theorem glFin_kInf (x : AdeleRing (𝓞 F) F) : glFin (𝓞 F) F (kInf F x) = 1 := by
  apply Units.ext
  rw [glFin_coe, projFin_kInf, Units.val_one]

private def kTot (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F := kInf F x * kF F x

private theorem glFin_kTot_mem (x : AdeleRing (𝓞 F) F) : glFin (𝓞 F) F (kTot F x) ∈ finiteIntegralGL2 (𝓞 F) F := by
  unfold kTot
  rw [map_mul, glFin_kInf, one_mul]
  exact glFin_kF_mem F x

private theorem isRowIsometry_kTot (x : AdeleRing (𝓞 F) F) (v : InfinitePlace F) :
    IsRowIsometry (archComponent F v (glArch (𝓞 F) F (kTot F x))) := by
  unfold kTot
  rw [map_mul, glArch_kF, mul_one]
  rcases isReal_or_isComplex v with hv | hv
  · refine isRowIsometry_of_coe_eq (g' := rotAt hv (θx F x ⟨v, hv⟩)) ?_ (isRowIsometry_rotAt hv _)
    rw [archComponent_glArch_coe]
    exact projArch_kInf_real F x ⟨v, hv⟩
  · refine isRowIsometry_of_coe_eq (g' := uAt hv (zC F x ⟨v, hv⟩)) ?_ (isRowIsometry_uAt hv _)
    rw [archComponent_glArch_coe]
    exact projArch_kInf_complex F x ⟨v, hv⟩

private theorem projArch_kTot_inv_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    (projArch F i.1).mapMatrix (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion) := by
  have h1 : archComponent F i.1 (glArch (𝓞 F) F (kTot F x)) = rotAt i.2 (θx F x i) := by
    apply Units.ext
    unfold kTot
    rw [map_mul, glArch_kF, mul_one, archComponent_glArch_coe]
    exact projArch_kInf_real F x i
  rw [← archComponent_glArch_coe, map_inv, map_inv, h1]

private theorem projArch_kTot_inv_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (projArch F w.1).mapMatrix (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion) := by
  have h1 : archComponent F w.1 (glArch (𝓞 F) F (kTot F x)) = uAt w.2 (zC F x w) := by
    apply Units.ext
    unfold kTot
    rw [map_mul, glArch_kF, mul_one, archComponent_glArch_coe]
    exact projArch_kInf_complex F x w
  rw [← archComponent_glArch_coe, map_inv, map_inv, h1]

private theorem projFin_kTot_inv (x : AdeleRing (𝓞 F) F) :
    (projFin F).mapMatrix (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = kffInv x.2 := by
  have h1 : glFin (𝓞 F) F (kTot F x) = kff x.2 := by
    unfold kTot
    rw [map_mul, glFin_kInf, one_mul, glFin_kF]
  rw [← glFin_coe, map_inv, h1, kff_inv_coe]

private theorem real_borel_entry (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    (!![(0 : i.1.Completion), 1; 1, x.1 i.1]
        * (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion)) 1 0
      = 0 := by
  have e00 : (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion) 0 0
      = (ringEquivRealOfIsReal i.2).symm (Real.cos (θx F x i)) := by
    simp [rotAt_inv_apply]
  have e10 : (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion) 1 0
      = (ringEquivRealOfIsReal i.2).symm (-Real.sin (θx F x i)) := by
    simp [rotAt_inv_apply]
  have hx : ringEquivRealOfIsReal i.2 (x.1 i.1) = xr F x i := rfl
  rw [Matrix.mul_apply, Fin.sum_univ_two, e00, e10]
  show (1 : i.1.Completion) * (ringEquivRealOfIsReal i.2).symm (Real.cos (θx F x i))
      + x.1 i.1 * (ringEquivRealOfIsReal i.2).symm (-Real.sin (θx F x i)) = 0
  apply (ringEquivRealOfIsReal i.2).injective
  rw [map_zero, map_add, map_mul, map_mul, map_one, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    one_mul, hx]
  unfold θx
  linear_combination cos_θR_sub_mul_sin_θR (xr F x i)

private theorem complex_borel_entry (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (!![(0 : w.1.Completion), 1; 1, x.1 w.1]
        * (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion)) 1 0
      = 0 := by
  have e00 : (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion) 0 0
      = (ringEquivComplexOfIsComplex w.2).symm (((ρR (zC F x w) : ℝ) : ℂ) * zC F x w) := by
    rw [uAt_inv_apply, star_uMat_apply_zero_zero]
  have e10 : (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion) 1 0
      = (ringEquivComplexOfIsComplex w.2).symm (-((ρR (zC F x w) : ℝ) : ℂ)) := by
    rw [uAt_inv_apply, star_uMat_apply_one_zero]
  have hz : ringEquivComplexOfIsComplex w.2 (x.1 w.1) = zC F x w := rfl
  have hx' : x.1 w.1 = (ringEquivComplexOfIsComplex w.2).symm (zC F x w) := by
    rw [← hz, RingEquiv.symm_apply_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, e00, e10]
  show (1 : w.1.Completion) * (ringEquivComplexOfIsComplex w.2).symm (((ρR (zC F x w) : ℝ) : ℂ) * zC F x w)
      + x.1 w.1 * (ringEquivComplexOfIsComplex w.2).symm (-((ρR (zC F x w) : ℝ) : ℂ)) = 0
  rw [hx', one_mul, ← map_mul, ← map_add, ← map_zero (ringEquivComplexOfIsComplex w.2).symm]
  congr 1
  ring

private theorem bigCell_mul_kTot_inv_mem_adelicBorel (x : AdeleRing (𝓞 F) F) :
    bigCell F x * (kTot F x)⁻¹ ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff, Units.val_mul]
  apply adele_eq_zero_of_proj
  · intro v
    have hentry : projArch F v
        ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
          * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) 1 0)
        = ((projArch F v).mapMatrix
            ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
              * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))) 1 0 := rfl
    rw [hentry, map_mul, projArch_bigCell]
    rcases isReal_or_isComplex v with hv | hv
    · rw [projArch_kTot_inv_real F x ⟨v, hv⟩]
      exact real_borel_entry F x ⟨v, hv⟩
    · rw [projArch_kTot_inv_complex F x ⟨v, hv⟩]
      exact complex_borel_entry F x ⟨v, hv⟩
  · have hentry : projFin F
        ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
          * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) 1 0)
        = ((projFin F).mapMatrix
            ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
              * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))) 1 0 := rfl
    rw [hentry, map_mul, projFin_bigCell, projFin_kTot_inv]
    exact fin_borel x.2

private theorem bigCell_eq_borel_mul_kTot (x : AdeleRing (𝓞 F) F) :
    bigCell F x = (bigCell F x * (kTot F x)⁻¹) * kTot F x := by
  rw [inv_mul_cancel_right]

end Global
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end BigCellExpansion.Iwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section Height

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain"

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace BigCellExpansion
namespace Height

variable (F : Type) [Field F] [NumberField F]

variable {F}

private theorem finHeight_mul_integral (g k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) :
    finHeight F (g * k) = finHeight F g := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_integral _ _ (hk v) fun i j => ?_
  rw [← map_inv]
  exact hk' v i j

private theorem adelicHeight_mul_of_integral_of_rowIsometry (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖
        ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v (glFin (𝓞 F) F k)⁻¹ :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    adelicHeight F (g * k) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hka, finHeight_mul_integral _ _ hk hk']

end BigCellExpansion.Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section Height

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain"

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace BigCellExpansion
namespace Height

section HeightOne

variable {K : Type*} [NormedField K]

private theorem finLocalHeight_one : finLocalHeight (1 : GL (Fin 2) K) = 1 := by
  unfold finLocalHeight rowMaxNorm
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, Matrix.det_one,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq, norm_one, norm_zero,
    max_eq_right zero_le_one]
  norm_num

end HeightOne
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

variable (F : Type) [Field F] [NumberField F]

private theorem finHeight_one : finHeight F 1 = 1 := by
  unfold finHeight
  simp only [map_one, finLocalHeight_one, finprod_one]

private theorem adelicHeight_one : adelicHeight F 1 = 1 := by
  unfold adelicHeight
  rw [map_one, map_one, archHeight_one, finHeight_one, mul_one]

private def flatOne (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)

private theorem flatOne_apply_one (s : ℂ) : flatOne F s 1 = 1 := by
  unfold flatOne
  rw [adelicHeight_one, Complex.ofReal_one, Complex.one_cpow]

variable {F}

end BigCellExpansion.Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section Height

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain"

open AutomorphicForm AutomorphicForm.WindowedSiegel

namespace BigCellExpansion
namespace Height

variable (F : Type) [Field F] [NumberField F]

private theorem norm_finComponent_le_one_of_mem {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    (∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
        ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
        ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := by
  rw [mem_finiteIntegralGL2_iff] at hk
  refine ⟨fun v i j => ?_, fun v i j => ?_⟩
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

end BigCellExpansion.Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section Height

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain"

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace BigCellExpansion
namespace Height

section Local

variable {K : Type*} [NormedField K]

private theorem finLocalHeight_of_row (g : GL (Fin 2) K) {x : K}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = x)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1) :
    finLocalHeight g = ((max 1 ‖x‖)⁻¹) ^ 2 := by
  unfold finLocalHeight rowMaxNorm
  rw [hdet, h10, h11, norm_one, inv_pow, one_div]

private theorem localHeight_of_row (g : GL (Fin 2) K) {x : K}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 1) (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = x)
    (hdet : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1) :
    localHeight g = (1 + ‖x‖ ^ 2)⁻¹ := by
  unfold localHeight rowNormSq
  rw [hdet, h10, h11, norm_one, one_pow, one_div]

end Local
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

variable (F : Type) [Field F] [NumberField F]

private theorem weyl_inv_mul_unipotent_val (x : AdeleRing (𝓞 F) F) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, x] := by
  have hw : ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, 0] := by
    ext i j
    rw [show adelicWeyl (𝓞 F) F = globalPoints (𝓞 F) F gl2Weyl from rfl, globalPoints_apply, gl2Weyl_val]
    fin_cases i <;> fin_cases j <;> simp
  rw [show (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F from by
      rw [show adelicWeyl (𝓞 F) F = globalPoints (𝓞 F) F gl2Weyl from rfl, ← map_inv, gl2Weyl_inv],
    Units.val_mul, hw, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem adelicHeight_weyl_unipotent (x : AdeleRing (𝓞 F) F) :
    adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
      = (∏ w : InfinitePlace F, ((1 + ‖x.1 w‖ ^ 2)⁻¹) ^ w.mult)
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖)⁻¹) ^ 2 := by
  set g : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hg
  have hval := weyl_inv_mul_unipotent_val F x
  rw [← hg] at hval
  have h10 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 1 := by
    rw [hval]; rfl
  have h11 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = x := by
    rw [hval]; rfl
  have h00 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = 0 := by
    rw [hval]; rfl
  have h01 : ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 1 := by
    rw [hval]; rfl

  have harch : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) = (1 + ‖x.1 w‖ ^ 2)⁻¹ := by
    intro w
    refine localHeight_of_row _ ?_ ?_ ?_
    · rw [archComponent_apply, glArch_apply, h10]; rfl
    · rw [archComponent_apply, glArch_apply, h11]
    · rw [Matrix.det_fin_two, archComponent_apply, archComponent_apply, archComponent_apply,
        archComponent_apply, glArch_apply, glArch_apply, glArch_apply, glArch_apply, h00, h01, h10, h11]
      show ‖(0 : w.Completion) * x.1 w - 1 * 1‖ = 1
      rw [zero_mul, mul_one, zero_sub, norm_neg, norm_one]

  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) = ((max 1 ‖x.2 v‖)⁻¹) ^ 2 := by
    intro v
    refine finLocalHeight_of_row _ ?_ ?_ ?_
    · rw [finComponent_apply, glFin_apply, h10]; rfl
    · rw [finComponent_apply, glFin_apply, h11]
    · rw [Matrix.det_fin_two, finComponent_apply, finComponent_apply, finComponent_apply,
        finComponent_apply, glFin_apply, glFin_apply, glFin_apply, glFin_apply, h00, h01, h10, h11]
      show ‖(0 : v.adicCompletion F) * x.2 v - 1 * 1‖ = 1
      rw [zero_mul, mul_one, zero_sub, norm_neg, norm_one]
  unfold adelicHeight archHeight finHeight
  rw [Finset.prod_congr rfl fun w _ => by rw [harch w], finprod_congr hfin]

end BigCellExpansion.Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

end Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

section PlaceMeasure

set_option autoImplicit false

p2m_open "MeasureTheory Complex NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace IsDedekindDomain"

open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter

open scoped Pointwise ENNReal NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing InfinitePlace.IsReal InfinitePlace.IsComplex mk place HeightOneSpectrum.one_lt_absNorm InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfinitePlace AdeleRing FinitePlace.norm_def AdelicHaar.compactSpace_adicCompletionIntegers AdelicLevel.isOpen_setOf_valued_le AdelicLevel.exists_valued_eq_exp_neg TateGlobal.ideleNorm TateGlobal.localChar TateGlobal.archUnitHom AdelicVolume.archCentralUnit AdelicVolume.archCentralUnit_snd AdelicVolume.archCentralUnit_fst_self AdelicVolume.archCentralUnit_fst_of_ne TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles AdeleRing.val_finitePartUnits"
namespace AdelicCountability
p2m_open "NumberField"

end NumberField.AdelicCountability
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

namespace BigCellExpansion
namespace PlaceMeasure

variable (F : Type) [Field F] [NumberField F]

@[reducible] private def placeBorel (w : InfinitePlace F) : MeasurableSpace (w.Completion) := borel _

attribute [local instance] placeBorel

private scoped instance placeBorelSpace (w : InfinitePlace F) : BorelSpace (w.Completion) := ⟨rfl⟩

variable {F}

variable (F) in
@[reducible] private def infMS : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))

attribute [local instance] infMS

end BigCellExpansion.PlaceMeasure
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces"

namespace BigCellExpansion
namespace PlaceMeasure

attribute [local instance] placeBorel infMS

variable {F : Type} [Field F] [NumberField F]

end BigCellExpansion.PlaceMeasure
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end PlaceMeasure
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section CellFactor

set_option autoImplicit false

noncomputable section

namespace BigCellExpansion
namespace CellFactor

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicHeight"

open AutomorphicForm IsDedekindDomain

open BigCellExpansion.Height

open scoped NNReal

attribute [local instance] BigCellExpansion.PlaceMeasure.placeBorel BigCellExpansion.PlaceMeasure.infMS

variable (F : Type) [Field F] [NumberField F]

private def archCellFactor (y : (w : InfinitePlace F) → w.Completion) : ℝ :=
  ∏ w : InfinitePlace F, ((1 + ‖y w‖ ^ 2)⁻¹) ^ w.mult

private def finCellFactor (z : FiniteAdeleRing (𝓞 F) F) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((max 1 ‖z v‖)⁻¹) ^ 2

variable {F}

private theorem archCellFactor_nonneg (y : (w : InfinitePlace F) → w.Completion) :
    0 ≤ archCellFactor F y :=
  Finset.prod_nonneg fun w _ => pow_nonneg (inv_nonneg.mpr (by positivity)) _

private theorem finCellFactor_nonneg (z : FiniteAdeleRing (𝓞 F) F) : 0 ≤ finCellFactor F z :=
  finprod_nonneg fun _ => sq_nonneg _

private theorem adelicHeight_weyl_unipotent_factor (x : AdeleRing (𝓞 F) F) :
    (adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ)
      = archCellFactor F x.1 * finCellFactor F x.2 :=
  adelicHeight_weyl_unipotent F x

private theorem flatOne_weyl_unipotent (s : ℂ) (x : AdeleRing (𝓞 F) F) :
    flatOne F s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
      = ((archCellFactor F x.1 : ℝ) : ℂ) ^ (s + 1 / 2)
          * ((finCellFactor F x.2 : ℝ) : ℂ) ^ (s + 1 / 2) := by
  unfold flatOne
  rw [adelicHeight_weyl_unipotent_factor, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (archCellFactor_nonneg x.1) (finCellFactor_nonneg x.2)]

private theorem finCellFactor_cpow_eq (s : ℂ) (z : FiniteAdeleRing (𝓞 F) F)
    (hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      max 1 ‖z v‖).Finite) :
    ((finCellFactor F z : ℝ) : ℂ) ^ (s + 1 / 2)
      = ((∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖ : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hr1 : (1 : ℝ) ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖ :=
    one_le_finprod fun v => le_max_left _ _
  have hr0 : (0 : ℝ) < ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖ := lt_of_lt_of_le one_pos hr1

  have hreal : finCellFactor F z
      = ((∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖) ^ 2)⁻¹ := by
    unfold finCellFactor
    simp_rw [inv_pow]
    rw [finprod_inv_distrib, ← finprod_pow hsupp]
  rw [hreal]

  have hbase : ((((∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖) ^ 2)⁻¹ : ℝ) : ℂ)
      = ((∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖ : ℝ) : ℂ) ^ (-2 : ℤ) := by
    push_cast
    rw [zpow_neg, zpow_two, sq]
  have him : (Complex.log ((∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖z v‖ : ℝ) : ℂ)
      * ((-2 : ℤ) : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hr0.le]
    simp
  rw [hbase, ← Complex.cpow_intCast, ← Complex.cpow_mul]
  · congr 1
    push_cast
    ring
  · rw [him]
    linarith [Real.pi_pos]
  · rw [him]
    linarith [Real.pi_pos]

end BigCellExpansion.CellFactor
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end CellFactor
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section ArchFactor

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace"

open scoped Classical

attribute [local instance] BigCellExpansion.PlaceMeasure.placeBorel BigCellExpansion.PlaceMeasure.infMS

noncomputable section

namespace BigCellExpansion
namespace ArchFactor

variable (F : Type) [Field F] [NumberField F]

variable {F} in

private def mR {w : InfinitePlace F} (hw : w.IsReal) : w.Completion ≃ᵐ ℝ :=
  (Completion.isometryEquivRealOfIsReal hw).toHomeomorph.toMeasurableEquiv

variable {F} in

private def mC {w : InfinitePlace F} (hw : w.IsComplex) : w.Completion ≃ᵐ ℂ :=
  (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.toMeasurableEquiv

private def sigmaC : {w : InfinitePlace F // ¬ w.IsReal} ≃ {w : InfinitePlace F // w.IsComplex} :=
  Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex

private def eR : ((i : {w : InfinitePlace F // w.IsReal}) → i.1.Completion)
    ≃ᵐ ({w : InfinitePlace F // w.IsReal} → ℝ) :=
  MeasurableEquiv.piCongrRight fun i => mR i.2

private def eC' : ((b : {w : InfinitePlace F // ¬ w.IsReal}) → b.1.Completion)
    ≃ᵐ ({w : InfinitePlace F // ¬ w.IsReal} → ℂ) :=
  MeasurableEquiv.piCongrRight fun b => mC (not_isReal_iff_isComplex.mp b.2)

private def eL : ({w : InfinitePlace F // ¬ w.IsReal} → ℂ) ≃ᵐ ({w : InfinitePlace F // w.IsComplex} → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (sigmaC F)

private def Φ : InfiniteAdeleRing F ≃ᵐ mixedEmbedding.mixedSpace F :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun w : InfinitePlace F => w.Completion)
      (fun w : InfinitePlace F => w.IsReal)).trans
    (MeasurableEquiv.prodCongr (eR F) ((eC' F).trans (eL F)))

omit [NumberField F] in
private theorem Φ_fst (y : InfiniteAdeleRing F) (i : {w : InfinitePlace F // w.IsReal}) :
    (Φ F y).1 i = Completion.extensionEmbeddingOfIsReal i.2 (y i) := rfl

omit [NumberField F] in
private theorem Φ_snd (y : InfiniteAdeleRing F) :
    (Φ F y).2 = eL F (fun b : {w : InfinitePlace F // ¬ w.IsReal} =>
      mC (not_isReal_iff_isComplex.mp b.2) (y b)) := rfl

omit [NumberField F] in
private theorem Φ_snd_sigmaC (y : InfiniteAdeleRing F) (b : {w : InfinitePlace F // ¬ w.IsReal}) :
    (Φ F y).2 (sigmaC F b) = Completion.extensionEmbedding b.1 (y b) := by
  rw [Φ_snd]
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) (sigmaC F)
    (fun b : {w : InfinitePlace F // ¬ w.IsReal} => mC (not_isReal_iff_isComplex.mp b.2) (y b)) b

private theorem prod_cpow_ofReal_nonneg {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    (r : ℂ) : (((∏ i ∈ S, f i : ℝ)) : ℂ) ^ r = ∏ i ∈ S, ((f i : ℝ) : ℂ) ^ r := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a (Finset.mem_insert_self a S))
        (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private theorem inv_ofReal_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    (((u⁻¹ : ℝ)) : ℂ) ^ p = (u : ℂ) ^ (-p) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

private theorem inv_sq_ofReal_cpow {u : ℝ} (hu : 0 < u) (p : ℂ) :
    ((((u⁻¹) ^ 2 : ℝ)) : ℂ) ^ p = (u : ℂ) ^ (-p + -p) := by
  rw [sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hu.le) (inv_nonneg.2 hu.le),
    inv_ofReal_cpow hu, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hu.ne')]

private def gMix (s : ℂ) (x : mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ w, ((1 + x.1 w ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))) *
    ∏ w, ((1 + ‖x.2 w‖ ^ 2 : ℝ) : ℂ) ^ (-(2 * s + 1))

variable {F} in
omit [NumberField F] in
private theorem norm_extensionEmbeddingOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖Completion.extensionEmbeddingOfIsReal hw x‖ = ‖x‖ :=
  (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x

variable {F} in
omit [NumberField F] in
private theorem norm_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

private theorem archCellFactor_split (y : InfiniteAdeleRing F) :
    BigCellExpansion.CellFactor.archCellFactor F y
      = (∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖y i‖ ^ 2)⁻¹)
          * ∏ b : {w : InfinitePlace F // ¬ w.IsReal}, ((1 + ‖y b‖ ^ 2)⁻¹) ^ 2 := by
  unfold BigCellExpansion.CellFactor.archCellFactor
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)
    (fun w : InfinitePlace F => ((1 + ‖y w‖ ^ 2)⁻¹) ^ w.mult)]
  congr 1
  · refine Fintype.prod_congr _ _ (fun i => ?_)
    rw [mult_isReal i, pow_one]
  · refine Fintype.prod_congr _ _ (fun b => ?_)
    have hm : (b.1).mult = 2 := mult_isComplex ⟨b.1, not_isReal_iff_isComplex.mp b.2⟩
    rw [hm]

private theorem arch_integrand_eq (s : ℂ) (y : InfiniteAdeleRing F) :
    ((BigCellExpansion.CellFactor.archCellFactor F y : ℝ) : ℂ) ^ (s + 1 / 2) = gMix F s (Φ F y) := by

  have hA' : ∀ i ∈ (Finset.univ : Finset {w : InfinitePlace F // w.IsReal}),
      0 ≤ (1 + ‖y i‖ ^ 2)⁻¹ := fun i _ => inv_nonneg.2 (by positivity)
  have hB' : ∀ b ∈ (Finset.univ : Finset {w : InfinitePlace F // ¬ w.IsReal}),
      0 ≤ ((1 + ‖y b‖ ^ 2)⁻¹) ^ 2 := fun b _ => pow_nonneg (inv_nonneg.2 (by positivity)) _
  have hA : 0 ≤ ∏ i : {w : InfinitePlace F // w.IsReal}, (1 + ‖y i‖ ^ 2)⁻¹ :=
    Finset.prod_nonneg hA'
  have hB : 0 ≤ ∏ b : {w : InfinitePlace F // ¬ w.IsReal}, ((1 + ‖y b‖ ^ 2)⁻¹) ^ 2 :=
    Finset.prod_nonneg hB'

  rw [archCellFactor_split, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hA hB,
    prod_cpow_ofReal_nonneg _ _ hA', prod_cpow_ofReal_nonneg _ _ hB']
  unfold gMix
  congr 1
  ·
    refine Fintype.prod_congr _ _ (fun i => ?_)
    rw [inv_ofReal_cpow (u := 1 + ‖y i‖ ^ 2) (by positivity), Φ_fst]
    congr 2
    rw [← sq_abs (Completion.extensionEmbeddingOfIsReal i.2 (y i)), ← Real.norm_eq_abs,
      norm_extensionEmbeddingOfIsReal]
  ·
    have he : -(s + 1 / 2) + -(s + 1 / 2) = -(2 * s + 1) := by ring
    refine Fintype.prod_equiv (sigmaC F) _ _ (fun b => ?_)
    rw [inv_sq_ofReal_cpow (u := 1 + ‖y b‖ ^ 2) (by positivity), he, Φ_snd_sigmaC,
      norm_extensionEmbedding]

end BigCellExpansion.ArchFactor
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end ArchFactor
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section Height

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHeight NumberField.AdelicLevel"

open AutomorphicForm AutomorphicForm.WindowedSiegel

noncomputable section

namespace BigCellExpansion
namespace Height

variable (F : Type) [Field F] [NumberField F]

private theorem flatOne_spherical (s : ℂ) (k : AdelicGL2 (𝓞 F) F)
    (hk : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k)))
    (g : AdelicGL2 (𝓞 F) F) : flatOne F s (g * k) = flatOne F s g := by
  unfold flatOne
  rw [adelicHeight_mul_of_integral_of_rowIsometry g k (norm_finComponent_le_one_of_mem F hk).1
    (norm_finComponent_le_one_of_mem F hk).2 hka]

end BigCellExpansion.Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end Height
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section FiniteShell

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero"

open scoped NNReal

namespace BigCellExpansion
namespace FiniteShell

variable {F : Type} [Field F] [NumberField F]

section Local

variable (v : HeightOneSpectrum (𝓞 F))

private theorem one_lt_absNorm_real : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

private def placeExp (y : v.adicCompletion F) : ℕ := (log (Valued.v y)).toNat

private theorem placeExp_eq_zero_of_mem {y : v.adicCompletion F} (hy : y ∈ v.adicCompletionIntegers F) :
    placeExp v y = 0 := by
  simp only [placeExp, Int.toNat_eq_zero]
  by_cases h0 : Valued.v y = 0
  · rw [h0, log_zero]
  · rw [log_le_iff_le_exp h0, exp_zero]
    exact (mem_adicCompletionIntegers _ _ _).mp hy

private theorem max_one_norm (y : v.adicCompletion F) :
    max 1 ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ placeExp v y := by
  have hq1 : (1 : ℝ) ≤ Ideal.absNorm v.asIdeal := (one_lt_absNorm_real v).le
  by_cases hy : Valued.v y = 0
  · have hy0 : y = 0 := (Valuation.zero_iff _).mp hy
    rw [hy0, norm_zero, max_eq_left zero_le_one, placeExp, map_zero, log_zero, Int.toNat_zero, pow_zero]
  · have hlog : ((unzero hy).toAdd : ℤ) = log (Valued.v y) := by
      conv_rhs => rw [← coe_unzero hy]
      rfl
    rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hy, hlog, placeExp]
    push_cast
    rcases le_or_gt 0 (log (Valued.v y)) with hm | hm
    · rw [max_eq_right (one_le_zpow₀ hq1 hm), ← zpow_natCast, Int.toNat_of_nonneg hm]
    · rw [max_eq_left (zpow_le_one_of_nonpos₀ hq1 hm.le), Int.toNat_eq_zero.mpr hm.le, pow_zero]

end Local
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section IdealExp

variable (v : HeightOneSpectrum (𝓞 F))

end IdealExp
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section Global

variable (x : FiniteAdeleRing (𝓞 F) F)

private theorem finite_setOf_not_mem :
    {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.mp x.2

private def badSet : Finset (HeightOneSpectrum (𝓞 F)) := (finite_setOf_not_mem x).toFinset

private theorem mem_badSet_iff (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ badSet x ↔ x v ∉ v.adicCompletionIntegers F := by
  rw [badSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

private theorem placeExp_eq_zero_of_not_mem_badSet {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badSet x) :
    placeExp v (x v) = 0 :=
  placeExp_eq_zero_of_mem v (by rwa [mem_badSet_iff, not_not] at hv)

private theorem mulSupport_max_one_norm_subset :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖x v‖) ⊆ ↑(badSet x) := by
  intro v hv
  rw [Function.mem_mulSupport] at hv
  rw [Finset.mem_coe]
  by_contra hvS
  exact hv (by rw [max_one_norm, placeExp_eq_zero_of_not_mem_badSet x hvS, pow_zero])

private theorem hasFiniteMulSupport_max_one_norm :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => max 1 ‖x v‖).Finite :=
  (badSet x).finite_toSet.subset (mulSupport_max_one_norm_subset x)

end Global
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end BigCellExpansion.FiniteShell
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

end FiniteShell
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section FlatValue
p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicLevel"

open NumberField.InfinitePlace IsDedekindDomain AutomorphicForm BigCellExpansion.Height BigCellExpansion.CellFactor

open scoped NNReal

namespace BigCellExpansion
namespace FlatValue

variable (F : Type) [Field F] [NumberField F]

private theorem finprod_max_cpow_eq (s : ℂ) (z : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :
    ((BigCellExpansion.CellFactor.finCellFactor F z : ℝ) : ℂ) ^ (s + 1 / 2)
      = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          ((max 1 ‖z v‖ : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hsupp := BigCellExpansion.FiniteShell.hasFiniteMulSupport_max_one_norm (F := F) z
  rw [BigCellExpansion.CellFactor.finCellFactor_cpow_eq s z hsupp]

  have h1 : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), max 1 ‖z v‖ : ℝ)
      = ∏ v ∈ hsupp.toFinset, max 1 ‖z v‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hsupp.mem_toFinset.mpr hv)
  have h2 : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        ((max 1 ‖z v‖ : ℝ) : ℂ) ^ (-(2 * s + 1)))
      = ∏ v ∈ hsupp.toFinset, ((max 1 ‖z v‖ : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
    refine finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hsupp.mem_toFinset.mpr ?_)
    intro h0
    apply hv
    simp only [Function.mem_mulSupport] at *
    rw [h0]
    simp
  rw [h1, h2]
  exact BigCellExpansion.ArchFactor.prod_cpow_ofReal_nonneg hsupp.toFinset _
    (fun v _ => le_trans zero_le_one (le_max_left _ _)) _

omit [NumberField F] in

private theorem Φ_snd_apply (y : NumberField.InfiniteAdeleRing F)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (BigCellExpansion.ArchFactor.Φ F y).2 w = Completion.extensionEmbedding w.1 (y w.1) := by
  have h := BigCellExpansion.ArchFactor.Φ_snd_sigmaC F y ((BigCellExpansion.ArchFactor.sigmaC F).symm w)
  rwa [Equiv.apply_symm_apply] at h

open scoped Classical in

private theorem flatOne_bigCell_eq (s : ℂ) (x : AdeleRing (𝓞 F) F) :
    flatOne F s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
      = (∏ i : {w : InfinitePlace F // w.IsReal},
          (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
            ^ (-(s + 1 / 2)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
            (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
              ^ (-(2 * s + 1)))
        * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
            ((max 1 ‖x.2 v‖ : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hreal : (∏ i : {w : InfinitePlace F // InfinitePlace.IsReal w},
        (((1 + (BigCellExpansion.ArchFactor.Φ F x.1).1 i ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)))
      = ∏ i : {w : InfinitePlace F // w.IsReal},
          (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
            ^ (-(s + 1 / 2)) :=
    Finset.prod_congr rfl fun i _ => by rw [BigCellExpansion.ArchFactor.Φ_fst]
  have hcplx : (∏ w : {w : InfinitePlace F // InfinitePlace.IsComplex w},
        (((1 + ‖(BigCellExpansion.ArchFactor.Φ F x.1).2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1)))
      = ∏ w : {w : InfinitePlace F // w.IsComplex},
          (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
            ^ (-(2 * s + 1)) :=
    Finset.prod_congr rfl fun w _ => by rw [Φ_snd_apply]
  rw [BigCellExpansion.CellFactor.flatOne_weyl_unipotent s x,
    BigCellExpansion.ArchFactor.arch_integrand_eq F s x.1, finprod_max_cpow_eq F s x.2]
  unfold BigCellExpansion.ArchFactor.gMix
  rw [hreal, hcplx]

end BigCellExpansion.FlatValue
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
end FlatValue
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

namespace BigCellExpansion
namespace LevelExpansion

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicLevel"
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

variable {G : Type*} [Mul G]

private def RightInvariantOn (S : Set G) (f : G → ℂ) : Prop :=
  ∀ g : G, ∀ k ∈ S, f (g * k) = f g

variable (F : Type) [Field F] [NumberField F]

private def congrSet (n : ℕ) : Set (AdelicGL2 (𝓞 F) F) :=
  {u | glArch (𝓞 F) F u = 1 ∧ ∀ i j : Fin 2,
    (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
      idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) ∧
    (((glFin (𝓞 F) F u)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
      idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)})}

private theorem idealBound_span_singleton {r : 𝓞 F} (hr : r ≠ 0) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (Ideal.span {r}) v = v.intValuation r := by
  rw [idealBound_of_ne_bot (by rwa [Ne, Ideal.span_singleton_eq_bot]) v, v.intValuation_if_neg hr]

private theorem idealBall_span_mul_subset {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) :
    idealBall (𝓞 F) F (Ideal.span {a * b}) ⊆ idealBall (𝓞 F) F (Ideal.span {a}) := by
  intro x hx v
  have h := hx v
  rw [idealBound_span_singleton F (mul_ne_zero ha hb)] at h
  rw [idealBound_span_singleton F ha]
  refine h.trans ?_
  rw [map_mul]
  exact mul_le_of_le_one_right' (v.intValuation_le_one b)

private theorem eq_zero_of_forall_mem_idealBall (x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hx : ∀ m : ℕ, m ≠ 0 → x ∈ idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)})) : x = 0 := by
  refine IsDedekindDomain.FiniteAdeleRing.ext F fun v => ?_
  rw [coe_zero_apply]
  by_contra h0
  have hv0 : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
  set e : ℤ := WithZero.log (Valued.v (x v)) with he_def
  have he : Valued.v (x v) = WithZero.exp e := (WithZero.exp_log hv0).symm
  set M : ℕ := Ideal.absNorm v.asIdeal ^ (e.natAbs + 1) with hM_def
  have hM0 : M ≠ 0 :=
    pow_ne_zero _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hmem : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal ^ (e.natAbs + 1) := by
    rw [hM_def, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) _
  have h1 : Valued.v (x v) ≤ v.intValuation ((M : ℕ) : 𝓞 F) := by
    rw [← idealBound_span_singleton F (Nat.cast_ne_zero.mpr hM0) v]
    exact hx M hM0 v
  have h2 : v.intValuation ((M : ℕ) : 𝓞 F) ≤ WithZero.exp (-((e.natAbs + 1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ _).mpr hmem
  have h3 := (he ▸ h1).trans h2
  rw [WithZero.exp_le_exp] at h3
  omega

private theorem exists_idealBall_subset {O : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)} (hO : IsOpen O)
    (h0 : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ O) :
    ∃ m : ℕ, m ≠ 0 ∧ idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)}) ⊆ O := by
  have hS := isCompact_integralFiniteAdeles (𝓞 F) F
  let t : ℕ → Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := fun k =>
    idealBall (𝓞 F) F (Ideal.span {((k + 1 : ℕ) : 𝓞 F)}) ∩ Oᶜ
  have htc : ∀ k, IsClosed (t k) := fun k =>
    (isClosed_idealBall (𝓞 F) F _).inter hO.isClosed_compl
  have hst : integralFiniteAdeles (𝓞 F) F ∩ ⋂ k, t k = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxI := Set.mem_iInter.mp hx.2
    have hx0 : x = 0 := by
      refine eq_zero_of_forall_mem_idealBall F x fun m hm => ?_
      have h := (hxI (m - 1)).1
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
    exact (hxI 0).2 (hx0 ▸ h0)
  obtain ⟨u, hu⟩ := hS.elim_finite_subfamily_closed t htc hst
  refine ⟨∏ k ∈ u, (k + 1), Finset.prod_ne_zero_iff.mpr fun k _ => Nat.succ_ne_zero k,
    fun x hx => ?_⟩
  by_contra hxO
  have hxall : x ∈ integralFiniteAdeles (𝓞 F) F ∩ ⋂ k ∈ u, t k := by
    refine ⟨idealBall_subset_integralFiniteAdeles _ hx, Set.mem_iInter₂.mpr fun k hk => ⟨?_, hxO⟩⟩
    have hsplit : (∏ i ∈ u, (i + 1) : ℕ) = (k + 1) * ∏ i ∈ u.erase k, (i + 1) :=
      (Finset.mul_prod_erase u (fun i => i + 1) hk).symm
    rw [hsplit, Nat.cast_mul] at hx
    exact idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.succ_ne_zero i)) hx
  rw [hu] at hxall
  exact hxall

private noncomputable def liftFin (X : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, X i j)

private theorem _root_.BigCellExpansion.LevelExpansion.one_apply_eq (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) := by
  rw [Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

p2m_export "BigCellExpansion.LevelExpansion" "one_apply_eq"
private theorem coe_eq_liftFin {u : AdelicGL2 (𝓞 F) F} (hu : glArch (𝓞 F) F u = 1) :
    (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      liftFin F (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · show ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
    rw [← glArch_apply, hu, Units.val_one]
  · rfl

private theorem exists_forall_liftFin_mem {W : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))}
    (hW : IsOpen W) (h1 : (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ∈ W) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ X : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      (∀ i j, X i j - (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
        idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)})) → liftFin F X ∈ W := by
  obtain ⟨r, hr, hrW⟩ := isOpen_pi_iff'.mp hW _ h1
  have hc : ∀ i, ∃ c : Fin 2 → Set (AdeleRing (𝓞 F) F),
      (∀ j, IsOpen (c j) ∧ (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j ∈ c j) ∧
        Set.univ.pi c ⊆ r i := fun i => isOpen_pi_iff'.mp (hr i).1 _ (hr i).2
  choose c hc hcr using hc
  have hAB : ∀ i j, ∃ A : Set (InfiniteAdeleRing F), ∃ B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      IsOpen A ∧ IsOpen B ∧ (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j ∈ A ∧
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈ B ∧ A ×ˢ B ⊆ c i j := by
    intro i j
    have h := (hc i j).2
    rw [one_apply_eq] at h
    exact isOpen_prod_iff.mp (hc i j).1 _ _ h
  choose A B hA hB hA1 hB1 hABc using hAB
  let T : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    ⋂ i, ⋂ j, (fun y => (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j + y) ⁻¹' B i j
  have hT : IsOpen T :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hB i j).preimage (continuous_const.add continuous_id)
  have hT0 : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ T := by
    refine Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j => ?_
    show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j + 0 ∈ B i j
    rw [add_zero]
    exact hB1 i j
  obtain ⟨m, hm, hmT⟩ := exists_idealBall_subset F hT hT0
  refine ⟨m, hm, fun X hX => hrW (Set.mem_univ_pi.mpr fun i => hcr i (Set.mem_univ_pi.mpr fun j => ?_))⟩
  refine hABc i j (Set.mk_mem_prod (hA1 i j) ?_)
  have h := Set.mem_iInter.mp (Set.mem_iInter.mp (hmT (hX i j)) i) j
  have h' : (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j +
      (X i j - (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ∈ B i j := h
  rwa [add_sub_cancel] at h'

private theorem exists_congrSet_subset {V : Set (AdelicGL2 (𝓞 F) F)} (hV : IsOpen V)
    (h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ V) : ∃ n : ℕ, congrSet F n ⊆ V := by
  obtain ⟨O, hO, hOV⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have h1O : Units.embedProduct _ (1 : AdelicGL2 (𝓞 F) F) ∈ O := by
    rw [← Set.mem_preimage, hOV]
    exact h1
  rw [map_one, Prod.one_eq_mk] at h1O
  obtain ⟨O₁, O₂, hO₁, hO₂, h1O₁, h1O₂, hprod⟩ := isOpen_prod_iff.mp hO _ _ h1O
  obtain ⟨m₁, hm₁, hW₁⟩ := exists_forall_liftFin_mem F hO₁ h1O₁
  obtain ⟨m₂, hm₂, hW₂⟩ := exists_forall_liftFin_mem F (hO₂.preimage MulOpposite.continuous_op)
    (by rw [Set.mem_preimage, MulOpposite.op_one]; exact h1O₂)
  refine ⟨m₁ * m₂ - 1, fun u hu => ?_⟩
  have hn : m₁ * m₂ - 1 + 1 = m₁ * m₂ :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hm₁ hm₂))
  obtain ⟨harch, hent⟩ := hu
  simp only [hn, Nat.cast_mul] at hent
  have harch' : glArch (𝓞 F) F u⁻¹ = 1 := by rw [map_inv, harch, inv_one]
  have hval : (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ∈ O₁ := by
    rw [coe_eq_liftFin F harch]
    exact hW₁ _ fun i j => idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr hm₁)
      (Nat.cast_ne_zero.mpr hm₂) (hent i j).1
  have hinv : MulOpposite.op ((u⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2)
      (AdeleRing (𝓞 F) F)) ∈ O₂ := by
    have h := hW₂ _ fun i j => idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr hm₂)
      (Nat.cast_ne_zero.mpr hm₁) (mul_comm (m₁ : 𝓞 F) (m₂ : 𝓞 F) ▸ (hent i j).2)
    rw [Set.mem_preimage, ← map_inv, ← coe_eq_liftFin F harch'] at h
    exact h
  rw [← hOV, Set.mem_preimage, Units.embedProduct_apply]
  exact hprod (Set.mk_mem_prod hval hinv)

private theorem exists_rightInvariantOn_congrSet_of_isKfSmooth (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsKfSmooth F f) : ∃ n : ℕ, RightInvariantOn (congrSet F n) f := by
  have hopen : IsOpen ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F))
      (FLT.SmoothVectors.RightTranslationFn.mk f :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (↥(finiteAdelicGL2Subgroup F))) : Set (↥(finiteAdelicGL2Subgroup F))) := hf
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ V := by
    have h : (1 : ↥(finiteAdelicGL2Subgroup F)) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact Subgroup.one_mem _
    exact h
  obtain ⟨n, hn⟩ := exists_congrSet_subset F hV h1
  refine ⟨n, fun g k hk => ?_⟩
  have hkK : k ∈ finiteAdelicGL2Subgroup F := (mem_finiteAdelicGL2Subgroup_iff F k).mpr hk.1
  have hst : (⟨k, hkK⟩ : ↥(finiteAdelicGL2Subgroup F)) ∈
      ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F))
        (FLT.SmoothVectors.RightTranslationFn.mk f :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
          Subgroup (↥(finiteAdelicGL2Subgroup F))) : Set (↥(finiteAdelicGL2Subgroup F))) := by
    rw [← hVeq]; exact hn hk
  have heq := MulAction.mem_stabilizer_iff.mp (SetLike.mem_coe.mp hst)
  exact congrArg (fun φ => FLT.SmoothVectors.RightTranslationFn.toFun φ g) heq

private theorem span_natSucc_ne_bot (n : ℕ) :
    Ideal.span {((n + 1 : ℕ) : 𝓞 F)} ≠ (⊥ : Ideal (𝓞 F)) :=
  Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))

private noncomputable def levelPlaces (n : ℕ) : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  (finite_setOf_idealBound_ne_one (span_natSucc_ne_bot F n)).toFinset

private theorem mem_levelPlaces_iff (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    v ∈ levelPlaces F n ↔ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v ≠ 1 := by
  simp only [levelPlaces, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

private theorem idealBound_eq_one_of_notMem_levelPlaces {n : ℕ}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hv : v ∉ levelPlaces F n) :
    idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v = 1 := by
  by_contra h
  exact hv ((mem_levelPlaces_iff F n v).2 h)

private theorem exists_forall_exp_neg_le_idealBound (n : ℕ) :
    ∃ m : ℕ, ∀ v ∈ levelPlaces F n,
      WithZero.exp (-(m : ℤ)) ≤ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v := by
  have h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ c : ℕ,
      WithZero.exp (-(c : ℤ)) ≤ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v := by
    intro v
    rw [idealBound_of_ne_bot (span_natSucc_ne_bot F n)]
    exact ⟨_, le_rfl⟩
  choose c hc using h
  refine ⟨(levelPlaces F n).sup c, fun v hv => ?_⟩
  refine le_trans ?_ (hc v)
  rw [WithZero.exp_le_exp]
  have := Finset.le_sup (f := c) hv
  omega

open BigCellExpansion.Iwasawa

section Cells

variable {F}
variable (m : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

private def levelSetoid : Setoid (v.adicCompletionIntegers F) where
  r a b := Valued.v ((a : v.adicCompletion F) - b) ≤ WithZero.exp (-(m : ℤ))
  iseqv := by
    refine ⟨fun a => ?_, fun {a b} h => ?_, fun {a b c} hab hbc => ?_⟩
    · rw [sub_self, map_zero]
      exact zero_le'
    · rwa [Valuation.map_sub_swap]
    · have h := Valuation.map_sub Valued.v ((a : v.adicCompletion F) - b) ((c : v.adicCompletion F) - b)
      rw [sub_sub_sub_cancel_right, Valuation.map_sub_swap _ (c : v.adicCompletion F)] at h
      exact h.trans (max_le hab hbc)

private def LevelClass : Type := Quotient (levelSetoid m v)

private theorem finite_levelClass : Finite (LevelClass m v) := by
  obtain ⟨t, ht0, hvt⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := F) v m
  have hcpt : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F v)
  let U : v.adicCompletionIntegers F → Set (v.adicCompletion F) := fun a =>
    {y | Valued.v (y - a) ≤ Valued.v t}
  have hU : ∀ a, IsOpen (U a) := fun a =>
    (NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht0).preimage (continuous_id.sub continuous_const)
  have hcov : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ⊆ ⋃ a, U a := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show Valued.v (y - y) ≤ Valued.v t
    rw [sub_self, map_zero]
    exact zero_le'
  obtain ⟨s, hs⟩ := hcpt.elim_finite_subcover U hU hcov
  refine Finite.of_surjective (fun a : s => (Quotient.mk (levelSetoid m v) a.1 : LevelClass m v)) ?_
  intro q
  induction q using Quotient.inductionOn with
  | h b =>
    obtain ⟨a, ha, hba⟩ := Set.mem_iUnion₂.1 (hs b.2)
    refine ⟨⟨a, ha⟩, Quotient.sound ?_⟩
    show Valued.v ((a : v.adicCompletion F) - b) ≤ WithZero.exp (-(m : ℤ))
    rw [Valuation.map_sub_swap, ← hvt]
    exact hba

open scoped Classical in

private def cellAt (y : v.adicCompletion F) : LevelClass m v ⊕ LevelClass m v :=
  if h : y ∈ v.adicCompletionIntegers F then Sum.inl (Quotient.mk (levelSetoid m v) ⟨y, h⟩)
  else Sum.inr (Quotient.mk (levelSetoid m v)
    ⟨y⁻¹, ((v.adicCompletionIntegers F).mem_or_inv_mem y).resolve_left h⟩)

open scoped Classical in

private def cellA (c : LevelClass m v ⊕ LevelClass m v) (y : v.adicCompletion F) : ℂ :=
  if h : y ∈ v.adicCompletionIntegers F then
    (if Sum.inl (Quotient.mk (levelSetoid m v) ⟨y, h⟩) = c then 1 else 0) else 0

open scoped Classical in

private def cellB (c : LevelClass m v ⊕ LevelClass m v) (z : v.adicCompletion F) : ℂ :=
  if h : z ∈ v.adicCompletionIntegers F then
    (if Sum.inr (Quotient.mk (levelSetoid m v) ⟨z, h⟩) = c then 1 else 0) else 0

private theorem cellA_congr (c : LevelClass m v ⊕ LevelClass m v) {x y : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) (hy : y ∈ v.adicCompletionIntegers F)
    (hxy : Valued.v (y - x) ≤ WithZero.exp (-(m : ℤ))) : cellA m v c y = cellA m v c x := by
  have hq : (Sum.inl (Quotient.mk (levelSetoid m v) ⟨y, hy⟩) : LevelClass m v ⊕ LevelClass m v)
      = Sum.inl (Quotient.mk (levelSetoid m v) ⟨x, hx⟩) := congrArg Sum.inl (Quotient.sound hxy)
  simp only [cellA, dif_pos hx, dif_pos hy]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hq.symm.trans h1) h2
  · exact absurd (hq.trans h2) h1
  · rfl

private theorem mem_of_valued_sub_le (hm : 1 ≤ m) {x y : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) (hxy : Valued.v (y - x) ≤ WithZero.exp (-(m : ℤ))) :
    y ∈ v.adicCompletionIntegers F := by
  have hd : y - x ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    refine hxy.trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  simpa using add_mem hd hx

private theorem cellB_congr (hm : 1 ≤ m) (c : LevelClass m v ⊕ LevelClass m v) {x y : v.adicCompletion F}
    (hxy : Valued.v (y - x) ≤ WithZero.exp (-(m : ℤ))) : cellB m v c y = cellB m v c x := by
  by_cases hx : x ∈ v.adicCompletionIntegers F
  · have hy : y ∈ v.adicCompletionIntegers F := mem_of_valued_sub_le m v hm hx hxy
    have hq : (Sum.inr (Quotient.mk (levelSetoid m v) ⟨y, hy⟩) : LevelClass m v ⊕ LevelClass m v)
        = Sum.inr (Quotient.mk (levelSetoid m v) ⟨x, hx⟩) := congrArg Sum.inr (Quotient.sound hxy)
    simp only [cellB, dif_pos hx, dif_pos hy]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hq.symm.trans h1) h2
    · exact absurd (hq.trans h2) h1
    · rfl
  · have hy : y ∉ v.adicCompletionIntegers F := fun hy =>
      hx (mem_of_valued_sub_le m v hm hy (by rwa [Valuation.map_sub_swap]))
    simp only [cellB, dif_neg hx, dif_neg hy]

open scoped Classical in

private theorem indicator_cellA_add_indicator_cellB (c : LevelClass m v ⊕ LevelClass m v)
    (y : v.adicCompletion F) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (cellA m v c) y
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun z => cellB m v c z⁻¹) y
      = if cellAt m v y = c then 1 else 0 := by
  by_cases h : y ∈ v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (fun h' => (h' : y ∉ _) h), add_zero]
    simp only [cellA, cellAt, dif_pos h]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  · have hinv : y⁻¹ ∈ v.adicCompletionIntegers F := ((v.adicCompletionIntegers F).mem_or_inv_mem y).resolve_left h
    rw [Set.indicator_of_notMem h,
      Set.indicator_of_mem (show y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ from h), zero_add]
    simp only [cellB, cellAt, dif_pos hinv, dif_neg h]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl

private theorem valued_locKinv_mul_locK_sub_one_le {xf xf' : FiniteAdeleRing (𝓞 F) F}
    (h : cellAt m v (xf v) = cellAt m v (xf' v)) (i j : Fin 2) :
    Valued.v ((locKinv xf' v * locK xf v) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j)
      ≤ WithZero.exp (-(m : ℤ)) := by
  unfold cellAt at h
  by_cases hx : xf v ∈ v.adicCompletionIntegers F <;> by_cases hx' : xf' v ∈ v.adicCompletionIntegers F
  · rw [dif_pos hx, dif_pos hx'] at h
    have hd : Valued.v (xf v - xf' v) ≤ WithZero.exp (-(m : ℤ)) := Quotient.exact (Sum.inl.inj h)
    unfold locK locKinv
    rw [if_pos hx, if_pos hx']
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm] using hd
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  · rw [dif_pos hx, dif_neg hx'] at h
    exact absurd h Sum.inl_ne_inr
  · rw [dif_neg hx, dif_pos hx'] at h
    exact absurd h Sum.inr_ne_inl
  · rw [dif_neg hx, dif_neg hx'] at h
    have hd : Valued.v ((xf v)⁻¹ - (xf' v)⁻¹) ≤ WithZero.exp (-(m : ℤ)) := Quotient.exact (Sum.inr.inj h)
    unfold locK locKinv
    rw [if_neg hx, if_neg hx']
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm] using hd
    · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem valued_locKinv_mul_locK_sub_one_le_one (xf xf' : FiniteAdeleRing (𝓞 F) F) (i j : Fin 2) :
    Valued.v ((locKinv xf' v * locK xf v) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1 := by
  rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  refine sub_mem ?_ ?_
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (locKinv_mem xf' v i k) (locK_mem xf v k j)
  · rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end Cells
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

section Expansion

variable {F}
variable (n m : ℕ)

private theorem entry_mem_idealBall
    (hm : ∀ v ∈ levelPlaces F n,
      WithZero.exp (-(m : ℤ)) ≤ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v)
    {xf xf' : FiniteAdeleRing (𝓞 F) F}
    (hc : ∀ v ∈ levelPlaces F n, cellAt m v (xf v) = cellAt m v (xf' v)) (i j : Fin 2) :
    (kffInv xf' * kffVal xf) i j - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      ∈ idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) := by
  intro v
  have hev : ((kffInv xf' * kffVal xf) i j - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) v
      = (locKinv xf' v * locK xf v) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j := by
    rw [coe_sub_apply, finAdeleEval_matrix_entry F v, finAdeleEval_matrix_entry F v, map_mul, eval_kffVal,
      eval_kffInv, map_one]
  rw [hev]
  by_cases hv : v ∈ levelPlaces F n
  · exact (valued_locKinv_mul_locK_sub_one_le m v (hc v hv) i j).trans (hm v hv)
  · rw [idealBound_eq_one_of_notMem_levelPlaces F hv]
    exact valued_locKinv_mul_locK_sub_one_le_one v xf xf' i j

private theorem inv_mul_mem_congrSet
    (hm : ∀ v ∈ levelPlaces F n,
      WithZero.exp (-(m : ℤ)) ≤ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v)
    {k k' : AdelicGL2 (𝓞 F) F} {xf xf' : FiniteAdeleRing (𝓞 F) F}
    (hk : glArch (𝓞 F) F k = 1) (hk' : glArch (𝓞 F) F k' = 1)
    (hf : glFin (𝓞 F) F k = kff xf) (hf' : glFin (𝓞 F) F k' = kff xf')
    (hc : ∀ v ∈ levelPlaces F n, cellAt m v (xf v) = cellAt m v (xf' v)) :
    k'⁻¹ * k ∈ congrSet F n := by
  refine ⟨by rw [map_mul, map_inv, hk, hk', inv_one, one_mul], fun i j => ⟨?_, ?_⟩⟩
  · have h1 : ((glFin (𝓞 F) F (k'⁻¹ * k) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = kffInv xf' * kffVal xf := by
      rw [map_mul, map_inv, hf, hf', Units.val_mul, kff_inv_coe, kff_coe]
    rw [h1]
    exact entry_mem_idealBall n m hm hc i j
  · have h2 : (((glFin (𝓞 F) F (k'⁻¹ * k))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = kffInv xf * kffVal xf' := by
      rw [map_mul, map_inv, hf, hf', mul_inv_rev, inv_inv, Units.val_mul, kff_inv_coe, kff_coe]
    rw [h2]
    exact entry_mem_idealBall n m hm (fun v hv => (hc v hv).symm) i j

private theorem apply_eq_of_cellAt_eq {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : RightInvariantOn (congrSet F n) ψ)
    (hm : ∀ v ∈ levelPlaces F n,
      WithZero.exp (-(m : ℤ)) ≤ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v)
    {k k' : AdelicGL2 (𝓞 F) F} {xf xf' : FiniteAdeleRing (𝓞 F) F}
    (hk : glArch (𝓞 F) F k = 1) (hk' : glArch (𝓞 F) F k' = 1)
    (hf : glFin (𝓞 F) F k = kff xf) (hf' : glFin (𝓞 F) F k' = kff xf')
    (hc : ∀ v ∈ levelPlaces F n, cellAt m v (xf v) = cellAt m v (xf' v)) : ψ k = ψ k' := by
  have h := hψ k' _ (inv_mul_mem_congrSet n m hm hk hk' hf hf' hc)
  rwa [mul_inv_cancel_left] at h

private def Cell : Type :=
  (w : {v // v ∈ levelPlaces F n}) → (LevelClass m w.1 ⊕ LevelClass m w.1)

private theorem finite_cell : Finite (Cell (F := F) n m) := by
  haveI : ∀ w : {v // v ∈ levelPlaces F n}, Finite (LevelClass m w.1) := fun w => finite_levelClass m w.1
  exact Pi.finite

private def cellOf (xf : FiniteAdeleRing (𝓞 F) F) : Cell (F := F) n m := fun w => cellAt m w.1 (xf w.1)

open scoped Classical in

private noncomputable def cellDataA (γ : Cell (F := F) n m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) : ℂ :=
  if hv : v ∈ levelPlaces F n then cellA m v (γ ⟨v, hv⟩) y else 0

open scoped Classical in

private noncomputable def cellDataB (γ : Cell (F := F) n m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (z : v.adicCompletion F) : ℂ :=
  if hv : v ∈ levelPlaces F n then cellB m v (γ ⟨v, hv⟩) z else 0

private theorem cellDataA_of_mem (γ : Cell (F := F) n m) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ levelPlaces F n) : cellDataA n m γ v = cellA m v (γ ⟨v, hv⟩) := by
  ext y
  simp only [cellDataA, dif_pos hv]

private theorem cellDataB_of_mem (γ : Cell (F := F) n m) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ levelPlaces F n) : cellDataB n m γ v = cellB m v (γ ⟨v, hv⟩) := by
  ext z
  simp only [cellDataB, dif_pos hv]

open scoped Classical in

private theorem prod_factor_eq (γ : Cell (F := F) n m) (xf : FiniteAdeleRing (𝓞 F) F) :
    (∏ v ∈ levelPlaces F n,
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (cellDataA n m γ v) (xf v)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => cellDataB n m γ v y⁻¹) (xf v)))
      = if cellOf n m xf = γ then 1 else 0 := by
  rw [← Finset.prod_attach]
  have hfac : ∀ w : {v // v ∈ levelPlaces F n},
      ((w.1.adicCompletionIntegers F : Set (w.1.adicCompletion F)).indicator (cellDataA n m γ w.1) (xf w.1)
          + (w.1.adicCompletionIntegers F : Set (w.1.adicCompletion F))ᶜ.indicator
              (fun y => cellDataB n m γ w.1 y⁻¹) (xf w.1))
        = if cellAt m w.1 (xf w.1) = γ w then 1 else 0 := by
    intro w
    rw [cellDataA_of_mem n m γ w.2, cellDataB_of_mem n m γ w.2]
    exact indicator_cellA_add_indicator_cellB m w.1 (γ w) (xf w.1)
  rw [Finset.prod_congr rfl fun w _ => hfac w, Finset.prod_boole]
  have hiff : (∀ w ∈ (levelPlaces F n).attach, cellAt m w.1 (xf w.1) = γ w) ↔ cellOf n m xf = γ := by
    simp only [Finset.mem_attach, true_implies]
    exact funext_iff.symm
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

end Expansion
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

private theorem exists_finset_sum_prod_eq_of_isKfSmooth (F : Type) [Field F] [NumberField F]
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (_hψ : IsKfSmooth F ψ) :
    ∃ (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (m : ℕ), 1 ≤ m ∧
      ∃ (N : ℕ) (d : Fin N → ℂ)
        (A B : Fin N → (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        (∀ (γ : Fin N), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
            Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A γ v y = A γ v x) ∧
        (∀ (γ : Fin N), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
            Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B γ v y = B γ v x) ∧
        ∀ (k : AdelicGL2 (𝓞 F) F) (xf : FiniteAdeleRing (𝓞 F) F),
          glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k = BigCellExpansion.Iwasawa.kff xf →
            ψ k = ∑ γ : Fin N, d γ
              * ∏ v ∈ S,
                  ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A γ v) (xf v)
                    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                        (fun y => B γ v y⁻¹) (xf v)) := by
  classical
  obtain ⟨n, hn⟩ := exists_rightInvariantOn_congrSet_of_isKfSmooth F ψ _hψ
  obtain ⟨m₀, hm₀⟩ := exists_forall_exp_neg_le_idealBound F n
  have hm : ∀ v ∈ levelPlaces F n,
      WithZero.exp (-((m₀ + 1 : ℕ) : ℤ)) ≤ idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v := by
    intro v hv
    refine le_trans ?_ (hm₀ v hv)
    rw [WithZero.exp_le_exp]
    omega
  haveI : Finite (Cell (F := F) n (m₀ + 1)) := finite_cell n (m₀ + 1)
  letI : Fintype (Cell (F := F) n (m₀ + 1)) := Fintype.ofFinite _
  let e := Fintype.equivFin (Cell (F := F) n (m₀ + 1))
  let dC : Cell (F := F) n (m₀ + 1) → ℂ := fun γ =>
    if h : ∃ p : AdelicGL2 (𝓞 F) F × FiniteAdeleRing (𝓞 F) F,
        glArch (𝓞 F) F p.1 = 1 ∧ glFin (𝓞 F) F p.1 = BigCellExpansion.Iwasawa.kff p.2 ∧ cellOf n (m₀ + 1) p.2 = γ
    then ψ h.choose.1 else 0
  refine ⟨levelPlaces F n, m₀ + 1, Nat.le_add_left 1 m₀, Fintype.card (Cell (F := F) n (m₀ + 1)),
    fun i => dC (e.symm i), fun i => cellDataA n (m₀ + 1) (e.symm i), fun i => cellDataB n (m₀ + 1) (e.symm i),
    ?_, ?_, ?_⟩
  · intro i v hv x hx y hy hxy
    simp only [cellDataA, dif_pos hv]
    exact cellA_congr (m₀ + 1) v _ hx hy hxy
  · intro i v hv x y hxy
    simp only [cellDataB, dif_pos hv]
    exact cellB_congr (m₀ + 1) v (Nat.le_add_left 1 m₀) _ hxy
  · intro k xf hk hf
    rw [Fintype.sum_equiv e.symm _ (fun γ => dC γ * ∏ v ∈ levelPlaces F n,
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (cellDataA n (m₀ + 1) γ v) (xf v)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => cellDataB n (m₀ + 1) γ v y⁻¹) (xf v))) (fun _ => rfl)]
    simp only [prod_factor_eq, mul_boole]
    rw [Fintype.sum_ite_eq]
    have hex : ∃ p : AdelicGL2 (𝓞 F) F × FiniteAdeleRing (𝓞 F) F,
        glArch (𝓞 F) F p.1 = 1 ∧ glFin (𝓞 F) F p.1 = BigCellExpansion.Iwasawa.kff p.2
          ∧ cellOf n (m₀ + 1) p.2 = cellOf n (m₀ + 1) xf := ⟨(k, xf), hk, hf, rfl⟩
    show ψ k = dite _ _ _
    rw [dif_pos hex]
    obtain ⟨hk₀, hf₀, hc₀⟩ := hex.choose_spec
    exact apply_eq_of_cellAt_eq n (m₀ + 1) hn hm hk hk₀ hf hf₀
      fun v hv => (congrFun hc₀ ⟨v, hv⟩).symm

end BigCellExpansion.LevelExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

namespace BigCellExpansion
namespace QuotientChar

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicLevel"
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm
open scoped NNReal

private noncomputable def unitIdele (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v u)

private theorem localChar_eq_apply_unitIdele (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    NumberField.TateGlobal.localChar χ v u = χ (unitIdele F v u) := rfl

private theorem val_unitIdele_fst (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl

private theorem val_unitIdele_snd (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
      = ((localUnit (𝓞 F) F v u : (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)ˣ) :
          IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := rfl

private theorem adele_one_fst (F : Type) [Field F] [NumberField F] : (1 : AdeleRing (𝓞 F) F).1 = 1 :=
  map_one (adeleArch (𝓞 F) F)

private theorem adele_zero_fst (F : Type) [Field F] [NumberField F] : (0 : AdeleRing (𝓞 F) F).1 = 0 :=
  map_zero (adeleArch (𝓞 F) F)

private theorem adele_one_snd (F : Type) [Field F] [NumberField F] : (1 : AdeleRing (𝓞 F) F).2 = 1 :=
  map_one (adeleFin (𝓞 F) F)

private theorem adele_zero_snd (F : Type) [Field F] [NumberField F] : (0 : AdeleRing (𝓞 F) F).2 = 0 :=
  map_zero (adeleFin (𝓞 F) F)

private theorem unitIdele_inv (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    unitIdele F v u⁻¹ = (unitIdele F v u)⁻¹ := by
  simp only [unitIdele, map_inv]

private theorem localUnit_apply_mem_integers (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ((localUnit (𝓞 F) F v u : (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)ˣ) :
        IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F := by
  by_cases hw : w = v
  · rw [hw, localUnit_apply_self]
    exact hu.le
  · rw [localUnit_apply_of_ne (𝓞 F) F v u hw]
    exact one_mem _

private theorem valued_inv_eq_one (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

private theorem valued_inv_sub_one (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    Valued.v (((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1)
      = Valued.v ((u : v.adicCompletion F) - 1) := by
  have h : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1
      = ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * (1 - (u : v.adicCompletion F)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  rw [h, map_mul, valued_inv_eq_one F v hu, one_mul, Valuation.map_sub_swap]

private theorem ideleNorm_unitIdele (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    NumberField.TateGlobal.ideleNorm F (unitIdele F v u) = 1 := by
  refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles F
    (unitIdele F v u) rfl ?_
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [NumberField.AdeleRing.val_finitePartUnits]
    exact localUnit_apply_mem_integers F v hu w
  · rw [← map_inv, NumberField.AdeleRing.val_finitePartUnits, ← unitIdele_inv]
    exact localUnit_apply_mem_integers F v (valued_inv_eq_one F v hu) w

private theorem height_unitIdele (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits (unitIdele F v u) : ℝˣ) : ℝ) = 1 := by
  rw [MonoidHom.coe_toHomUnits]
  exact ideleNorm_unitIdele F v hu

private theorem val_mul_cpowChar (F : Type) [Field F] [NumberField F]
    (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) {x : (AdeleRing (𝓞 F) F)ˣ}
    (hx : ((α x : ℝˣ) : ℝ) = 1) :
    (((μ * cpowChar α hα s) x : ℂˣ) : ℂ) = ((μ x : ℂˣ) : ℂ) := by
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, hx, Complex.ofReal_one, Complex.one_cpow,
    mul_one]

private noncomputable def diagAt (F : Type) [Field F] [NumberField F] (k : Fin 2)
    (t : (AdeleRing (𝓞 F) F)ˣ) : AdelicGL2 (𝓞 F) F where
  val := Matrix.diagonal fun i => if i = k then (t : AdeleRing (𝓞 F) F) else 1
  inv := Matrix.diagonal fun i => if i = k then ((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp

private theorem coe_diagAt (F : Type) [Field F] [NumberField F] (k : Fin 2) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((diagAt F k t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal fun i => if i = k then (t : AdeleRing (𝓞 F) F) else 1 := rfl

private theorem diagAt_inv (F : Type) [Field F] [NumberField F] (k : Fin 2) (t : (AdeleRing (𝓞 F) F)ˣ) :
    (diagAt F k t)⁻¹ = diagAt F k t⁻¹ := by
  exact Units.ext rfl

private theorem diagAt_mem_adelicBorel (F : Type) [Field F] [NumberField F] (k : Fin 2)
    (t : (AdeleRing (𝓞 F) F)ˣ) : diagAt F k t ∈ adelicBorel (𝓞 F) F := by
  show (Matrix.diagonal (fun i => if i = k then (t : AdeleRing (𝓞 F) F) else 1) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem apply_diagAt_zero_mul (F : Type) [Field F] [NumberField F]
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ₀ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ₀) (t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ₀ (diagAt F 0 t * g) = ((χ₁ t : ℂˣ) : ℂ) * φ₀ g := by
  rw [hφ₀ (diagAt F 0 t) (diagAt_mem_adelicBorel F 0 t) g]
  have h1 : borelDiagFst (⟨diagAt F 0 t, diagAt_mem_adelicBorel F 0 t⟩ : ↥(adelicBorel (𝓞 F) F)) = t := by
    refine Units.ext ?_
    show ((diagAt F 0 t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0
      = (t : AdeleRing (𝓞 F) F)
    rw [coe_diagAt]
    simp
  have h2 : borelDiagSnd (⟨diagAt F 0 t, diagAt_mem_adelicBorel F 0 t⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
    refine Units.ext ?_
    show ((diagAt F 0 t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1
      = (1 : AdeleRing (𝓞 F) F)
    rw [coe_diagAt]
    simp
  rw [h1, h2, map_one, Units.val_one, mul_one]

private theorem apply_diagAt_one_mul (F : Type) [Field F] [NumberField F]
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ₀ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ₀) (t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ₀ (diagAt F 1 t * g) = ((χ₂ t : ℂˣ) : ℂ) * φ₀ g := by
  rw [hφ₀ (diagAt F 1 t) (diagAt_mem_adelicBorel F 1 t) g]
  have h1 : borelDiagFst (⟨diagAt F 1 t, diagAt_mem_adelicBorel F 1 t⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
    refine Units.ext ?_
    show ((diagAt F 1 t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0
      = (1 : AdeleRing (𝓞 F) F)
    rw [coe_diagAt]
    simp
  have h2 : borelDiagSnd (⟨diagAt F 1 t, diagAt_mem_adelicBorel F 1 t⟩ : ↥(adelicBorel (𝓞 F) F)) = t := by
    refine Units.ext ?_
    show ((diagAt F 1 t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1
      = (t : AdeleRing (𝓞 F) F)
    rw [coe_diagAt]
    simp
  rw [h1, h2, map_one, Units.val_one, one_mul]

private theorem glArch_conj_diagAt (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) (k : Fin 2)
    {t : (AdeleRing (𝓞 F) F)ˣ} (ht : ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1) :
    glArch (𝓞 F) F (g⁻¹ * diagAt F k t * g) = 1 := by
  have hD : glArch (𝓞 F) F (diagAt F k t) = 1 := by
    refine Units.ext ?_
    rw [Units.val_one]
    ext i j
    rw [glArch_apply, coe_diagAt]
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [ht, adele_one_fst, adele_zero_fst]
  rw [map_mul, map_mul, hD, mul_one, map_inv, inv_mul_cancel]

private noncomputable def conjEntry (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F)
    (k i j : Fin 2) : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F :=
  (((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i k
    * ((glFin (𝓞 F) F g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) k j

private theorem coe_glFin_diagAt (F : Type) [Field F] [NumberField F] (k : Fin 2) (t : (AdeleRing (𝓞 F) F)ˣ) :
    (glFin (𝓞 F) F (diagAt F k t) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
      = Matrix.diagonal fun i => if i = k then ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 else 1 := by
  ext i j
  rw [glFin_apply, coe_diagAt]
  simp only [Matrix.diagonal_apply]
  split_ifs <;> simp [adele_one_snd, adele_zero_snd]

private theorem glFin_conj_diagAt_sub_one (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F)
    (k : Fin 2) (t : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    (glFin (𝓞 F) F (g⁻¹ * diagAt F k t * g) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j
      = (((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 - 1) * conjEntry F g k i j := by
  have hL : ∀ (A B : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
      (a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      (A * Matrix.diagonal (fun i => if i = k then a else 1) * B) i j - (A * B) i j = (a - 1) * (A i k * B k j) := by
    intro A B a
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases k <;> simp <;> ring
  have hG : (((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
      * ((glFin (𝓞 F) F g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) = 1 := Units.inv_mul _
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, coe_glFin_diagAt, ← hG]
  exact hL _ _ _

private theorem exists_forall_mul_conj_mem_idealBall (F : Type) [Field F] [NumberField F] (n : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :
    ∃ c : ℕ, ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) →
        (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 - 1) * y
          ∈ idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, idealBound (𝓞 F) (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) v = WithZero.exp (-(e : ℤ)) :=
    ⟨_, idealBound_of_ne_bot (LevelExpansion.span_natSucc_ne_bot F n) v⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Valued.v (y v) ≤ WithZero.exp (m : ℤ) := by
    rcases eq_or_ne (Valued.v (y v)) 0 with h0 | h0
    · exact ⟨0, by rw [h0]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v (y v))).toNat, ?_⟩
      calc Valued.v (y v) = WithZero.exp (WithZero.log (Valued.v (y v))) := (WithZero.exp_log h0).symm
        _ ≤ WithZero.exp (((WithZero.log (Valued.v (y v))).toNat : ℤ)) := by
          rw [WithZero.exp_le_exp]
          exact Int.self_le_toNat _
  refine ⟨e + m, fun u hu w => ?_⟩
  rw [coe_mul_apply, coe_sub_apply, coe_one_apply, map_mul]
  by_cases hwv : w = v
  · rw [hwv]
    have hcomp : (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v = (u : v.adicCompletion F) := by
      rw [val_unitIdele_snd, localUnit_apply_self]
    rw [hcomp, he]
    calc Valued.v ((u : v.adicCompletion F) - 1) * Valued.v (y v)
        ≤ WithZero.exp (-((e + m : ℕ) : ℤ)) * WithZero.exp (m : ℤ) := mul_le_mul' hu hm
      _ = WithZero.exp (-(e : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  · have hcomp : (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) w = 1 := by
      rw [val_unitIdele_snd, localUnit_apply_of_ne (𝓞 F) F v u hwv]
    rw [hcomp, sub_self, map_zero, zero_mul]
    exact zero_le'

private theorem mul_conj_mem_idealBall_of_notMem (F : Type) [Field F] [NumberField F] {n : ℕ}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hv : v ∉ LevelExpansion.levelPlaces F n)
    {y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F} (hy : y v ∈ v.adicCompletionIntegers F)
    {u : (v.adicCompletion F)ˣ} (hu : Valued.v (u : v.adicCompletion F) = 1) :
    (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 - 1) * y
      ∈ idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) := by
  intro w
  rw [coe_mul_apply, coe_sub_apply, coe_one_apply, map_mul]
  by_cases hwv : w = v
  · rw [hwv]
    have hcomp : (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v = (u : v.adicCompletion F) := by
      rw [val_unitIdele_snd, localUnit_apply_self]
    rw [hcomp, LevelExpansion.idealBound_eq_one_of_notMem_levelPlaces F hv]
    have h1 : Valued.v ((u : v.adicCompletion F) - 1) ≤ 1 := by
      calc Valued.v ((u : v.adicCompletion F) - 1)
          ≤ max (Valued.v (u : v.adicCompletion F)) (Valued.v (1 : v.adicCompletion F)) :=
            Valuation.map_sub _ _ _
        _ = 1 := by rw [hu, map_one, max_self]
    exact mul_le_one' h1 hy
  · have hcomp : (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) w = 1 := by
      rw [val_unitIdele_snd, localUnit_apply_of_ne (𝓞 F) F v u hwv]
    rw [hcomp, sub_self, map_zero, zero_mul]
    exact zero_le'

private theorem conj_mem_congrSet (F : Type) [Field F] [NumberField F] (n : ℕ) (g : AdelicGL2 (𝓞 F) F)
    (k : Fin 2) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ)
    (h₁ : ∀ i j : Fin 2, (((unitIdele F v u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 - 1)
        * conjEntry F g k i j ∈ idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}))
    (h₂ : ∀ i j : Fin 2, (((unitIdele F v u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 - 1)
        * conjEntry F g k i j ∈ idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)})) :
    g⁻¹ * diagAt F k (unitIdele F v u) * g ∈ LevelExpansion.congrSet F n := by
  have hinv : (g⁻¹ * diagAt F k (unitIdele F v u) * g)⁻¹ = g⁻¹ * diagAt F k (unitIdele F v u⁻¹) * g := by
    rw [unitIdele_inv, ← diagAt_inv]
    group
  refine ⟨glArch_conj_diagAt F g k (val_unitIdele_fst F v u), fun i j => ⟨?_, ?_⟩⟩
  · rw [glFin_conj_diagAt_sub_one]
    exact h₁ i j
  · rw [← map_inv (glFin (𝓞 F) F), hinv, glFin_conj_diagAt_sub_one]
    exact h₂ i j

private theorem exists_forall_conj_mem_congrSet (F : Type) [Field F] [NumberField F] (n : ℕ)
    (g : AdelicGL2 (𝓞 F) F) (k : Fin 2) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    ∃ c : ℕ, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) →
        g⁻¹ * diagAt F k (unitIdele F v u) * g ∈ LevelExpansion.congrSet F n := by
  have h := fun i j => exists_forall_mul_conj_mem_idealBall F n v (conjEntry F g k i j)
  choose c hc using h
  refine ⟨(Finset.univ : Finset (Fin 2 × Fin 2)).sup (fun p => c p.1 p.2), fun u hu hdeep => ?_⟩
  have hmono : ∀ i j : Fin 2,
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c i j : ℤ)) := by
    intro i j
    refine hdeep.trans ?_
    rw [WithZero.exp_le_exp]
    have := Finset.le_sup (f := fun p : Fin 2 × Fin 2 => c p.1 p.2) (Finset.mem_univ (i, j))
    simp only at this
    omega
  refine conj_mem_congrSet F n g k v u (fun i j => hc i j u (hmono i j)) (fun i j => hc i j u⁻¹ ?_)
  rw [valued_inv_sub_one F v hu]
  exact hmono i j

private noncomputable def badPlaces (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  (Set.finite_iUnion fun k : Fin 2 => Set.finite_iUnion fun i : Fin 2 => Set.finite_iUnion fun j : Fin 2 =>
    (Filter.eventually_cofinite.1 (conjEntry F g k i j).2 :
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) |
        ¬ conjEntry F g k i j v ∈ v.adicCompletionIntegers F}.Finite)).toFinset

private theorem conjEntry_mem_integers_of_notMem_badPlaces (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPlaces F g)
    (k i j : Fin 2) : conjEntry F g k i j v ∈ v.adicCompletionIntegers F := by
  by_contra h
  apply hv
  simp only [badPlaces, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨k, i, j, h⟩

private theorem conj_mem_congrSet_of_notMem (F : Type) [Field F] [NumberField F] {n : ℕ}
    (g : AdelicGL2 (𝓞 F) F) (k : Fin 2) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}
    (hv1 : v ∉ LevelExpansion.levelPlaces F n) (hv2 : v ∉ badPlaces F g) {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    g⁻¹ * diagAt F k (unitIdele F v u) * g ∈ LevelExpansion.congrSet F n := by
  refine conj_mem_congrSet F n g k v u (fun i j => ?_) (fun i j => ?_)
  · exact mul_conj_mem_idealBall_of_notMem F hv1 (conjEntry_mem_integers_of_notMem_badPlaces F g hv2 k i j) hu
  · exact mul_conj_mem_idealBall_of_notMem F hv1 (conjEntry_mem_integers_of_notMem_badPlaces F g hv2 k i j)
      (valued_inv_eq_one F v hu)

private theorem localChar_eq_one_of_conj_mem (F : Type) [Field F] [NumberField F]
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) {φ₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀) {n : ℕ}
    (hn : LevelExpansion.RightInvariantOn (LevelExpansion.congrSet F n) φ₀) {g : AdelicGL2 (𝓞 F) F} (hg : φ₀ g ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {u : (v.adicCompletion F)ˣ}
    (hαu : ((α (unitIdele F v u) : ℝˣ) : ℝ) = 1)
    (hconj : ∀ k : Fin 2, g⁻¹ * diagAt F k (unitIdele F v u) * g ∈ LevelExpansion.congrSet F n) :
    NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1 := by
  have hμ : ((μ (unitIdele F v u) : ℂˣ) : ℂ) = 1 := by
    have h := hn g _ (hconj 0)
    rw [show g * (g⁻¹ * diagAt F 0 (unitIdele F v u) * g) = diagAt F 0 (unitIdele F v u) * g by group,
      apply_diagAt_zero_mul F hφ₀] at h
    have h1 : ((etaFst μ α hα s₀ (unitIdele F v u) : ℂˣ) : ℂ) = ((μ (unitIdele F v u) : ℂˣ) : ℂ) :=
      val_mul_cpowChar F μ α hα (s₀ + 1 / 2) hαu
    rw [h1] at h
    exact mul_right_cancel₀ hg (h.trans (one_mul _).symm)
  have hν : ((ν (unitIdele F v u) : ℂˣ) : ℂ) = 1 := by
    have h := hn g _ (hconj 1)
    rw [show g * (g⁻¹ * diagAt F 1 (unitIdele F v u) * g) = diagAt F 1 (unitIdele F v u) * g by group,
      apply_diagAt_one_mul F hφ₀] at h
    have h1 : ((etaSnd ν α hα s₀ (unitIdele F v u) : ℂˣ) : ℂ) = ((ν (unitIdele F v u) : ℂˣ) : ℂ) :=
      val_mul_cpowChar F ν α hα (-(s₀ + 1 / 2)) hαu
    rw [h1] at h
    exact mul_right_cancel₀ hg (h.trans (one_mul _).symm)
  rw [localChar_eq_apply_unitIdele]
  apply Units.ext
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ, hν, inv_one,
    mul_one, Units.val_one]

private theorem exists_finset_forall_localChar_eq_one_of_isInducedSection_of_isKfSmooth_of_ne_zero
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ)
      (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀)
      (_hφ₀f : IsKfSmooth F φ₀)
      (_hne : ∃ g : AdelicGL2 (𝓞 F) F, φ₀ g ≠ 0),
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ cN : ℕ,
          ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
            NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
      ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
        ∀ v ∉ S₀, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1 := by
  intro α hα μ ν s₀ φ₀ hφ₀ hφ₀f hne
  obtain ⟨g, hg⟩ := hne
  obtain ⟨n, hn⟩ := LevelExpansion.exists_rightInvariantOn_congrSet_of_isKfSmooth F φ₀ hφ₀f
  classical
  refine ⟨fun v => ?_, LevelExpansion.levelPlaces F n ∪ badPlaces F g, fun v hv u hu => ?_⟩
  · obtain ⟨c₀, hc₀⟩ := exists_forall_conj_mem_congrSet F n g 0 v
    obtain ⟨c₁, hc₁⟩ := exists_forall_conj_mem_congrSet F n g 1 v
    refine ⟨max c₀ c₁ + 1, fun u hu => ?_⟩
    rw [LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hdeep : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-((max c₀ c₁ + 1 : ℕ) : ℤ)) :=
      hu2.resolve_left (Nat.succ_ne_zero _)
    have hle : ∀ c : ℕ, c ≤ max c₀ c₁ →
        Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      intro c hc
      refine hdeep.trans ?_
      rw [WithZero.exp_le_exp]
      omega
    exact localChar_eq_one_of_conj_mem F α hα μ ν s₀ hφ₀ hn hg (height_unitIdele F v hu1)
      (Fin.forall_fin_two.2 ⟨hc₀ u hu1 (hle c₀ (le_max_left _ _)), hc₁ u hu1 (hle c₁ (le_max_right _ _))⟩)
  · exact localChar_eq_one_of_conj_mem F α hα μ ν s₀ hφ₀ hn hg (height_unitIdele F v hu)
      fun k => conj_mem_congrSet_of_notMem F g k (fun h => hv (Finset.mem_union_left _ h))
        (fun h => hv (Finset.mem_union_right _ h)) hu

end BigCellExpansion.QuotientChar
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure"

noncomputable section

open scoped Real
open MeasureTheory AddCircle
open Filter Topology
open BigCellExpansion.RealPlaces

namespace CircleParity

variable {T : ℝ} [hT : Fact (0 < T)]

private scoped instance factTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

private theorem fourierCoeff_eq_zero_of_translate_eq (h : C(AddCircle T, ℂ)) (c : AddCircle T)
    (ε : ℂ)
    (hε : ∀ θ : AddCircle T, h (θ + c) = ε * h θ) (n : ℤ) (hn : (fourier n c : ℂ) ≠ ε) :
    fourierCoeff (⇑h) n = 0 := by
  have h1 : fourierCoeff (fun θ => h (θ + c)) n = ε * fourierCoeff (⇑h) n := by
    have : (fun θ => h (θ + c)) = fun θ => ε * h θ := funext hε
    rw [this]
    exact fourierCoeff.const_mul (f := (⇑h)) ε n
  have h2 := fourierCoeff_translate h c n
  have h3 : ((fourier n c : ℂ) - ε) * fourierCoeff (⇑h) n = 0 := by
    rw [sub_mul, ← h2, h1, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hn
  · exact h4

private theorem fourierCoeff_zero_eq_zero_of_eq_mul_hom (h : C(AddCircle T, ℂ)) (A : ℂ)
    (c : AddCircle T → ℂ)
    (hc : ∀ θ₁ θ₂ : AddCircle T, c (θ₁ + θ₂) = c θ₁ * c θ₂) (hne : ∃ α : AddCircle T, c α ≠ 1)
    (hA : ∀ θ : AddCircle T, h θ = A * c θ) :
    fourierCoeff (⇑h) 0 = 0 := by
  obtain ⟨α, hα⟩ := hne
  refine fourierCoeff_eq_zero_of_translate_eq h α (c α) (fun θ => ?_) 0 ?_
  · rw [hA, hA, hc]
    ring
  · rw [fourier_zero]
    exact fun h1 => hα h1.symm

private theorem one_sub_inv_pow_eq_sum (b : ℂ) (a : ℕ) :
    (1 - b⁻¹) ^ a = ∑ i ∈ Finset.range (a + 1), ((a.choose i : ℂ) * (-1) ^ i) * (b⁻¹) ^ i := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, neg_pow]
  ring

private theorem tendsto_rpow_neg_half_atTop :
    Filter.Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun R : ℝ => 1 + R ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ (Filter.tendsto_pow_atTop two_ne_zero)
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1

private theorem tendsto_mul_rpow_neg_half_atTop :
    Filter.Tendsto (fun R : ℝ => R * (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) Filter.atTop (nhds 1) := by
  have hev : ∀ᶠ R : ℝ in atTop,
      R * (1 + R ^ 2) ^ (-(1 / 2 : ℝ)) = (R⁻¹ ^ 2 + 1) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h1 : R⁻¹ ^ 2 + 1 = (1 + R ^ 2) / R ^ 2 := by
      field_simp
    have h2 : (R ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = R⁻¹ := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
      norm_num [Real.rpow_neg_one]
    rw [h1, Real.div_rpow (by positivity) (by positivity), h2, div_inv_eq_mul, mul_comm]
  have h3 : Tendsto (fun R : ℝ => R⁻¹ ^ 2 + 1) atTop (𝓝 1) := by
    simpa using (tendsto_inv_atTop_zero.pow 2).add_const (1 : ℝ)
  have h4 : Tendsto (fun R : ℝ => (R⁻¹ ^ 2 + 1) ^ (-(1 / 2 : ℝ))) atTop (𝓝 1) := by
    simpa using h3.rpow_const (Or.inl one_ne_zero)
  exact h4.congr' (hev.mono fun R hR => hR.symm)

private def monoC (d : ℕ × ℕ × ℕ) (ζ : ℂ) : ℂ :=
  ζ ^ d.1 * (starRingEnd ℂ) ζ ^ d.2.1 * (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ^ (-((d.2.2 : ℂ) / 2))

private def IsPoleType (d : ℕ × ℕ × ℕ) : Prop := d.2.1 = d.1 ∧ d.2.2 = 2 * d.1

private scoped instance (d : ℕ × ℕ × ℕ) : Decidable (IsPoleType d) := by
  unfold IsPoleType
  infer_instance

private abbrev DropIndex {ι : Type} (d : ι → ℕ × ℕ × ℕ) : Type :=
  {j : ι // ¬ IsPoleType (d j)} ⊕ Σ j : {j : ι // IsPoleType (d j)}, Fin (d j.1).1

private def dropType {ι : Type} (d : ι → ℕ × ℕ × ℕ) : DropIndex d → ℕ × ℕ × ℕ
  | Sum.inl j => d j.1
  | Sum.inr ⟨_, i⟩ => (0, 0, 2 * (i.1 + 1))

private def dropWeight {ι : Type} (d : ι → ℕ × ℕ × ℕ) : DropIndex d → ℂ
  | Sum.inl _ => 1
  | Sum.inr ⟨j, i⟩ => ((d j.1).1.choose (i.1 + 1) : ℂ) * (-1) ^ (i.1 + 1)

private def dropParent {ι : Type} (d : ι → ℕ × ℕ × ℕ) : DropIndex d → ι
  | Sum.inl j => j.1
  | Sum.inr ⟨j, _⟩ => j.1

private theorem monoC_zero (ζ : ℂ) : monoC (0, 0, 0) ζ = 1 := by
  simp [monoC]

private theorem monoC_zero_zero (i : ℕ) (ζ : ℂ) :
    monoC (0, 0, 2 * i) ζ = ((((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ)⁻¹) ^ i := by
  have hb : (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + ‖ζ‖ ^ 2 : ℝ) ≠ 0)
  simp only [monoC, pow_zero, one_mul]
  have h1 : (-((((2 * i : ℕ) : ℕ) : ℂ) / 2)) = -((i : ℕ) : ℂ) := by push_cast; ring
  rw [h1, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]

private theorem monoC_pole_eq_sum (a : ℕ) (ζ : ℂ) :
    monoC (a, a, 2 * a) ζ
      = ∑ i ∈ Finset.range (a + 1), ((a.choose i : ℂ) * (-1) ^ i) * monoC (0, 0, 2 * i) ζ := by
  set b : ℂ := (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) with hb_def
  have hb : b ≠ 0 := by
    rw [hb_def]; exact_mod_cast (by positivity : (1 + ‖ζ‖ ^ 2 : ℝ) ≠ 0)
  have hpole : monoC (a, a, 2 * a) ζ = (1 - b⁻¹) ^ a := by
    have h1 : ζ ^ a * (starRingEnd ℂ) ζ ^ a = ((‖ζ‖ ^ 2 : ℝ) : ℂ) ^ a := by
      rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : (-((((2 * a : ℕ) : ℕ) : ℂ) / 2)) = -((a : ℕ) : ℂ) := by push_cast; ring
    have h3 : 1 - b⁻¹ = ((‖ζ‖ ^ 2 : ℝ) : ℂ) * b⁻¹ := by
      field_simp
      rw [hb_def]; push_cast; ring
    simp only [monoC]
    rw [h1, h2, Complex.cpow_neg, Complex.cpow_natCast, ← hb_def, h3, mul_pow, inv_pow]
  rw [hpole, one_sub_inv_pow_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [monoC_zero_zero, hb_def]

private theorem radial_tendsto (n m : ℕ) (hnm : n ≤ m) :
    Tendsto (fun R : ℝ => R ^ n * (1 + R ^ 2) ^ (-((m : ℝ) / 2))) atTop
      (𝓝 (if n = m then (1 : ℝ) else 0)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hsplit : ∀ᶠ R : ℝ in atTop,
      R ^ n * (1 + R ^ 2) ^ (-(((n + k : ℕ) : ℝ) / 2))
        = (R * (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) ^ n * (1 + R ^ 2) ^ (-((k : ℝ) / 2)) := by
    filter_upwards with R
    have hpos : (0 : ℝ) < 1 + R ^ 2 := by positivity
    rw [mul_pow, ← Real.rpow_natCast ((1 + R ^ 2) ^ (-(1 / 2 : ℝ))) n, ← Real.rpow_mul hpos.le,
      mul_assoc, ← Real.rpow_add hpos]
    congr 2
    push_cast
    ring
  have h1 : Tendsto (fun R : ℝ => (R * (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) ^ n) atTop (𝓝 1) := by
    simpa using tendsto_mul_rpow_neg_half_atTop.pow n
  have h2 : Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (-((k : ℝ) / 2))) atTop
      (𝓝 (if n = n + k then (1 : ℝ) else 0)) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hne : n ≠ n + k := by omega
      simp only [hne, if_false]
      have h3 : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
      exact (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < (k : ℝ) / 2)).comp h3
  refine (Tendsto.congr' (EventuallyEq.symm hsplit) ?_)
  simpa using h1.mul h2

private theorem monoC_ray (d : ℕ × ℕ × ℕ) (hd : d.1 + d.2.1 ≤ d.2.2) (θ : ℝ) :
    Tendsto (fun R : ℝ => monoC d ((R : ℂ) * Complex.exp (θ * Complex.I))) atTop
      (𝓝 (if d.1 + d.2.1 = d.2.2 then
            Complex.exp (θ * Complex.I) ^ d.1
              * (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) ^ d.2.1
          else 0)) := by
  obtain ⟨a, b, m⟩ := d
  simp only at hd ⊢
  set η : ℂ := Complex.exp (θ * Complex.I) with hη
  have hηn : ‖η‖ = 1 := by
    rw [hη]
    simp
  have hkey : ∀ᶠ R : ℝ in atTop,
      monoC (a, b, m) ((R : ℂ) * η)
        = (η ^ a * (starRingEnd ℂ) η ^ b)
            * (((R ^ (a + b) * (1 + R ^ 2) ^ (-((m : ℝ) / 2)) : ℝ)) : ℂ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have hnorm : ‖(R : ℂ) * η‖ ^ 2 = R ^ 2 := by
      rw [norm_mul, hηn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
    have hpos : (0 : ℝ) ≤ 1 + R ^ 2 := by positivity
    have hrad : ((((1 + R ^ 2 : ℝ)) : ℂ)) ^ (-((m : ℂ) / 2))
        = ((((1 + R ^ 2) ^ (-((m : ℝ) / 2)) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_cpow hpos]
      push_cast
      ring
    simp only [monoC, hnorm, mul_pow, map_mul, Complex.conj_ofReal]
    rw [hrad]
    push_cast
    ring
  refine (Tendsto.congr' (EventuallyEq.symm hkey) ?_)
  have hlim := (Complex.continuous_ofReal.tendsto _).comp (radial_tendsto (a + b) m hd)
  have h := hlim.const_mul (η ^ a * (starRingEnd ℂ) η ^ b)
  convert h using 2
  all_goals try rfl
  split_ifs <;> simp

private theorem fourier_sub_eq (a b : ℕ) (θ : ℝ) :
    (fourier ((a : ℤ) - b) ((θ : ℝ) : AddCircle (2 * π)) : ℂ)
      = Complex.exp (θ * Complex.I) ^ a * (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) ^ b := by
  rw [fourier_coe_apply, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast at hπ ⊢
  field_simp
  ring

private theorem sum_pole_eq_zero {ι : Type} [Fintype ι] (d : ι → ℕ × ℕ × ℕ)
    (hd : ∀ j, (d j).1 + (d j).2.1 ≤ (d j).2.2) (C : ι → ℂ) (F : ℂ → ℂ)
    (hF : ∀ ζ : ℂ, F ζ = ∑ j, C j * monoC (d j) ζ)
    (A : ℂ) (c : AddCircle (2 * π) → ℂ)
    (hc : ∀ θ₁ θ₂ : AddCircle (2 * π), c (θ₁ + θ₂) = c θ₁ * c θ₂)
    (hne : ∃ α : AddCircle (2 * π), c α ≠ 1)
    (hlim : ∀ θ : ℝ, Tendsto (fun R : ℝ => F ((R : ℂ) * Complex.exp (θ * Complex.I))) atTop
      (𝓝 (A * c ((θ : ℝ) : AddCircle (2 * π))))) :
    ∑ j ∈ Finset.univ.filter (fun j => IsPoleType (d j)), C j = 0 := by
  classical
  set S : Finset ι := Finset.univ.filter (fun j => (d j).1 + (d j).2.1 = (d j).2.2) with hS
  set h : C(AddCircle (2 * π), ℂ) :=
    ∑ j ∈ S, C j • (fourier (((d j).1 : ℤ) - (d j).2.1) : C(AddCircle (2 * π), ℂ)) with hh
  have hval : ∀ θ : ℝ, h ((θ : ℝ) : AddCircle (2 * π)) = A * c ((θ : ℝ) : AddCircle (2 * π)) := by
    intro θ
    have hF' : Tendsto (fun R : ℝ => F ((R : ℂ) * Complex.exp (θ * Complex.I))) atTop
        (𝓝 (∑ j, C j * (if (d j).1 + (d j).2.1 = (d j).2.2 then
            Complex.exp (θ * Complex.I) ^ (d j).1
              * (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) ^ (d j).2.1
          else 0))) := by
      simp_rw [hF]
      exact tendsto_finsetSum _ fun j _ => (monoC_ray (d j) (hd j) θ).const_mul (C j)
    rw [← tendsto_nhds_unique hF' (hlim θ), hh, ContinuousMap.coe_sum, Finset.sum_apply, hS,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, fourier_sub_eq]
    · simp
  have hAc : ∀ θq : AddCircle (2 * π), h θq = A * c θq := fun θq =>
    QuotientAddGroup.induction_on θq hval
  have hzero := fourierCoeff_zero_eq_zero_of_eq_mul_hom h A c hc hne hAc
  rw [hh, ContinuousMap.coe_sum] at hzero
  simp_rw [ContinuousMap.coe_smul] at hzero
  rw [fourierCoeff.sum S (fun i => C i • ⇑(fourier (((d i).1 : ℤ) - (d i).2.1))) fun i _ =>
    integrable_of_continuous ((map_continuous (fourier _)).const_smul (C i))] at hzero
  simp only [Finset.sum_apply, fourierCoeff.const_smul, fourierCoeff_fourier,
    Pi.single_apply, smul_eq_mul] at hzero
  rw [← hzero, hS, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hp : IsPoleType (d j)
  · have h1 : (d j).2.1 = (d j).1 := hp.1
    have h2 : (d j).2.2 = 2 * (d j).1 := hp.2
    have h3 : (d j).1 + (d j).2.1 = (d j).2.2 := by omega
    have h4 : (0 : ℤ) = ((d j).1 : ℤ) - (d j).2.1 := by omega
    rw [if_pos hp, if_pos h3, if_pos h4, mul_one]
  · by_cases h3 : (d j).1 + (d j).2.1 = (d j).2.2
    · have h4 : (0 : ℤ) ≠ ((d j).1 : ℤ) - (d j).2.1 := fun h4 => hp ⟨by omega, by omega⟩
      rw [if_neg hp, if_pos h3, if_neg h4, mul_zero]
    · rw [if_neg hp, if_neg h3]

private theorem eq_of_isPoleType {d : ℕ × ℕ × ℕ} (hp : IsPoleType d) : d = (d.1, d.1, 2 * d.1) := by
  obtain ⟨h1, h2⟩ := hp
  ext <;> simp [h1, h2]

private theorem drop {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℕ × ℕ × ℕ)
    (hd : ∀ j, (d j).1 + (d j).2.1 ≤ (d j).2.2) (C : ι → ℂ) (F : ℂ → ℂ)
    (hF : ∀ ζ : ℂ, F ζ = ∑ j, C j * monoC (d j) ζ)
    (A : ℂ) (c : AddCircle (2 * π) → ℂ)
    (hc : ∀ θ₁ θ₂ : AddCircle (2 * π), c (θ₁ + θ₂) = c θ₁ * c θ₂)
    (hne : ∃ α : AddCircle (2 * π), c α ≠ 1)
    (hlim : ∀ θ : ℝ, Tendsto (fun R : ℝ => F ((R : ℂ) * Complex.exp (θ * Complex.I))) atTop
      (𝓝 (A * c ((θ : ℝ) : AddCircle (2 * π))))) :
    (∀ j' : DropIndex d, (dropType d j').1 + (dropType d j').2.1 ≤ (dropType d j').2.2) ∧
      (∀ j' : DropIndex d, ¬ IsPoleType (dropType d j')) ∧
      ∀ ζ : ℂ, F ζ = ∑ j' : DropIndex d,
        dropWeight d j' * C (dropParent d j') * monoC (dropType d j') ζ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro (j | ⟨j, i⟩)
    · exact hd j.1
    · simp [dropType]
  · rintro (j | ⟨j, i⟩)
    · exact j.2
    · simp [dropType, IsPoleType]
  · intro ζ
    have hpole := sum_pole_eq_zero d hd C F hF A c hc hne hlim

    have hterm : ∀ j : {j : ι // IsPoleType (d j)},
        C j.1 * monoC (d j.1) ζ
          = C j.1 + ∑ i : Fin (d j.1).1,
              dropWeight d (Sum.inr ⟨j, i⟩) * C (dropParent d (Sum.inr ⟨j, i⟩))
                * monoC (dropType d (Sum.inr ⟨j, i⟩)) ζ := by
      intro j
      have hmono : monoC (d j.1) ζ = monoC ((d j.1).1, (d j.1).1, 2 * (d j.1).1) ζ := by
        rw [← eq_of_isPoleType j.2]
      rw [hmono, monoC_pole_eq_sum, Finset.sum_range_succ', Nat.choose_zero_right, pow_zero,
        mul_one, Nat.cast_one, one_mul, Nat.mul_zero, monoC_zero, mul_add, mul_one, add_comm,
        Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      simp only [dropWeight, dropType, dropParent]
      ring
    rw [hF, ← Fintype.sum_subtype_add_sum_subtype (fun j => IsPoleType (d j)),
      Fintype.sum_sum_type, Fintype.sum_sigma]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    have hzero : ∑ j : {j : ι // IsPoleType (d j)}, C j.1 = 0 := by
      rw [← hpole]
      exact (Finset.sum_subtype _ (fun j => by simp) _).symm
    rw [hzero, zero_add, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [dropWeight, dropParent, dropType]

end CircleParity
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

noncomputable section

open scoped Real
open Filter Topology

namespace CircleParity

private def DropStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℕ × ℕ × ℕ)
    (_ : ∀ j, (d j).1 + (d j).2.1 ≤ (d j).2.2) (C : ι → ℂ) (F : ℂ → ℂ)
    (_ : ∀ ζ : ℂ, F ζ = ∑ j, C j * monoC (d j) ζ)
    (A : ℂ) (c : AddCircle (2 * π) → ℂ)
    (_ : ∀ θ₁ θ₂ : AddCircle (2 * π), c (θ₁ + θ₂) = c θ₁ * c θ₂)
    (_ : ∃ α : AddCircle (2 * π), c α ≠ 1)
    (_ : ∀ θ : ℝ, Tendsto (fun R : ℝ => F ((R : ℂ) * Complex.exp (θ * Complex.I))) atTop
      (𝓝 (A * c ((θ : ℝ) : AddCircle (2 * π))))),
    (∀ j' : DropIndex d, (dropType d j').1 + (dropType d j').2.1 ≤ (dropType d j').2.2) ∧
      (∀ j' : DropIndex d, ¬ IsPoleType (dropType d j')) ∧
      ∀ ζ : ℂ, F ζ = ∑ j' : DropIndex d,
        dropWeight d j' * C (dropParent d j') * monoC (dropType d j') ζ

private def monoPi {W : Type} [Fintype W] (dd : W → ℕ × ℕ × ℕ) (ζ : W → ℂ) : ℂ :=
  ∏ w, monoC (dd w) (ζ w)

private theorem monoPi_eq_mul_prod_erase {W : Type} [Fintype W] [DecidableEq W] (w₀ : W)
    (dd : W → ℕ × ℕ × ℕ) (ζ : W → ℂ) :
    monoPi dd ζ = monoC (dd w₀) (ζ w₀) * ∏ w ∈ Finset.univ.erase w₀, monoC (dd w) (ζ w) := by
  unfold monoPi
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ w₀)).symm

private theorem drop_at_place (hdrop : DropStatement) {W : Type} [Fintype W] [DecidableEq W] (w₀ : W)
    {ι : Type} [Fintype ι] [DecidableEq ι] (dd : ι → W → ℕ × ℕ × ℕ)
    (hlaw : ∀ j w, (dd j w).1 + (dd j w).2.1 ≤ (dd j w).2.2)
    {P : Type} (C : ι → P → ℂ) (Φ : P → (W → ℂ) → ℂ)
    (hΦ : ∀ p ζ, Φ p ζ = ∑ j, C j p * monoPi (dd j) ζ)
    (c : AddCircle (2 * π) → ℂ)
    (hc : ∀ θ₁ θ₂ : AddCircle (2 * π), c (θ₁ + θ₂) = c θ₁ * c θ₂)
    (hne : ∃ α : AddCircle (2 * π), c α ≠ 1)
    (A : P → (W → ℂ) → ℂ)
    (hlim : ∀ (p : P) (ζ : W → ℂ) (θ : ℝ),
      Tendsto (fun R : ℝ => Φ p (Function.update ζ w₀ ((R : ℂ) * Complex.exp (θ * Complex.I)))) atTop
        (𝓝 (A p ζ * c ((θ : ℝ) : AddCircle (2 * π))))) :
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι') (dd' : ι' → W → ℕ × ℕ × ℕ) (wt : ι' → ℂ)
      (par : ι' → ι),
      (∀ j' w, (dd' j' w).1 + (dd' j' w).2.1 ≤ (dd' j' w).2.2) ∧
      (∀ j', ¬ IsPoleType (dd' j' w₀)) ∧
      (∀ j' w, w ≠ w₀ → dd' j' w = dd (par j') w) ∧
      ∀ p ζ, Φ p ζ = ∑ j', wt j' * C (par j') p * monoPi (dd' j') ζ := by
  classical
  let d : ι → ℕ × ℕ × ℕ := fun j => dd j w₀
  refine ⟨DropIndex d, inferInstance, inferInstance,
    fun j' w => if w = w₀ then dropType d j' else dd (dropParent d j') w,
    dropWeight d, dropParent d, ?_, ?_, ?_, ?_⟩
  · rintro (j | ⟨j, i⟩) w
    · by_cases hw : w = w₀
      · simp only [hw, if_true, dropType]; exact hlaw _ _
      · simp only [if_neg hw, dropParent]; exact hlaw _ _
    · by_cases hw : w = w₀
      · simp only [hw, if_true, dropType]; omega
      · simp only [if_neg hw, dropParent]; exact hlaw _ _
  · rintro (j | ⟨j, i⟩)
    · simp only [if_true, dropType]; exact j.2
    · simp only [if_true, dropType, IsPoleType]; omega
  · intro j' w hw
    simp only [if_neg hw]
  · intro p ζ

    let rest : ι → ℂ := fun j => ∏ w ∈ Finset.univ.erase w₀, monoC (dd j w) (ζ w)
    have hrest : ∀ (j : ι) (z : ℂ),
        monoPi (dd j) (Function.update ζ w₀ z) = monoC (d j) z * rest j := by
      intro j z
      rw [monoPi_eq_mul_prod_erase w₀, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    let F : ℂ → ℂ := fun z => Φ p (Function.update ζ w₀ z)
    have hF : ∀ z : ℂ, F z = ∑ j, (C j p * rest j) * monoC (d j) z := by
      intro z
      simp only [F, hΦ, hrest]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have key := (hdrop d (fun j => hlaw j w₀) (fun j => C j p * rest j) F hF (A p ζ) c hc hne
      (fun θ => hlim p ζ θ)).2.2 (ζ w₀)
    have hF₀ : F (ζ w₀) = Φ p ζ := by
      simp only [F, Function.update_eq_self]
    rw [← hF₀, key]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have hsplit : monoPi (fun w => if w = w₀ then dropType d j' else dd (dropParent d j') w) ζ
        = monoC (dropType d j') (ζ w₀) * rest (dropParent d j') := by
      rw [monoPi_eq_mul_prod_erase w₀, if_pos rfl]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [if_neg (Finset.ne_of_mem_erase hw)]
    rw [hsplit]
    ring

private theorem drop_at_places (hdrop : DropStatement) {W : Type} [Fintype W] [DecidableEq W]
    {P : Type} (Φ : P → (W → ℂ) → ℂ)
    (c : W → AddCircle (2 * π) → ℂ)
    (hc : ∀ (w : W) (θ₁ θ₂ : AddCircle (2 * π)), c w (θ₁ + θ₂) = c w θ₁ * c w θ₂)
    (A : W → P → (W → ℂ) → ℂ)
    (hlim : ∀ (w : W) (p : P) (ζ : W → ℂ) (θ : ℝ),
      Tendsto (fun R : ℝ => Φ p (Function.update ζ w ((R : ℂ) * Complex.exp (θ * Complex.I)))) atTop
        (𝓝 (A w p ζ * c w ((θ : ℝ) : AddCircle (2 * π))))) :
    ∀ (S : List W), (∀ w ∈ S, ∃ α : AddCircle (2 * π), c w α ≠ 1) →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (dd : ι → W → ℕ × ℕ × ℕ)
      (_ : ∀ j w, (dd j w).1 + (dd j w).2.1 ≤ (dd j w).2.2) (C : ι → P → ℂ)
      (_ : ∀ p ζ, Φ p ζ = ∑ j, C j p * monoPi (dd j) ζ),
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι') (dd' : ι' → W → ℕ × ℕ × ℕ) (wt : ι' → ℂ)
      (par : ι' → ι),
      (∀ j' w, (dd' j' w).1 + (dd' j' w).2.1 ≤ (dd' j' w).2.2) ∧
      (∀ j', ∀ w ∈ S, ¬ IsPoleType (dd' j' w)) ∧
      (∀ j' w, w ∉ S → dd' j' w = dd (par j') w) ∧
      ∀ p ζ, Φ p ζ = ∑ j', wt j' * C (par j') p * monoPi (dd' j') ζ := by
  intro S
  induction S with
  | nil =>
    intro _ ι _ _ dd hlaw C hΦ
    exact ⟨ι, inferInstance, inferInstance, dd, fun _ => 1, id, hlaw, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ => rfl, fun p ζ => by simpa using hΦ p ζ⟩
  | cons w₀ S ih =>
    intro hS ι _ _ dd hlaw C hΦ
    obtain ⟨ι₁, _, _, dd₁, wt₁, par₁, hlaw₁, hpole₁, hoff₁, hΦ₁⟩ :=
      ih (fun w hw => hS w (List.mem_cons_of_mem _ hw)) dd hlaw C hΦ
    obtain ⟨ι₂, _, _, dd₂, wt₂, par₂, hlaw₂, hpole₂, hoff₂, hΦ₂⟩ :=
      drop_at_place hdrop w₀ dd₁ hlaw₁ (fun j' p => wt₁ j' * C (par₁ j') p) Φ
        (fun p ζ => by rw [hΦ₁ p ζ]) (c w₀) (hc w₀)
        (hS w₀ List.mem_cons_self) (A w₀) (hlim w₀)
    refine ⟨ι₂, inferInstance, inferInstance, dd₂, fun j => wt₂ j * wt₁ (par₂ j), par₁ ∘ par₂, hlaw₂,
      ?_, ?_, fun p ζ => ?_⟩
    · intro j w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hpole₂ j
      · by_cases hww : w = w₀
        · subst hww; exact hpole₂ j
        · rw [hoff₂ j w hww]; exact hpole₁ _ w hw'
    · intro j w hw
      have hw₀ : w ≠ w₀ := fun h => hw (h ▸ List.mem_cons_self)
      have hwS : w ∉ S := fun h => hw (List.mem_cons_of_mem _ h)
      rw [hoff₂ j w hw₀, hoff₁ _ w hwS]
      rfl
    · rw [hΦ₂ p ζ]
      refine Finset.sum_congr rfl fun _ _ => ?_
      simp only [Function.comp]
      ring

end CircleParity
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

noncomputable section

namespace BigCellExpansion
namespace EtaNegHalf

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField AutomorphicForm"

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem neg_half_add_half : (-(1 / 2 : ℂ)) + 1 / 2 = 0 := by ring

private theorem etaFst_neg_half_apply (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (x : (AdeleRing R K)ˣ) :
    ((etaFst μ α hα (-(1 / 2 : ℂ)) x : ℂˣ) : ℂ) = ((μ x : ℂˣ) : ℂ) := by
  rw [etaFst_apply, Units.val_mul, cpowChar_apply_val, neg_half_add_half, Complex.cpow_zero, mul_one]

private theorem etaSnd_neg_half_apply (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (x : (AdeleRing R K)ˣ) :
    ((etaSnd ν α hα (-(1 / 2 : ℂ)) x : ℂˣ) : ℂ) = ((ν x : ℂˣ) : ℂ) := by
  rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val, neg_half_add_half, neg_zero, Complex.cpow_zero,
    mul_one]

private theorem isInducedSection_of_neg_half {μ ν : (AdeleRing R K)ˣ →* ℂˣ}
    {α : (AdeleRing R K)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {φ : AdelicGL2 R K → ℂ}
    (hφ : IsInducedSection R K (etaFst μ α hα (-(1 / 2 : ℂ))) (etaSnd ν α hα (-(1 / 2 : ℂ))) φ) :
    IsInducedSection R K μ ν φ := by
  intro b hb g
  rw [hφ b hb g, etaFst_neg_half_apply, etaSnd_neg_half_apply]

private theorem neg_two_mul_neg_half_add_one : -(2 * (-(1 / 2 : ℂ)) + 1) = 0 := by ring

end BigCellExpansion.EtaNegHalf
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

namespace BigCellExpansion
namespace ArchExpansion

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicLevel"
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

noncomputable section

section Smooth

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.AdelicLevel IsDedekindDomain"
open AutomorphicForm AutomorphicForm.WindowedSiegel FLT.SmoothVectors
open BigCellExpansion.RealPlaces

variable {F : Type} [Field F] [NumberField F]

private theorem eq_of_glArch_eq_of_glFin_eq {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h) (h₂ : glFin (𝓞 F) F g = glFin (𝓞 F) F h) : g = h := by
  ext i j
  refine Prod.ext ?_ ?_
  · exact congrArg (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      (k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  · exact congrArg (fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂

private theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {g u : AdelicGL2 (𝓞 F) F}
    (hg : glFin (𝓞 F) F g = 1) (hu : glArch (𝓞 F) F u = 1) : g * u = u * g :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, hu, mul_one, one_mul])
    (by rw [map_mul, map_mul, hg, mul_one, one_mul])

private theorem glFin_eq_one_of_mem_archRowIsometrySubgroup {w : InfinitePlace F} {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ archRowIsometrySubgroup F w) : glFin (𝓞 F) F g = 1 := by
  obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hg
  exact glFin_adelicArchGLIncl F _

private theorem isKfSmooth_of_forall_fixed₂ {φ₁ φ₂ f : AdelicGL2 (𝓞 F) F → ℂ}
    (h₁ : IsKfSmooth F φ₁) (h₂ : IsKfSmooth F φ₂)
    (hf : ∀ u : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F u = 1 → (∀ x, φ₁ (x * u) = φ₁ x) →
      (∀ x, φ₂ (x * u) = φ₂ x) → ∀ x, f (x * u) = f x) :
    IsKfSmooth F f := by
  unfold IsKfSmooth at h₁ h₂ ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at h₁ h₂ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk φ₁ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) ⊓ MulAction.stabilizer
    (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk φ₂ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ))
    (fun u hu => ?_) ?_
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    rw [MulAction.mem_stabilizer_iff] at hu1 hu2 ⊢
    have e₁ : ∀ x, φ₁ (x * (u : AdelicGL2 (𝓞 F) F)) = φ₁ x := fun x =>
      congrArg (fun ψ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun ψ x) hu1
    have e₂ : ∀ x, φ₂ (x * (u : AdelicGL2 (𝓞 F) F)) = φ₂ x := fun x =>
      congrArg (fun ψ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun ψ x) hu2
    exact RightTranslationFn.ext fun x => hf u u.2 e₁ e₂ x
  · rw [Subgroup.coe_inf]
    exact h₁.inter h₂

private theorem isKfSmooth_of_forall_fixed {φ f : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ)
    (hf : ∀ u : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F u = 1 → (∀ x, φ (x * u) = φ x) → ∀ x, f (x * u) = f x) :
    IsKfSmooth F f :=
  isKfSmooth_of_forall_fixed₂ hφ hφ fun u hu h _ => hf u hu h

private theorem isKfSmooth_rTrans {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ)
    {g : AdelicGL2 (𝓞 F) F} (hg : glFin (𝓞 F) F g = 1) : IsKfSmooth F (rTrans g φ) :=
  isKfSmooth_of_forall_fixed hφ fun u hu hφu x => by
    show φ (x * u * g) = φ (x * g)
    rw [mul_assoc, ← mul_comm_of_glFin_eq_one_of_glArch_eq_one hg hu, ← mul_assoc, hφu]

private theorem isKfSmooth_add {f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : IsKfSmooth F f₁)
    (h₂ : IsKfSmooth F f₂) : IsKfSmooth F (f₁ + f₂) :=
  isKfSmooth_of_forall_fixed₂ h₁ h₂ fun _ _ e₁ e₂ x => by
    show f₁ (x * _) + f₂ (x * _) = f₁ x + f₂ x
    rw [e₁, e₂]

private theorem isKfSmooth_smul {f : AdelicGL2 (𝓞 F) F → ℂ} (c : ℂ) (hf : IsKfSmooth F f) :
    IsKfSmooth F (c • f) :=
  isKfSmooth_of_forall_fixed hf fun _ _ e x => by
    show c * f (x * _) = c * f x
    rw [e]

private theorem isKfSmooth_of_mem_transSpan {w : InfinitePlace F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ transSpan w φ) : IsKfSmooth F v := by
  have hv' : v ∈ Submodule.span ℂ
      (Set.range fun g : ↥(archRowIsometrySubgroup F w) => rTrans (g : AdelicGL2 (𝓞 F) F) φ) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact isKfSmooth_rTrans hφ (glFin_eq_one_of_mem_archRowIsometrySubgroup g.2)
  | zero => exact isKfSmooth_zero F
  | add f₁ f₂ _ _ ih₁ ih₂ => exact isKfSmooth_add ih₁ ih₂
  | smul c f _ ih => exact isKfSmooth_smul c ih

private theorem isKfSmooth_coeffFn {w : InfinitePlace F} (hw : w.IsReal) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) (n : ℤ) : IsKfSmooth F (coeffFn hw φ n) :=
  isKfSmooth_of_forall_fixed hφ fun u hu hφu y => by
    show fourierCoeff (circleFn hw φ (y * u)) n = fourierCoeff (circleFn hw φ y) n
    congr 1
    funext cq
    induction cq using QuotientAddGroup.induction_on with
    | H θ =>
      rw [circleFn_coe, circleFn_coe, mul_assoc, ← mul_comm_of_glFin_eq_one_of_glArch_eq_one
        (glFin_eq_one_of_mem_archRowIsometrySubgroup (rotAt_incl_mem_archRowIsometrySubgroup F hw θ)) hu,
        ← mul_assoc, hφu]

end Smooth
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section Parity

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.AdelicLevel IsDedekindDomain"
open AutomorphicForm AutomorphicForm.WindowedSiegel FLT.SmoothVectors
open BigCellExpansion.RealPlaces

variable {F : Type} [Field F] [NumberField F]

private theorem neg_one_zpow_neg (k : ℤ) : (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k := by
  have h2 : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact Even.neg_one_zpow ⟨k, rfl⟩
  rw [_root_.zpow_neg]
  exact inv_eq_of_mul_eq_one_right h2

private def antipodalSign (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (i : {w : InfinitePlace F // w.IsReal}) : ℂ :=
  ((χ₁ (NumberField.TateGlobal.archUnitHom i.1 (-1)) : ℂˣ) : ℂ)
    * ((χ₂ (NumberField.TateGlobal.archUnitHom i.1 (-1)) : ℂˣ) : ℂ)

private theorem incl_rotAt_pi (i : {w : InfinitePlace F // w.IsReal}) :
    adelicArchGLInclAt F i.1 (rotAt i.2 Real.pi)
      = AutomorphicForm.centralScalar (𝓞 F) F (NumberField.TateGlobal.archUnitHom i.1 (-1)) := by
  refine Units.ext ?_
  change ((adelicArchGLInclAt F i.1 (rotAt i.2 Real.pi) : AdelicGL2 (𝓞 F) F)
      : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    = Matrix.scalar (Fin 2)
        ((NumberField.AdelicVolume.archCentralUnit F i.1 (-1) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  refine matrix_ext_of_proj F (fun v => ?_) ?_
  · by_cases hv : v = i.1
    · subst hv
      rw [projArch_incl_self]
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        rotAt, glEquivOfRingEquiv_apply_entry, rotGL_coe]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, projArch_apply, NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_neg,
          Units.val_one]
        fin_cases a <;> simp [Real.cos_pi]
      · rw [if_neg hab, projArch_apply]
        show _ = 0
        fin_cases a <;> fin_cases b <;> simp_all [Real.sin_pi]
    · rw [projArch_incl_of_ne F hv]
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl, projArch_apply, NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hv]
      · rw [if_neg hab, if_neg hab, projArch_apply]
        rfl
  · rw [projFin_incl]
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl, projFin_apply, NumberField.AdelicVolume.archCentralUnit_snd]
    · rw [if_neg hab, if_neg hab, projFin_apply]
      rfl

private theorem mul_centralScalar_eq (z : (AdeleRing (𝓞 F) F)ˣ) (y : AdelicGL2 (𝓞 F) F) :
    y * AutomorphicForm.centralScalar (𝓞 F) F z = AutomorphicForm.centralScalar (𝓞 F) F z * y := by
  refine Units.ext ?_
  change (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
    = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

private theorem mul_incl_rotAt_pi (i : {w : InfinitePlace F // w.IsReal}) (y : AdelicGL2 (𝓞 F) F) :
    y * adelicArchGLInclAt F i.1 (rotAt i.2 Real.pi)
      = AutomorphicForm.centralScalar (𝓞 F) F (NumberField.TateGlobal.archUnitHom i.1 (-1)) * y := by
  rw [incl_rotAt_pi, mul_centralScalar_eq]

private theorem isInducedSection_coeffFn {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    {w₀ : InfinitePlace F} (hw₀ : w₀.IsReal) (n : ℤ) :
    AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ (coeffFn hw₀ f n) := by
  intro b hb y
  have hfun : circleFn hw₀ f (b * y)
      = fun θq => ((χ₁ (AutomorphicForm.borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ)
          * ((χ₂ (AutomorphicForm.borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ) * circleFn hw₀ f y θq := by
    funext θq
    refine QuotientAddGroup.induction_on θq fun θ => ?_
    rw [circleFn_coe, circleFn_coe, mul_assoc b y, hf b hb]
  show fourierCoeff (circleFn hw₀ f (b * y)) n = _ * fourierCoeff (circleFn hw₀ f y) n
  rw [hfun]
  exact fourierCoeff.const_mul (circleFn hw₀ f y) _ n

private theorem circleFn_add_pi_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (i : {w : InfinitePlace F // w.IsReal}) (y : AdelicGL2 (𝓞 F) F) (θq : AddCircle (2 * Real.pi)) :
    circleFn i.2 f y (θq + ((Real.pi : ℝ) : AddCircle (2 * Real.pi)))
      = antipodalSign χ₁ χ₂ i * circleFn i.2 f y θq := by
  refine QuotientAddGroup.induction_on θq fun θ => ?_
  have h1 : (((θ : ℝ) : AddCircle (2 * Real.pi)) + ((Real.pi : ℝ) : AddCircle (2 * Real.pi)))
      = ((θ + Real.pi : ℝ) : AddCircle (2 * Real.pi)) := rfl
  show circleFn i.2 f y (((θ : ℝ) : AddCircle (2 * Real.pi)) + ↑Real.pi) = _
  rw [h1, circleFn_coe, circleFn_coe, rotAt_add, map_mul, ← mul_assoc, mul_incl_rotAt_pi,
    AutomorphicForm.isInducedSection_centralScalar_mul hf]
  rfl

private theorem coeffFn_eq_zero_of_isInducedSection {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f)
    (hf : AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ f) (i : {w : InfinitePlace F // w.IsReal})
    {n : ℤ} (hn : (-1 : ℂ) ^ n ≠ antipodalSign χ₁ χ₂ i) (y : AdelicGL2 (𝓞 F) F) :
    coeffFn i.2 f n y = 0 := by
  let h : C(AddCircle (2 * Real.pi), ℂ) := ⟨circleFn i.2 f y, continuous_circleFn i.2 hfc y⟩
  have hpi : (fourier n ((Real.pi : ℝ) : AddCircle (2 * Real.pi)) : ℂ) = (-1) ^ n := by
    have h2 : ((Real.pi : ℝ) : AddCircle (2 * Real.pi))
        = (((2 * Real.pi) / 2 : ℝ) : AddCircle (2 * Real.pi)) := by
      congr 1
      ring
    rw [h2, fourier_coe_apply]
    have h3 : (2 * Real.pi * Complex.I * (n : ℂ) * ((2 * Real.pi / 2 : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ))
        = (n : ℂ) * (Real.pi * Complex.I) := by
      have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
    rw [h3, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have h1 : fourierCoeff (fun θq => h (θq + ((Real.pi : ℝ) : AddCircle (2 * Real.pi)))) n
      = antipodalSign χ₁ χ₂ i * fourierCoeff (⇑h) n := by
    have h4 : (fun θq => h (θq + ((Real.pi : ℝ) : AddCircle (2 * Real.pi))))
        = fun θq => antipodalSign χ₁ χ₂ i * h θq :=
      funext fun θq => circleFn_add_pi_of_isInducedSection hf i y θq
    rw [h4]
    exact fourierCoeff.const_mul (⇑h) _ n
  have h5 := fourierCoeff_translate h ((Real.pi : ℝ) : AddCircle (2 * Real.pi)) n
  have h6 : ((fourier n ((Real.pi : ℝ) : AddCircle (2 * Real.pi)) : ℂ) - antipodalSign χ₁ χ₂ i)
      * fourierCoeff (⇑h) n = 0 := by
    rw [sub_mul, ← h5, h1, sub_self]
  rcases mul_eq_zero.mp h6 with h7 | h7
  · exact absurd (by rw [← hpi]; exact sub_eq_zero.mp h7) hn
  · exact h7

private theorem multi_real_expansion_smooth_induced {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ)
    (hφs : AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ φ) :
    ∀ L : List {w : InfinitePlace F // w.IsReal}, L.Nodup →
      ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ)
        (kd : ι → {w : InfinitePlace F // w.IsReal} → ℤ),
        (∀ j : ι, Continuous (Cf j) ∧ IsArchKFinite F (Cf j) ∧ IsKfSmooth F (Cf j) ∧
          AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ (Cf j)) ∧
        (∀ (j : ι) (i : {w : InfinitePlace F // w.IsReal}), i ∈ L →
          (-1 : ℂ) ^ (kd j i) = antipodalSign χ₁ χ₂ i) ∧
        ∀ (y : AdelicGL2 (𝓞 F) F) (θ : {w : InfinitePlace F // w.IsReal} → ℝ),
          φ (y * rotProd L θ) = ∑ j : ι, Cf j y * charProd L (kd j) θ := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨Unit, inferInstance, fun _ => φ, fun _ _ => 0, fun _ => ⟨hφc, hφK, hφf, hφs⟩,
      fun _ _ hi => (List.not_mem_nil hi).elim, fun y θ => ?_⟩
    rw [rotProd_nil, mul_one]
    simp [charProd_nil]
  | cons w₀ L ih =>
    intro hL
    obtain ⟨hw₀L, hLnd⟩ := List.nodup_cons.mp hL
    obtain ⟨ι, hι, Cf, kd, hCf, hpar, hexp⟩ := ih hLnd
    choose tfin htfin using fun j : ι => (uniform_expansion w₀.2 (hCf j).1 (hCf j).2.1).2
    have hcoef : ∀ (j : ι) (n : ℤ),
        Continuous (coeffFn w₀.2 (Cf j) n) ∧ IsArchKFinite F (coeffFn w₀.2 (Cf j) n)
          ∧ IsKfSmooth F (coeffFn w₀.2 (Cf j) n)
          ∧ AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ (coeffFn w₀.2 (Cf j) n) :=
      fun j n => ⟨((uniform_expansion w₀.2 (hCf j).1 (hCf j).2.1).1 n).1,
        ((uniform_expansion w₀.2 (hCf j).1 (hCf j).2.1).1 n).2, isKfSmooth_coeffFn w₀.2 (hCf j).2.2.1 n,
        isInducedSection_coeffFn (hCf j).2.2.2 w₀.2 n⟩
    let tfin' : ι → Finset ℤ := fun j => (tfin j).filter fun n => (-1 : ℂ) ^ n = antipodalSign χ₁ χ₂ w₀
    have hfilt : ∀ (j : ι) (y : AdelicGL2 (𝓞 F) F) (θ : ℝ),
        ∑ n ∈ tfin j, coeffFn w₀.2 (Cf j) n y * fourier n (θ : AddCircle (2 * Real.pi))
          = ∑ n ∈ tfin' j, coeffFn w₀.2 (Cf j) n y * fourier n (θ : AddCircle (2 * Real.pi)) := by
      intro j y θ
      refine (Finset.sum_filter_of_ne fun n _ hne => ?_).symm
      by_contra hn
      exact hne (by rw [coeffFn_eq_zero_of_isInducedSection (hCf j).1 (hCf j).2.2.2 w₀ hn y, zero_mul])
    refine ⟨(Σ j : ι, ↥(tfin' j)), inferInstance,
      fun p => coeffFn w₀.2 (Cf p.1) (p.2 : ℤ),
      fun p i => if i = w₀ then (p.2 : ℤ) else kd p.1 i,
      fun p => hcoef p.1 p.2, fun p i hi => ?_, fun y θ => ?_⟩
    · rcases List.mem_cons.mp hi with hiw | hiL
      · subst hiw
        show (-1 : ℂ) ^ (if i = i then (p.2 : ℤ) else kd p.1 i) = antipodalSign χ₁ χ₂ i
        rw [if_pos rfl]
        exact (Finset.mem_filter.mp p.2.2).2
      · have hne : i ≠ w₀ := fun h => hw₀L (h ▸ hiL)
        show (-1 : ℂ) ^ (if i = w₀ then (p.2 : ℤ) else kd p.1 i) = antipodalSign χ₁ χ₂ i
        rw [if_neg hne]
        exact hpar p.1 i hiL
    · rw [rotProd_cons, ← mul_assoc, hexp (y * adelicArchGLInclAt F w₀.1 (rotAt w₀.2 (θ w₀))) θ]
      simp_rw [htfin, hfilt]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, ← Finset.sum_coe_sort (s := tfin' j)]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp only
      rw [charProd_cons, if_pos rfl, mul_assoc]
      congr 2
      unfold charProd
      refine list_prod_map_congr L fun i hi => ?_
      have hne : ¬ i = w₀ := fun h => hw₀L (h ▸ hi)
      dsimp only
      rw [if_neg hne]

end Parity
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section ComplexPort

p2m_open "Matrix NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open AutomorphicForm AutomorphicForm.WindowedSiegel BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa

open scoped ComplexConjugate

section MonoClass

private def monoC (d : ℕ × ℕ × ℕ) (ζ : ℂ) : ℂ :=
  ζ ^ d.1 * (starRingEnd ℂ) ζ ^ d.2.1 * (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ^ (-((d.2.2 : ℂ) / 2))

private theorem base_ne_zero (ζ : ℂ) : (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

private theorem monoC_zero (ζ : ℂ) : monoC (0, 0, 0) ζ = 1 := by
  simp [monoC]

private theorem monoC_mul (d d' : ℕ × ℕ × ℕ) (ζ : ℂ) :
    monoC d ζ * monoC d' ζ = monoC (d.1 + d'.1, d.2.1 + d'.2.1, d.2.2 + d'.2.2) ζ := by
  unfold monoC
  dsimp only
  have h : (-(((d.2.2 + d'.2.2 : ℕ) : ℂ) / 2)) = (-((d.2.2 : ℂ) / 2)) + (-((d'.2.2 : ℂ) / 2)) := by
    push_cast; ring
  rw [h, Complex.cpow_add _ _ (base_ne_zero ζ), pow_add, pow_add]
  ring

private theorem ofReal_ρR (ζ : ℂ) :
    ((ρR ζ : ℝ) : ℂ) = (((1 + ‖ζ‖ ^ 2 : ℝ)) : ℂ) ^ (-(((1 : ℕ) : ℂ) / 2)) := by
  have hb : (0 : ℝ) ≤ 1 + ‖ζ‖ ^ 2 := by positivity
  unfold ρR bR
  rw [Complex.ofReal_cpow hb]
  congr 1
  norm_num

private def IsMonoComb (f : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (d : ι → ℕ × ℕ × ℕ),
    (∀ i, (d i).1 + (d i).2.1 ≤ (d i).2.2) ∧ ∀ ζ : ℂ, f ζ = ∑ i, c i * monoC (d i) ζ

private theorem isMonoComb_zero : IsMonoComb (fun _ => (0 : ℂ)) :=
  ⟨PEmpty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun _ => by simp⟩

private theorem isMonoComb_one : IsMonoComb (fun _ => (1 : ℂ)) :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => (0, 0, 0), fun _ => by simp, fun ζ => by
    simp [monoC_zero]⟩

private theorem IsMonoComb.add {f g : ℂ → ℂ} (hf : IsMonoComb f) (hg : IsMonoComb g) :
    IsMonoComb (fun ζ => f ζ + g ζ) := by
  obtain ⟨ι, hι, c, d, hd, hf⟩ := hf
  obtain ⟨ι', hι', c', d', hd', hg⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim d d', fun i => ?_, fun ζ => ?_⟩
  · cases i with
    | inl i => exact hd i
    | inr i => exact hd' i
  · show f ζ + g ζ = _
    rw [hf ζ, hg ζ, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]

private theorem IsMonoComb.const_mul {f : ℂ → ℂ} (a : ℂ) (hf : IsMonoComb f) :
    IsMonoComb (fun ζ => a * f ζ) := by
  obtain ⟨ι, hι, c, d, hd, hf⟩ := hf
  refine ⟨ι, hι, fun i => a * c i, d, hd, fun ζ => ?_⟩
  show a * f ζ = _
  rw [hf ζ, Finset.mul_sum]
  simp only [mul_assoc]

private theorem IsMonoComb.mul {f g : ℂ → ℂ} (hf : IsMonoComb f) (hg : IsMonoComb g) :
    IsMonoComb (fun ζ => f ζ * g ζ) := by
  obtain ⟨ι, hι, c, d, hd, hf⟩ := hf
  obtain ⟨ι', hι', c', d', hd', hg⟩ := hg
  refine ⟨ι × ι', inferInstance, fun p => c p.1 * c' p.2,
    fun p => ((d p.1).1 + (d' p.2).1, (d p.1).2.1 + (d' p.2).2.1, (d p.1).2.2 + (d' p.2).2.2),
    fun p => ?_, fun ζ => ?_⟩
  · have h1 := hd p.1
    have h2 := hd' p.2
    dsimp only
    omega
  · show f ζ * g ζ = _
    rw [hf ζ, hg ζ, Fintype.sum_prod_type]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [← monoC_mul]
    ring

private theorem isMonoComb_functional (ℓ : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ) :
    IsMonoComb (fun ζ => ℓ (uMat ζ)) := by

  set E₀ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0] with hE₀
  set E₁ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1] with hE₁
  set E₂ : Matrix (Fin 2) (Fin 2) ℂ := !![-Complex.I, 0; 0, Complex.I] with hE₂
  have hdecomp : ∀ ζ : ℂ, uMat ζ = ρR ζ • (E₀ + ζ.re • E₁ + ζ.im • E₂) := by
    intro ζ
    ext i j
    fin_cases i <;> fin_cases j <;> refine Complex.ext ?_ ?_ <;> simp [uMat, hE₀, hE₁, hE₂]
  have hval : ∀ ζ : ℂ, ℓ (uMat ζ) = ((ρR ζ : ℝ) : ℂ) *
      (ℓ E₀ + ((ζ.re : ℝ) : ℂ) * ℓ E₁ + ((ζ.im : ℝ) : ℂ) * ℓ E₂) := by
    intro ζ
    rw [hdecomp ζ]
    simp only [map_smul, map_add, Complex.real_smul]
  have hre : ∀ ζ : ℂ, ((ζ.re : ℝ) : ℂ) = (1 / 2 : ℂ) * ζ + (1 / 2 : ℂ) * (starRingEnd ℂ) ζ := by
    intro ζ
    have h := Complex.add_conj ζ
    push_cast at h
    linear_combination (-(1 / 2 : ℂ)) * h
  have him : ∀ ζ : ℂ, ((ζ.im : ℝ) : ℂ)
      = (-(Complex.I / 2)) * ζ + (Complex.I / 2) * (starRingEnd ℂ) ζ := by
    intro ζ
    have h := Complex.sub_conj ζ
    push_cast at h
    linear_combination (Complex.I / 2) * h + ((ζ.im : ℝ) : ℂ) * Complex.I_sq
  refine ⟨Fin 3, inferInstance,
    ![ℓ E₀, (1 / 2 : ℂ) * ℓ E₁ + (-(Complex.I / 2)) * ℓ E₂, (1 / 2 : ℂ) * ℓ E₁ + (Complex.I / 2) * ℓ E₂],
    ![(0, 0, 1), (1, 0, 1), (0, 1, 1)], ?_, fun ζ => ?_⟩
  · intro i
    fin_cases i <;> simp
  · show ℓ (uMat ζ) = _
    rw [hval ζ, hre ζ, him ζ, Fin.sum_univ_three]
    simp [monoC, ofReal_ρR]
    ring

private theorem isMonoComb_list_prod :
    ∀ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ),
      IsMonoComb (fun ζ => (l.map fun ℓ => ℓ (uMat ζ)).prod) := by
  intro l
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact isMonoComb_one
  | cons ℓ l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (isMonoComb_functional ℓ).mul ih

private theorem isMonoComb_of_mem_polySpan {P : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hP : P ∈ Submodule.span ℂ
      {Q : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
        ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), Q = fun m => (l.map (fun ℓ => ℓ m)).prod}) :
    IsMonoComb (fun ζ => P (uMat ζ)) := by
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨l, rfl⟩ := hQ
    exact isMonoComb_list_prod l
  | zero => exact isMonoComb_zero
  | add Q₁ Q₂ _ _ ih₁ ih₂ =>
    simp only [Pi.add_apply]
    exact ih₁.add ih₂
  | smul a Q _ ih =>
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ih.const_mul a

end MonoClass
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section UFn

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

omit [NumberField F] in
private theorem unitAt_mul (hw : w.IsComplex) (k k' : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) :
    unitAt hw (k * k') = unitAt hw k * unitAt hw k' := by
  simp only [unitAt, unitToGL, map_mul]

private theorem unitAt_incl_mem (hw : w.IsComplex) (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) :
    adelicArchGLInclAt F w (unitAt hw k) ∈ AutomorphicForm.archRowIsometrySubgroup F w :=
  Subgroup.mem_map_of_mem _
    ((AutomorphicForm.WindowedSiegel.mem_rowIsometrySubgroup_iff).mpr (isRowIsometry_unitAt hw k))

private theorem uAt_incl_mem (hw : w.IsComplex) (ζ : ℂ) :
    adelicArchGLInclAt F w (uAt hw ζ) ∈ AutomorphicForm.archRowIsometrySubgroup F w :=
  unitAt_incl_mem hw (uUnit ζ)

private def uFn (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F) :
    ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ :=
  fun k => φ (y * adelicArchGLInclAt F w (unitAt hw k))

private theorem continuous_uFn (hw : w.IsComplex) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (y : AdelicGL2 (𝓞 F) F) : Continuous (uFn hw φ y) :=
  hφc.comp (continuous_const.mul ((continuous_adelicArchGLInclAt F w).comp (continuous_unitAt hw)))

private def uRestrictₗ (hw : w.IsComplex) (y : AdelicGL2 (𝓞 F) F) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) where
  toFun ψ := fun k => ψ (y * adelicArchGLInclAt F w (unitAt hw k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem uRestrictₗ_apply (hw : w.IsComplex) (y : AdelicGL2 (𝓞 F) F) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (k : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) :
    uRestrictₗ hw y ψ k = ψ (y * adelicArchGLInclAt F w (unitAt hw k)) := rfl

private theorem uFn_translates_mem_span (hw : w.IsComplex) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hK : IsArchKFiniteAt F w φ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun x => uFn hw φ y (x * k))
          ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hK
  refine ⟨s.image (uRestrictₗ hw y), fun k => ?_⟩
  have e : (fun x => uFn hw φ y (x * k))
      = uRestrictₗ hw y (fun g => φ (g * adelicArchGLInclAt F w (unitAt hw k))) := by
    funext x
    simp only [uFn, uRestrictₗ_apply, unitAt_mul, map_mul, mul_assoc]
  rw [e, Finset.coe_image]
  have hm := Submodule.mem_map_of_mem (f := uRestrictₗ hw y)
    (hs (adelicArchGLInclAt F w (unitAt hw k)) (unitAt_incl_mem hw k))
  rw [Submodule.map_span] at hm
  exact hm

private theorem isMonoComb_sample (hw : w.IsComplex) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hK : IsArchKFiniteAt F w φ) (y : AdelicGL2 (𝓞 F) F) :
    IsMonoComb (fun ζ => φ (y * adelicArchGLInclAt F w (uAt hw ζ))) := by
  obtain ⟨P, hP, hPk⟩ := Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (uFn hw φ y) (continuous_uFn hw hφc y) (uFn_translates_mem_span hw hK y)
  have e : (fun ζ => φ (y * adelicArchGLInclAt F w (uAt hw ζ))) = fun ζ => P (uMat ζ) := by
    funext ζ
    exact hPk (uUnit ζ)
  rw [e]
  exact isMonoComb_of_mem_polySpan hP

end UFn
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section UniformComplex

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

private theorem uniform_expansion_complex (hw : w.IsComplex) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) :
    ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ) (d : ι → ℕ × ℕ × ℕ),
      (∀ i : ι, Continuous (Cf i) ∧ IsArchKFinite F (Cf i) ∧ IsKfSmooth F (Cf i)) ∧
      (∀ i : ι, (d i).1 + (d i).2.1 ≤ (d i).2.2) ∧
      ∀ (y : AdelicGL2 (𝓞 F) F) (ζ : ℂ),
        φ (y * adelicArchGLInclAt F w (uAt hw ζ)) = ∑ i : ι, Cf i y * monoC (d i) ζ := by
  haveI : FiniteDimensional ℂ (transSpan w φ) := finiteDimensional_transSpan (hφK w)
  obtain ⟨t, e, he, hrep⟩ := exists_eval_coords (transSpan w φ)

  have hV : ∀ ζ : ℂ, (fun y => φ (y * adelicArchGLInclAt F w (uAt hw ζ))) ∈ transSpan w φ := fun ζ =>
    Submodule.subset_span ⟨⟨_, uAt_incl_mem hw ζ⟩, rfl⟩
  have hpt : ∀ (ζ : ℂ) (y : AdelicGL2 (𝓞 F) F),
      φ (y * adelicArchGLInclAt F w (uAt hw ζ))
        = ∑ z : ↥t, φ ((z : AdelicGL2 (𝓞 F) F) * adelicArchGLInclAt F w (uAt hw ζ)) * e z y := by
    intro ζ y
    have h := congrFun (hrep _ (hV ζ)) y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h

  have hsamp : ∀ z : ↥t, ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (d : ι → ℕ × ℕ × ℕ),
      (∀ i, (d i).1 + (d i).2.1 ≤ (d i).2.2) ∧
      ∀ ζ : ℂ, φ ((z : AdelicGL2 (𝓞 F) F) * adelicArchGLInclAt F w (uAt hw ζ)) = ∑ i, c i * monoC (d i) ζ :=
    fun z => isMonoComb_sample hw hφc (hφK w) (z : AdelicGL2 (𝓞 F) F)
  choose ι hι c d hd hexp using hsamp
  refine ⟨(Σ z : ↥t, ι z), inferInstance, fun p => fun y => c p.1 p.2 * e p.1 y, fun p => d p.1 p.2,
    fun p => ?_, fun p => hd p.1 p.2, fun y ζ => ?_⟩
  · have hmem : (c p.1 p.2 • e p.1) ∈ transSpan w φ := Submodule.smul_mem _ _ (he p.1)
    have hfun : (fun y => c p.1 p.2 * e p.1 y) = c p.1 p.2 • e p.1 := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := continuous_of_mem_transSpan hφc hmem
    have h2 := isArchKFinite_of_mem_transSpan hφK hmem
    have h3 := isKfSmooth_of_mem_transSpan hφf hmem
    rw [← hfun] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rw [hpt ζ y, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hexp z ζ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    ring

end UniformComplex
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section MultiComplex

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

private def monoProd (L : List {w : InfinitePlace F // w.IsComplex})
    (dd : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ) (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    ℂ :=
  (L.map fun w => monoC (dd w) (ζ w)).prod

omit [NumberField F] in
private theorem monoProd_nil (dd : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) : monoProd [] dd ζ = 1 := by
  unfold monoProd
  rw [List.map_nil, List.prod_nil]

omit [NumberField F] in
private theorem monoProd_cons (w : {w : InfinitePlace F // w.IsComplex})
    (L : List {w : InfinitePlace F // w.IsComplex})
    (dd : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ) (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    monoProd (w :: L) dd ζ = monoC (dd w) (ζ w) * monoProd L dd ζ := by
  unfold monoProd
  rw [List.map_cons, List.prod_cons]

private theorem multi_complex_expansion {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) :
    ∀ L : List {w : InfinitePlace F // w.IsComplex}, L.Nodup →
      ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ)
        (dd : ι → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ),
        (∀ j : ι, Continuous (Cf j) ∧ IsArchKFinite F (Cf j) ∧ IsKfSmooth F (Cf j)) ∧
        (∀ (j : ι) (w : {w : InfinitePlace F // w.IsComplex}), (dd j w).1 + (dd j w).2.1 ≤ (dd j w).2.2) ∧
        ∀ (y : AdelicGL2 (𝓞 F) F) (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ),
          φ (y * uProd L ζ) = ∑ j : ι, Cf j y * monoProd L (dd j) ζ := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨Unit, inferInstance, fun _ => φ, fun _ _ => (0, 0, 0), fun _ => ⟨hφc, hφK, hφf⟩,
      fun _ _ => by simp, fun y ζ => ?_⟩
    rw [uProd_nil, mul_one]
    simp [monoProd_nil]
  | cons w₀ L ih =>
    intro hL
    obtain ⟨hw₀L, hLnd⟩ := List.nodup_cons.mp hL
    obtain ⟨ι, hι, Cf, dd, hCf, hdd, hexp⟩ := ih hLnd
    choose ι' hι' Cf' d' hCf' hd' hexp' using
      fun j : ι => uniform_expansion_complex w₀.2 (hCf j).1 (hCf j).2.1 (hCf j).2.2
    refine ⟨(Σ j : ι, ι' j), inferInstance, fun p => Cf' p.1 p.2,
      fun p w => if w = w₀ then d' p.1 p.2 else dd p.1 w, fun p => hCf' p.1 p.2, fun p w => ?_,
      fun y ζ => ?_⟩
    · by_cases hw : w = w₀
      · dsimp only
        rw [if_pos hw]
        exact hd' p.1 p.2
      · dsimp only
        rw [if_neg hw]
        exact hdd p.1 w
    · rw [uProd_cons, ← mul_assoc, hexp (y * adelicArchGLInclAt F w₀.1 (uAt w₀.2 (ζ w₀))) ζ]
      simp_rw [hexp']
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [monoProd_cons, if_pos rfl, mul_assoc]
      congr 2
      unfold monoProd
      refine list_prod_map_congr L fun w hw => ?_
      have hne : ¬ w = w₀ := fun h => hw₀L (h ▸ hw)
      dsimp only
      rw [if_neg hne]

end MultiComplex
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end ComplexPort
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section Glue

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain"
open AutomorphicForm BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa
open scoped Classical

private theorem fourier_θR (t : ℝ) (n : ℤ) :
    (fourier n ((θR t : ℝ) : AddCircle (2 * Real.pi)) : ℂ)
      = ((((t : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ)) ^ (-n) := by
  set z : ℂ := ⟨t, 1⟩ with hz
  have hz0 : z ≠ 0 := zc_ne_zero t
  have hzn : ‖z‖ = Real.sqrt (1 + t ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg z), ← Complex.normSq_eq_norm_sq, hz, Complex.normSq_mk]
    congr 1
    ring
  have hzadd : z = (t : ℂ) + Complex.I := by
    rw [hz, Complex.mk_eq_add_mul_I]
    simp
  have hexp : Complex.exp (((θR t : ℝ) : ℂ) * Complex.I) = z / (‖z‖ : ℂ) := by
    have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz0)
    rw [eq_div_iff hn, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I z
  have hT : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hr0 : ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have htI : ((t : ℂ) - Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
  rw [fourier_coe_apply]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((θR t : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ))
      = (z / (‖z‖ : ℂ)) ^ n := by
    have e1 : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((θR t : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ))
        = (n : ℂ) * (((θR t : ℝ) : ℂ) * Complex.I) := by
      rw [div_eq_iff hT]
      push_cast
      ring
    rw [e1, Complex.exp_int_mul, hexp]
  refine h1.trans ?_
  rw [hzn, ← inv_zpow']
  congr 1
  rw [inv_div, div_eq_div_iff hr0 htI, hzadd, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 1 + t ^ 2)]
  push_cast
  linear_combination (-1 : ℂ) * Complex.I_sq

variable {F : Type} [Field F] [NumberField F]

private theorem multi_real_expansion_smooth {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) :
    ∀ L : List {w : InfinitePlace F // w.IsReal}, L.Nodup →
      ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ)
        (kd : ι → {w : InfinitePlace F // w.IsReal} → ℤ),
        (∀ j : ι, Continuous (Cf j) ∧ IsArchKFinite F (Cf j) ∧ IsKfSmooth F (Cf j)) ∧
        ∀ (y : AdelicGL2 (𝓞 F) F) (θ : {w : InfinitePlace F // w.IsReal} → ℝ),
          φ (y * rotProd L θ) = ∑ j : ι, Cf j y * charProd L (kd j) θ := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨Unit, inferInstance, fun _ => φ, fun _ _ => 0, fun _ => ⟨hφc, hφK, hφf⟩, fun y θ => ?_⟩
    rw [rotProd_nil, mul_one]
    simp [charProd_nil]
  | cons w₀ L ih =>
    intro hL
    obtain ⟨hw₀L, hLnd⟩ := List.nodup_cons.mp hL
    obtain ⟨ι, hι, Cf, kd, hCf, hexp⟩ := ih hLnd
    choose tfin htfin using fun j : ι => (uniform_expansion w₀.2 (hCf j).1 (hCf j).2.1).2
    have hcoef : ∀ (j : ι) (n : ℤ),
        Continuous (coeffFn w₀.2 (Cf j) n) ∧ IsArchKFinite F (coeffFn w₀.2 (Cf j) n)
          ∧ IsKfSmooth F (coeffFn w₀.2 (Cf j) n) :=
      fun j n => ⟨((uniform_expansion w₀.2 (hCf j).1 (hCf j).2.1).1 n).1,
        ((uniform_expansion w₀.2 (hCf j).1 (hCf j).2.1).1 n).2, isKfSmooth_coeffFn w₀.2 (hCf j).2.2 n⟩
    refine ⟨(Σ j : ι, ↥(tfin j)), inferInstance,
      fun p => coeffFn w₀.2 (Cf p.1) (p.2 : ℤ),
      fun p w => if w = w₀ then (p.2 : ℤ) else kd p.1 w,
      fun p => hcoef p.1 p.2, fun y θ => ?_⟩
    rw [rotProd_cons, ← mul_assoc, hexp (y * adelicArchGLInclAt F w₀.1 (rotAt w₀.2 (θ w₀))) θ]
    simp_rw [htfin]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_coe_sort (s := tfin j)]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [charProd_cons, if_pos rfl, mul_assoc]
    congr 2
    unfold charProd
    refine list_prod_map_congr L fun w hw => ?_
    have hne : ¬ w = w₀ := fun h => hw₀L (h ▸ hw)
    dsimp only
    rw [if_neg hne]

variable (F)

private theorem charProd_θx_eq (x : AdeleRing (𝓞 F) F) (kd : {w : InfinitePlace F // w.IsReal} → ℤ) :
    charProd (Lr F) kd (θx F x)
      = ∏ i : {w : InfinitePlace F // w.IsReal},
          ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ)
                - Complex.I)
              / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                  : ℝ) : ℂ)) ^ (-(kd i)) := by
  unfold charProd Lr
  rw [Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [θx, xr, fourier_θR]

private theorem monoProd_zC_eq (x : AdeleRing (𝓞 F) F)
    (dd : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ) :
    monoProd (Lc F) dd (zC F x)
      = ∏ w : {w : InfinitePlace F // w.IsComplex},
          Completion.extensionEmbedding w.1 (x.1 w.1) ^ (dd w).1
            * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1)) ^ (dd w).2.1
            * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                ^ (-(((dd w).2.2 : ℂ) / 2)) := by
  unfold monoProd Lc
  rw [Finset.prod_map_toList]
  rfl

end Glue
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section Torus

p2m_open "Matrix NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain"
open AutomorphicForm BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa Filter Topology
open scoped ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

private def expI (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

private theorem expI_ne_zero (θ : ℝ) : expI θ ≠ 0 := Complex.exp_ne_zero _

private theorem norm_expI (θ : ℝ) : ‖expI θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

private theorem conj_expI (θ : ℝ) : conj (expI θ) = (expI θ)⁻¹ := by
  unfold expI
  rw [← Complex.exp_conj, ← Complex.exp_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

private theorem expI_add (θ₁ θ₂ : ℝ) : expI (θ₁ + θ₂) = expI θ₁ * expI θ₂ := by
  unfold expI
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

private def tMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(expI θ)⁻¹, 0; 0, expI θ]

private theorem tMat_mul_star (θ : ℝ) : tMat θ * star (tMat θ) = 1 := by
  have h1 : (expI θ)⁻¹ * (conj (expI θ))⁻¹ = 1 := by
    rw [conj_expI, inv_inv, inv_mul_cancel₀ (expI_ne_zero θ)]
  have h2 : expI θ * conj (expI θ) = 1 := by
    rw [conj_expI, mul_inv_cancel₀ (expI_ne_zero θ)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, h1, h2, Fin.zero_eta, Fin.mk_one]

private theorem tMat_mem (θ : ℝ) : tMat θ ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (tMat_mul_star θ)

private def tUnit (θ : ℝ) : ↥(Matrix.unitaryGroup (Fin 2) ℂ) := ⟨tMat θ, tMat_mem θ⟩

private theorem norm_ray {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : ‖(R : ℂ) * expI θ‖ = R := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, norm_expI, mul_one]

private theorem ρR_ray {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : ρR ((R : ℂ) * expI θ) = (1 + R ^ 2) ^ (-(1 / 2 : ℝ)) := by
  unfold ρR bR
  rw [norm_ray hR]

private theorem tendsto_uUnit_ray
    (h0 : Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0))
    (h1 : Tendsto (fun R : ℝ => R * (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) atTop (𝓝 1)) (θ : ℝ) :
    Tendsto (fun R : ℝ => uUnit ((R : ℂ) * expI θ)) atTop (𝓝 (tUnit θ)) := by
  rw [tendsto_subtype_rng]
  change Tendsto (fun R : ℝ => uMat ((R : ℂ) * expI θ)) atTop (𝓝 (tMat θ))
  have hρ : Tendsto (fun R : ℝ => ((ρR ((R : ℂ) * expI θ) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp h0
    rw [Complex.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simp only [Function.comp_apply, ρR_ray hR]
  have hρR : Tendsto (fun R : ℝ => ((ρR ((R : ℂ) * expI θ) : ℝ) : ℂ) * (R : ℂ)) atTop (𝓝 1) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp h1
    rw [Complex.ofReal_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simp only [Function.comp_apply, ρR_ray hR, Complex.ofReal_mul, mul_comm]
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  ·
    simp only [Fin.zero_eta, tMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have h := hρR.mul_const ((expI θ)⁻¹)
    rw [one_mul] at h
    refine h.congr' (Eventually.of_forall fun R => ?_)
    simp only [uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_mul, Complex.conj_ofReal, conj_expI]
    ring
  ·
    simp only [Fin.zero_eta, Fin.mk_one, tMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have h := hρ.neg
    rw [neg_zero] at h
    refine h.congr' (Eventually.of_forall fun R => ?_)
    simp only [uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  ·
    simp only [Fin.zero_eta, Fin.mk_one, tMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    refine hρ.congr' (Eventually.of_forall fun R => ?_)
    simp only [uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  ·
    simp only [Fin.mk_one, tMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have h := hρR.mul_const (expI θ)
    rw [one_mul] at h
    refine h.congr' (Eventually.of_forall fun R => ?_)
    simp only [uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring

private def torusAt (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w.1 (unitAt w.2 (tUnit θ))

private def circleUnit (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) : (w.1.Completion)ˣ :=
  Units.mk0 ((ringEquivComplexOfIsComplex w.2).symm (expI θ))
    ((map_ne_zero_iff _ (ringEquivComplexOfIsComplex w.2).symm.injective).2 (expI_ne_zero θ))

omit [NumberField F] in
private theorem circleUnit_add (w : {w : InfinitePlace F // w.IsComplex}) (θ₁ θ₂ : ℝ) :
    circleUnit w (θ₁ + θ₂) = circleUnit w θ₁ * circleUnit w θ₂ := by
  refine Units.ext ?_
  show (ringEquivComplexOfIsComplex w.2).symm (expI (θ₁ + θ₂))
    = (ringEquivComplexOfIsComplex w.2).symm (expI θ₁) * (ringEquivComplexOfIsComplex w.2).symm (expI θ₂)
  rw [expI_add, map_mul]

private theorem tendsto_incl_uAt_ray
    (h0 : Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0))
    (h1 : Tendsto (fun R : ℝ => R * (1 + R ^ 2) ^ (-(1 / 2 : ℝ))) atTop (𝓝 1))
    (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    Tendsto (fun R : ℝ => adelicArchGLInclAt F w.1 (uAt w.2 ((R : ℂ) * expI θ))) atTop (𝓝 (torusAt w θ)) :=
  ((continuous_adelicArchGLInclAt F w.1).comp (continuous_unitAt w.2)).continuousAt.tendsto.comp
    (tendsto_uUnit_ray h0 h1 θ)

private theorem glFin_torusAt (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    glFin (𝓞 F) F (torusAt w θ) = 1 := by
  ext i j
  rfl

private theorem torusAt_apply_fst_self (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) (i j : Fin 2) :
    (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w.1
      = (ringEquivComplexOfIsComplex w.2).symm (tMat θ i j) := by
  have h : (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w.1
      = (projArch F w.1).mapMatrix
          ((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j := by
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply]
  rw [h]
  unfold torusAt
  rw [projArch_incl_self, unitAt, glEquivOfRingEquiv_apply_entry, unitToGL_coe]
  rfl

private theorem torusAt_apply_fst_of_ne (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) (i j : Fin 2)
    {v : InfinitePlace F} (hv : v ≠ w.1) :
    (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 v
      = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  have h : (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 v
      = (projArch F v).mapMatrix
          ((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j := by
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projArch_apply]
  rw [h]
  unfold torusAt
  rw [projArch_incl_of_ne F hv]

private theorem torusAt_apply_snd (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) (i j : Fin 2) :
    (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by
  have h : (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = (projFin F).mapMatrix
          ((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j := by
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, projFin_apply]
  rw [h]
  unfold torusAt
  rw [projFin_incl]

private theorem torusAt_mem_adelicBorel (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    torusAt w θ ∈ adelicBorel (𝓞 F) F := by
  show (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) = 0
  refine Prod.ext (funext fun v => ?_) ?_
  · by_cases hv : v = w.1
    · subst hv
      rw [torusAt_apply_fst_self]
      show (ringEquivComplexOfIsComplex w.2).symm (tMat θ 1 0) = 0
      simp [tMat]
    · rw [torusAt_apply_fst_of_ne w θ 1 0 hv]
      show (1 : Matrix (Fin 2) (Fin 2) v.Completion) 1 0 = 0
      exact Matrix.one_apply_ne (by decide)
  · rw [torusAt_apply_snd]
    show (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0
    exact Matrix.one_apply_ne (by decide)

private theorem borelDiagFst_torusAt (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    borelDiagFst (⟨torusAt w θ, torusAt_mem_adelicBorel w θ⟩ : ↥(adelicBorel (𝓞 F) F))
      = NumberField.TateGlobal.archUnitHom w.1 (circleUnit w θ)⁻¹ := by
  refine Units.ext ?_
  change (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0)
    = ((NumberField.AdelicVolume.archCentralUnit F w.1 (circleUnit w θ)⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
        : AdeleRing (𝓞 F) F)
  refine Prod.ext (funext fun v => ?_) ?_
  · by_cases hv : v = w.1
    · subst hv
      rw [torusAt_apply_fst_self, NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_inv_eq_inv_val]
      show (ringEquivComplexOfIsComplex w.2).symm ((expI θ)⁻¹)
        = ((ringEquivComplexOfIsComplex w.2).symm (expI θ))⁻¹
      rw [map_inv₀]
    · rw [torusAt_apply_fst_of_ne w θ 0 0 hv, NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hv]
      simp
  · rw [torusAt_apply_snd, NumberField.AdelicVolume.archCentralUnit_snd]
    simp

private theorem borelDiagSnd_torusAt (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    borelDiagSnd (⟨torusAt w θ, torusAt_mem_adelicBorel w θ⟩ : ↥(adelicBorel (𝓞 F) F))
      = NumberField.TateGlobal.archUnitHom w.1 (circleUnit w θ) := by
  refine Units.ext ?_
  change (((torusAt w θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)
    = ((NumberField.AdelicVolume.archCentralUnit F w.1 (circleUnit w θ) : (AdeleRing (𝓞 F) F)ˣ)
        : AdeleRing (𝓞 F) F)
  refine Prod.ext (funext fun v => ?_) ?_
  · by_cases hv : v = w.1
    · subst hv
      rw [torusAt_apply_fst_self, NumberField.AdelicVolume.archCentralUnit_fst_self]
      rfl
    · rw [torusAt_apply_fst_of_ne w θ 1 1 hv, NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hv]
      simp
  · rw [torusAt_apply_snd, NumberField.AdelicVolume.archCentralUnit_snd]
    simp

private def torusBracket (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : {w : InfinitePlace F // w.IsComplex})
    (θ : ℝ) : ℂ :=
  ((χ₁ (NumberField.TateGlobal.archUnitHom w.1 (circleUnit w θ)⁻¹) : ℂˣ) : ℂ)
    * ((χ₂ (NumberField.TateGlobal.archUnitHom w.1 (circleUnit w θ)) : ℂˣ) : ℂ)

private theorem torusBracket_add (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) (θ₁ θ₂ : ℝ) :
    torusBracket χ₁ χ₂ w (θ₁ + θ₂) = torusBracket χ₁ χ₂ w θ₁ * torusBracket χ₁ χ₂ w θ₂ := by
  unfold torusBracket
  rw [circleUnit_add, mul_inv, map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

private theorem torusBracket_add_two_pi (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    torusBracket χ₁ χ₂ w (θ + 2 * Real.pi) = torusBracket χ₁ χ₂ w θ := by
  have h : circleUnit w (θ + 2 * Real.pi) = circleUnit w θ := by
    refine Units.ext ?_
    show (ringEquivComplexOfIsComplex w.2).symm (expI (θ + 2 * Real.pi))
      = (ringEquivComplexOfIsComplex w.2).symm (expI θ)
    rw [expI_add]
    unfold expI
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I, mul_one]
  unfold torusBracket
  rw [h]

omit [NumberField F] in

private theorem exists_circleUnit_eq (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ)
    (hu : ‖extensionEmbedding w.1 (u : w.1.Completion)‖ = 1) : ∃ θ : ℝ, circleUnit w θ = u := by
  refine ⟨Complex.arg (extensionEmbedding w.1 (u : w.1.Completion)), Units.ext ?_⟩
  apply (ringEquivComplexOfIsComplex w.2).injective
  show ringEquivComplexOfIsComplex w.2 ((ringEquivComplexOfIsComplex w.2).symm (expI _))
    = extensionEmbedding w.1 (u : w.1.Completion)
  rw [RingEquiv.apply_symm_apply]
  unfold expI
  have h := Complex.norm_mul_exp_arg_mul_I (extensionEmbedding w.1 (u : w.1.Completion))
  rwa [hu, Complex.ofReal_one, one_mul] at h

private theorem exists_torusBracket_ne_one (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ)
    (hu : ‖extensionEmbedding w.1 (u : w.1.Completion)‖ = 1)
    (hne : (((χ₁ * χ₂⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) ≠ 1) :
    ∃ θ : ℝ, torusBracket χ₁ χ₂ w θ ≠ 1 := by
  obtain ⟨θ, hθ⟩ := exists_circleUnit_eq w u hu
  refine ⟨θ, fun h => hne ?_⟩
  unfold torusBracket at h
  rw [hθ, map_inv, map_inv, Units.val_inv_eq_inv_val] at h
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  have hx : ((χ₁ (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hy : ((χ₂ (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [inv_mul_eq_one₀ hx] at h
  rw [mul_inv_eq_one₀ hy]
  exact h

private def torusBracketCircle (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) : AddCircle (2 * Real.pi) → ℂ :=
  Function.Periodic.lift (f := torusBracket χ₁ χ₂ w) (c := 2 * Real.pi) (torusBracket_add_two_pi χ₁ χ₂ w)

private theorem torusBracketCircle_coe (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ) :
    torusBracketCircle χ₁ χ₂ w ((θ : ℝ) : AddCircle (2 * Real.pi)) = torusBracket χ₁ χ₂ w θ :=
  Function.Periodic.lift_coe _ _

private theorem torusBracketCircle_add (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) (θ₁ θ₂ : AddCircle (2 * Real.pi)) :
    torusBracketCircle χ₁ χ₂ w (θ₁ + θ₂) = torusBracketCircle χ₁ χ₂ w θ₁ * torusBracketCircle χ₁ χ₂ w θ₂ := by
  induction θ₁ using QuotientAddGroup.induction_on with
  | H a =>
    induction θ₂ using QuotientAddGroup.induction_on with
    | H b =>
      rw [← QuotientAddGroup.mk_add]
      exact (torusBracketCircle_coe χ₁ χ₂ w (a + b)).trans
        ((torusBracket_add χ₁ χ₂ w a b).trans
          (by rw [torusBracketCircle_coe, torusBracketCircle_coe]))

private theorem apply_torusAt_mul {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (w : {w : InfinitePlace F // w.IsComplex}) (θ : ℝ)
    (g : AdelicGL2 (𝓞 F) F) :
    φ (torusAt w θ * g) = torusBracket χ₁ χ₂ w θ * φ g := by
  rw [hφ (torusAt w θ) (torusAt_mem_adelicBorel w θ) g, borelDiagFst_torusAt, borelDiagSnd_torusAt]
  rfl

open scoped Classical in

private theorem uProd_update_of_not_mem (w : {w : InfinitePlace F // w.IsComplex}) (z : ℂ) :
    ∀ (L : List {w : InfinitePlace F // w.IsComplex}), w ∉ L →
      ∀ ζ : {w : InfinitePlace F // w.IsComplex} → ℂ, uProd L (Function.update ζ w z) = uProd L ζ := by
  intro L
  induction L with
  | nil => intro _ ζ; rw [uProd_nil, uProd_nil]
  | cons w₁ L ih =>
    intro hw ζ
    have hw₁ : w₁ ≠ w := fun h => hw (h ▸ List.mem_cons_self)
    rw [uProd_cons, uProd_cons, Function.update_of_ne hw₁, ih (fun h => hw (List.mem_cons_of_mem _ h)) ζ]

open scoped Classical in

private theorem uProd_update_eq (w : {w : InfinitePlace F // w.IsComplex}) (z : ℂ) :
    ∀ (L : List {w : InfinitePlace F // w.IsComplex}), L.Nodup → w ∈ L →
      ∀ ζ : {w : InfinitePlace F // w.IsComplex} → ℂ,
        uProd L (Function.update ζ w z) = adelicArchGLInclAt F w.1 (uAt w.2 z) * uProd (L.erase w) ζ := by
  intro L
  induction L with
  | nil => intro _ h; exact (List.not_mem_nil h).elim
  | cons w₀ L ih =>
    intro hL hw ζ
    obtain ⟨hw₀L, hLnd⟩ := List.nodup_cons.mp hL
    by_cases hww : w = w₀
    · subst hww
      rw [uProd_cons, Function.update_self, List.erase_cons_head, uProd_update_of_not_mem _ _ L hw₀L ζ]
    · have hwL : w ∈ L := (List.mem_cons.mp hw).resolve_left hww
      rw [uProd_cons, Function.update_of_ne (Ne.symm hww), ih hLnd hwL ζ,
        List.erase_cons_tail (fun h => hww (beq_iff_eq.mp h).symm), uProd_cons, ← mul_assoc, ← mul_assoc,
        incl_comm F (fun h => hww (Subtype.ext h).symm)]

end Torus
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

section InducedExpansion

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain"
open AutomorphicForm BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa Filter Topology
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

private theorem monoProd_Lc_eq_monoPi (dd : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    monoProd (Lc F) dd ζ = CircleParity.monoPi dd ζ := by
  unfold monoProd Lc CircleParity.monoPi
  rw [Finset.prod_map_toList]
  rfl

private theorem complex_expansion_drop {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ)
    (hφs : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) :
    ∃ (ι : Type) (_ : Fintype ι) (Cf : ι → AdelicGL2 (𝓞 F) F → ℂ)
      (dd : ι → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ),
      (∀ i : ι, IsKfSmooth F (Cf i)) ∧
      (∀ (i : ι) (w : {w : InfinitePlace F // w.IsComplex}), (dd i w).1 + (dd i w).2.1 ≤ (dd i w).2.2) ∧
      (∀ (i : ι) (w : {w : InfinitePlace F // w.IsComplex}),
        (∃ θ : ℝ, torusBracket χ₁ χ₂ w θ ≠ 1) → ¬ CircleParity.IsPoleType (dd i w)) ∧
      ∀ (g : AdelicGL2 (𝓞 F) F), glArch (𝓞 F) F g = 1 →
        ∀ ζ : {w : InfinitePlace F // w.IsComplex} → ℂ,
          φ (g * uProd (Lc F) ζ) = ∑ i : ι, Cf i g * CircleParity.monoPi (dd i) ζ := by
  obtain ⟨ι₀, _, Cf₀, dd₀, hCf₀, hdd₀, hexp₀⟩ := multi_complex_expansion hφc hφK hφf (Lc F) (Lc_nodup F)

  let P : Type := {g : AdelicGL2 (𝓞 F) F // glArch (𝓞 F) F g = 1}
  let Φ : P → ({w : InfinitePlace F // w.IsComplex} → ℂ) → ℂ := fun p ζ => φ (p.1 * uProd (Lc F) ζ)
  have hΦ : ∀ (p : P) ζ, Φ p ζ = ∑ i, Cf₀ i p.1 * CircleParity.monoPi (dd₀ i) ζ := by
    intro p ζ
    simp only [Φ, hexp₀, monoProd_Lc_eq_monoPi]

  let S : List {w : InfinitePlace F // w.IsComplex} :=
    (Lc F).filter fun w => decide (∃ θ : ℝ, torusBracket χ₁ χ₂ w θ ≠ 1)
  have hS : ∀ w ∈ S, ∃ α : AddCircle (2 * Real.pi), torusBracketCircle χ₁ χ₂ w α ≠ 1 := by
    intro w hw
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, torusBracket χ₁ χ₂ w θ ≠ 1 := by
      simpa using (List.mem_filter.mp hw).2
    exact ⟨(θ : AddCircle (2 * Real.pi)), by rwa [torusBracketCircle_coe]⟩

  have hlim : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (p : P)
      (ζ : {w : InfinitePlace F // w.IsComplex} → ℂ) (θ : ℝ),
      Tendsto (fun R : ℝ => Φ p (Function.update ζ w ((R : ℂ) * Complex.exp (θ * Complex.I)))) atTop
        (𝓝 (φ (p.1 * uProd ((Lc F).erase w) ζ)
          * torusBracketCircle χ₁ χ₂ w ((θ : ℝ) : AddCircle (2 * Real.pi)))) := by
    intro w p ζ θ
    have hw : w ∈ Lc F := by simp [Lc]
    have hfun : (fun R : ℝ => Φ p (Function.update ζ w ((R : ℂ) * Complex.exp (θ * Complex.I))))
        = fun R : ℝ => φ (p.1 * (adelicArchGLInclAt F w.1 (uAt w.2 ((R : ℂ) * expI θ))
            * uProd ((Lc F).erase w) ζ)) := by
      funext R
      simp only [Φ, uProd_update_eq w _ (Lc F) (Lc_nodup F) hw]
      rfl
    have hval : φ (p.1 * (torusAt w θ * uProd ((Lc F).erase w) ζ))
        = φ (p.1 * uProd ((Lc F).erase w) ζ) * torusBracket χ₁ χ₂ w θ := by
      rw [← mul_assoc, ← mul_comm_of_glFin_eq_one_of_glArch_eq_one (glFin_torusAt w θ) p.2, mul_assoc,
        apply_torusAt_mul hφs, mul_comm (torusBracket χ₁ χ₂ w θ)]
    rw [hfun, torusBracketCircle_coe, ← hval]
    have hcont : Tendsto (fun R : ℝ => p.1 * (adelicArchGLInclAt F w.1 (uAt w.2 ((R : ℂ) * expI θ))
          * uProd ((Lc F).erase w) ζ)) atTop (𝓝 (p.1 * (torusAt w θ * uProd ((Lc F).erase w) ζ))) :=
      ((tendsto_incl_uAt_ray CircleParity.tendsto_rpow_neg_half_atTop CircleParity.tendsto_mul_rpow_neg_half_atTop
          w θ).mul_const _).const_mul _
    exact (hφc.tendsto _).comp hcont
  obtain ⟨ι, _, _, dd, wt, par, hlaw, hpole, -, hexp⟩ :=
    CircleParity.drop_at_places (@CircleParity.drop) Φ (torusBracketCircle χ₁ χ₂)
      (torusBracketCircle_add χ₁ χ₂) (fun w p ζ => φ (p.1 * uProd ((Lc F).erase w) ζ)) hlim S hS dd₀ hdd₀
      (fun i (p : P) => Cf₀ i p.1) hΦ
  refine ⟨ι, inferInstance, fun i g => wt i * Cf₀ (par i) g, dd, fun i => ?_, hlaw, fun i w hw => ?_,
    fun g hg ζ => ?_⟩
  · simpa only [Pi.smul_def, smul_eq_mul] using isKfSmooth_smul (wt i) (hCf₀ (par i)).2.2
  · have hwS : w ∈ S := List.mem_filter.mpr ⟨by simp [Lc], by simpa using hw⟩
    exact hpole i w hwS
  · have h := hexp ⟨g, hg⟩ ζ
    simp only [Φ] at h
    rw [h]

private theorem exists_sum_mul_atoms_mul_eq_of_isInducedSection (F : Type) [Field F] [NumberField F]
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (_hs : IsInducedSection (𝓞 F) F χ₁ χ₂ ψ) (_hK : IsArchKFinite F ψ)
    (_hc : Continuous ψ) (_hf : IsKfSmooth F ψ) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
      (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
      (ψ' : Fin n → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
          (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ j : Fin n, IsKfSmooth F (ψ' j)) ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}), (-1 : ℂ) ^ (kdat j i) = antipodalSign χ₁ χ₂ i) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
          (∃ θ : ℝ, torusBracket χ₁ χ₂ w θ ≠ 1) → ¬ CircleParity.IsPoleType (abm j w)) ∧
      ∀ (g : AdelicGL2 (𝓞 F) F), glArch (𝓞 F) F g = 1 → ∀ (x : AdeleRing (𝓞 F) F),
        ψ (g * BigCellExpansion.Iwasawa.kInf F x)
          = ∑ j : Fin n,
              c j
                * (∏ i : {w : InfinitePlace F // w.IsReal},
                    ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ)
                          - Complex.I)
                        / ((Real.sqrt
                            (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                            : ℝ) : ℂ)) ^ (kdat j i))
                * (∏ w : {w : InfinitePlace F // w.IsComplex},
                    Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm j w).1
                      * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1)) ^ (abm j w).2.1
                      * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                          ^ (-(((abm j w).2.2 : ℂ) / 2)))
                * ψ' j g := by
  obtain ⟨ι, hι, Cf, kd, hCf, hpar, hexpR⟩ := multi_real_expansion_smooth_induced _hc _hK _hf _hs
    (BigCellExpansion.Iwasawa.Lr F) (BigCellExpansion.Iwasawa.Lr_nodup F)
  choose ι' hι' Cf' dd hCf' hdd hpole hexpC using
    fun j : ι => complex_expansion_drop (hCf j).1 (hCf j).2.1 (hCf j).2.2.1 (hCf j).2.2.2
  let e := Fintype.equivFin (Σ j : ι, ι' j)
  refine ⟨Fintype.card (Σ j : ι, ι' j), fun _ => 1, fun m i => -(kd (e.symm m).1 i),
    fun m => dd (e.symm m).1 (e.symm m).2, fun m => Cf' (e.symm m).1 (e.symm m).2,
    fun m w => hdd _ _ w, fun m => hCf' _ _, fun m i => ?_, fun m w hw => hpole _ _ w hw, fun g hg x => ?_⟩
  · rw [neg_one_zpow_neg]
    exact hpar _ i (by simp [BigCellExpansion.Iwasawa.Lr])
  unfold BigCellExpansion.Iwasawa.kInf
  rw [← mul_assoc, hexpR]
  simp_rw [hexpC _ g hg]
  rw [← Equiv.sum_comp e, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Equiv.symm_apply_apply]
  dsimp only
  rw [← charProd_θx_eq F x (kd j), ← monoProd_Lc_eq_monoPi, ← monoProd_zC_eq F x (dd j i)]
  ring

end InducedExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end BigCellExpansion.ArchExpansion
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

namespace BigCellExpansion
namespace BorelValue

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicLevel"
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

private noncomputable def borelPart (F : Type) [Field F] [NumberField F] (x : AdeleRing (𝓞 F) F) :
    ↥(adelicBorel (𝓞 F) F) :=
  ⟨BigCellExpansion.Iwasawa.bigCell F x * (BigCellExpansion.Iwasawa.kTot F x)⁻¹,
    BigCellExpansion.Iwasawa.bigCell_mul_kTot_inv_mem_adelicBorel F x⟩

private noncomputable def signIdele (F : Type) [Field F] [NumberField F] : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ w : InfinitePlace F, NumberField.TateGlobal.archUnitHom w (-1)

section ChiUnits

open NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

private theorem rpos (t : ℝ) : 0 < (1 + t ^ 2) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_pos_of_pos (by positivity) _

private noncomputable def realUnit (i : {w : InfinitePlace F // w.IsReal}) {r : ℝ} (hr : 0 < r) :
    (i.1.Completion)ˣ :=
  Units.mk0 ((ringEquivRealOfIsReal i.2).symm r)
    ((map_ne_zero_iff _ (ringEquivRealOfIsReal i.2).symm.injective).2 hr.ne')

private noncomputable def complexUnit (w : {w : InfinitePlace F // w.IsComplex}) {r : ℝ} (hr : 0 < r) :
    (w.1.Completion)ˣ :=
  Units.mk0 ((ringEquivComplexOfIsComplex w.2).symm (r : ℂ))
    ((map_ne_zero_iff _ (ringEquivComplexOfIsComplex w.2).symm.injective).2
      (Complex.ofReal_ne_zero.2 hr.ne'))

end ChiUnits
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

private noncomputable def Rr (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (i : {w : InfinitePlace F // w.IsReal}) (r : ℝ) : ℂ :=
  if hr : 0 < r then (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 (realUnit i hr)) : ℂˣ) : ℂ) else 1

private noncomputable def Rc (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : {w : InfinitePlace F // w.IsComplex}) (r : ℝ) : ℂ :=
  if hr : 0 < r then (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 (complexUnit w hr)) : ℂˣ) : ℂ) else 1

section ChiBracket

open scoped Classical
open NumberField.InfinitePlace.Completion NumberField.TateGlobal NumberField.AdelicVolume
open BigCellExpansion.RealPlaces BigCellExpansion.Iwasawa

variable {F : Type} [Field F] [NumberField F]

private noncomputable def cA (w : InfinitePlace F) : (AdeleRing (𝓞 F) F)ˣ →* w.Completion :=
  (projArch F w).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 F) F))

private noncomputable def cF (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (AdeleRing (𝓞 F) F)ˣ →* v.adicCompletion F :=
  ((finAdeleEval (𝓞 F) F v).comp (projFin F)).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 F) F))

private theorem cA_apply (w : InfinitePlace F) (u : (AdeleRing (𝓞 F) F)ˣ) :
    cA w u = ((u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w := rfl

private theorem cF_apply (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (u : (AdeleRing (𝓞 F) F)ˣ) :
    cF v u = (((u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem units_ext_of_components {a b : (AdeleRing (𝓞 F) F)ˣ} (harch : ∀ w, cA w a = cA w b)
    (hfin : ∀ v, cF v a = cF v b) : a = b := by
  apply Units.ext
  refine Prod.ext (funext fun w => harch w) ?_
  exact DFunLike.ext _ _ fun v => hfin v

private noncomputable def finIdeleHom (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v)

private theorem localChar_eq_finIdeleHom (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    localChar χ v t = χ (finIdeleHom v t) := rfl

private theorem cA_archUnitHom_self (w : InfinitePlace F) (a : (w.Completion)ˣ) : cA w (archUnitHom w a) = a :=
  archCentralUnit_fst_self w a

private theorem cA_archUnitHom_of_ne {w w' : InfinitePlace F} (h : w ≠ w') (a : (w'.Completion)ˣ) :
    cA w (archUnitHom w' a) = 1 :=
  archCentralUnit_fst_of_ne w' a h

private theorem cF_archUnitHom (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F)
    (a : (w.Completion)ˣ) : cF v (archUnitHom w a) = 1 := by
  show finAdeleEval (𝓞 F) F v ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
  rw [archCentralUnit_snd, map_one]

private theorem cA_finIdeleHom (w : InfinitePlace F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (t : (v.adicCompletion F)ˣ) : cA w (finIdeleHom v t) = 1 := by
  rw [cA_apply]
  show (finIncl (𝓞 F) F ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)).1 w = 1
  rw [finIncl_apply_fst]
  rfl

private theorem cF_finIdeleHom_self (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    cF v (finIdeleHom v t) = t :=
  localUnit_apply_self (𝓞 F) F v t

private theorem cF_finIdeleHom_of_ne {v v' : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (h : v ≠ v')
    (t : (v'.adicCompletion F)ˣ) : cF v (finIdeleHom v' t) = 1 :=
  localUnit_apply_of_ne (𝓞 F) F v' t h

private theorem cA_signIdele (w : InfinitePlace F) : cA w (signIdele F) = -1 := by
  unfold signIdele
  rw [map_prod, Finset.prod_eq_single w]
  · rw [cA_archUnitHom_self]
    simp
  · intro w' _ hw'
    exact cA_archUnitHom_of_ne (Ne.symm hw') _
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem cF_signIdele (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : cF v (signIdele F) = 1 := by
  unfold signIdele
  rw [map_prod]
  exact Finset.prod_eq_one fun w _ => cF_archUnitHom v w _

private noncomputable def uR (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) : (i.1.Completion)ˣ :=
  realUnit i (rpos (extensionEmbeddingOfIsReal i.2 (x.1 i.1)))

private noncomputable def uC (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (w.1.Completion)ˣ :=
  complexUnit w (rpos ‖extensionEmbedding w.1 (x.1 w.1)‖)

private noncomputable def uF (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ :=
  if h : (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F then 1
  else (Units.mk0 _ (ne_zero_of_not_mem x.2 h))⁻¹

private noncomputable def badSet (x : AdeleRing (𝓞 F) F) : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.1 (x.2 : FiniteAdeleRing (𝓞 F) F).2 :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) |
      ¬ (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}.Finite).toFinset

private theorem mem_badSet (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    v ∈ badSet x ↔ (x.2 : FiniteAdeleRing (𝓞 F) F) v ∉ v.adicCompletionIntegers F := by
  simp only [badSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

private theorem uF_of_not_mem_badSet (x : AdeleRing (𝓞 F) F) {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ badSet x) : uF x v = 1 := by
  have hmem : (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
    by_contra h
    exact hv ((mem_badSet x v).2 h)
  unfold uF
  rw [dif_pos hmem]

private noncomputable def pR (x : AdeleRing (𝓞 F) F) : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ i : {w : InfinitePlace F // w.IsReal}, archUnitHom i.1 (uR x i)

private noncomputable def pC (x : AdeleRing (𝓞 F) F) : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ w : {w : InfinitePlace F // w.IsComplex}, archUnitHom w.1 (uC x w)

private noncomputable def pF (x : AdeleRing (𝓞 F) F) : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ v ∈ badSet x, finIdeleHom v (uF x v)

private noncomputable def pos (x : AdeleRing (𝓞 F) F) : (AdeleRing (𝓞 F) F)ˣ := pR x * pC x * pF x

private theorem cA_pR_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    cA i.1 (pR x) = uR x i := by
  unfold pR
  rw [map_prod, Finset.prod_eq_single i]
  · exact cA_archUnitHom_self i.1 (uR x i)
  · intro j _ hj
    exact cA_archUnitHom_of_ne (fun h => hj (Subtype.ext h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem cA_pC_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) : cA i.1 (pC x) = 1 := by
  unfold pC
  rw [map_prod]
  refine Finset.prod_eq_one fun w _ => cA_archUnitHom_of_ne (fun h => ?_) _
  exact (not_isReal_iff_isComplex.2 w.2) (h ▸ i.2)

private theorem cA_pR_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    cA w.1 (pR x) = 1 := by
  unfold pR
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => cA_archUnitHom_of_ne (fun h => ?_) _
  exact (not_isReal_iff_isComplex.2 w.2) (h.symm ▸ i.2)

private theorem cA_pC_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    cA w.1 (pC x) = uC x w := by
  unfold pC
  rw [map_prod, Finset.prod_eq_single w]
  · exact cA_archUnitHom_self w.1 (uC x w)
  · intro w' _ hw'
    exact cA_archUnitHom_of_ne (fun h => hw' (Subtype.ext h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem cA_pF (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) : cA w (pF x) = 1 := by
  unfold pF
  rw [map_prod]
  exact Finset.prod_eq_one fun v _ => cA_finIdeleHom w v _

private theorem cF_pR (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : cF v (pR x) = 1 := by
  unfold pR
  rw [map_prod]
  exact Finset.prod_eq_one fun i _ => cF_archUnitHom v i.1 _

private theorem cF_pC (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : cF v (pC x) = 1 := by
  unfold pC
  rw [map_prod]
  exact Finset.prod_eq_one fun w _ => cF_archUnitHom v w.1 _

private theorem cF_pF (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    cF v (pF x) = uF x v := by
  unfold pF
  rw [map_prod]
  by_cases hv : v ∈ badSet x
  · rw [Finset.prod_eq_single_of_mem v hv fun v' _ hv' => cF_finIdeleHom_of_ne (Ne.symm hv') _]
    exact cF_finIdeleHom_self v _
  · rw [Finset.prod_eq_one fun v' hv' => cF_finIdeleHom_of_ne (fun h => by subst h; exact hv hv') _,
      uF_of_not_mem_badSet x hv, Units.val_one]

private theorem cA_pos_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    cA i.1 (pos x) = uR x i := by
  unfold pos
  rw [map_mul, map_mul, cA_pR_real, cA_pC_real, cA_pF, mul_one, mul_one]

private theorem cA_pos_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    cA w.1 (pos x) = uC x w := by
  unfold pos
  rw [map_mul, map_mul, cA_pR_complex, cA_pC_complex, cA_pF, one_mul, mul_one]

private theorem cF_pos (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    cF v (pos x) = uF x v := by
  unfold pos
  rw [map_mul, map_mul, cF_pR, cF_pC, cF_pF, one_mul, one_mul]

private theorem norm_sq_zc (t : ℝ) : ‖(⟨t, 1⟩ : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mk]
  ring

private theorem rpow_neg_half_eq (t : ℝ) : (1 + t ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / ‖(⟨t, 1⟩ : ℂ)‖ := by
  rw [← norm_sq_zc t, Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _), one_div]

private theorem sin_θx (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    Real.sin (θx F x i) = (1 + extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ)) := by
  show Real.sin (θR (xr F x i)) = (1 + xr F x i ^ 2) ^ (-(1 / 2 : ℝ))
  rw [sin_θR, rpow_neg_half_eq]

private theorem sin_add_mul_cos_θx (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    Real.sin (θx F x i) + xr F x i * Real.cos (θx F x i)
      = ((1 + extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ)))⁻¹ := by
  show Real.sin (θR (xr F x i)) + xr F x i * Real.cos (θR (xr F x i)) = ((1 + xr F x i ^ 2) ^ (-(1 / 2 : ℝ)))⁻¹
  rw [rpow_neg_half_eq, one_div, inv_inv, sin_θR, cos_θR]
  have hn : ‖(⟨xr F x i, 1⟩ : ℂ)‖ ^ 2 = 1 + xr F x i ^ 2 := norm_sq_zc _
  have hn0 : ‖(⟨xr F x i, 1⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (zc_ne_zero _)
  field_simp
  nlinarith [hn]

private theorem ρR_mul_one_add (ζ : ℂ) :
    ((ρR ζ : ℝ) : ℂ) + ζ * (((ρR ζ : ℝ) : ℂ) * (starRingEnd ℂ) ζ) = (((ρR ζ : ℝ) : ℂ))⁻¹ := by
  have hk := ρR_key ζ
  symm
  exact inv_eq_of_mul_eq_one_right (by linear_combination hk)

private theorem star_uMat_apply_zero_one (ζ : ℂ) : star (uMat ζ) 0 1 = ((ρR ζ : ℝ) : ℂ) := by
  simp [uMat]

private theorem star_uMat_apply_one_one (ζ : ℂ) : star (uMat ζ) 1 1 = ((ρR ζ : ℝ) : ℂ) * (starRingEnd ℂ) ζ := by
  simp [uMat]

private theorem val_uC (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((uC x w : (w.1.Completion)ˣ) : w.1.Completion)
      = (ringEquivComplexOfIsComplex w.2).symm ((ρR (zC F x w) : ℝ) : ℂ) := rfl

private theorem val_uR (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    ((uR x i : (i.1.Completion)ˣ) : i.1.Completion)
      = (ringEquivRealOfIsReal i.2).symm ((1 + extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ))) :=
  rfl

private theorem cA_diagFst (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    cA w (borelDiagFst (borelPart F x))
      = ((projArch F w).mapMatrix
          ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
            * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))) 0 0 := rfl

private theorem cA_diagSnd (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    cA w (borelDiagSnd (borelPart F x))
      = ((projArch F w).mapMatrix
          ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
            * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))) 1 1 := rfl

private theorem cF_diagFst (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    cF v (borelDiagFst (borelPart F x))
      = ((finAdeleEval (𝓞 F) F v).mapMatrix ((projFin F).mapMatrix
          ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
            * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))))) 0 0 := rfl

private theorem cF_diagSnd (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    cF v (borelDiagSnd (borelPart F x))
      = ((finAdeleEval (𝓞 F) F v).mapMatrix ((projFin F).mapMatrix
          ((((bigCell F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
            * (((kTot F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))))) 1 1 := rfl

private theorem diagFst_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    cA i.1 (borelDiagFst (borelPart F x)) = -((uR x i : (i.1.Completion)ˣ) : i.1.Completion) := by
  rw [cA_diagFst, map_mul, projArch_bigCell, projArch_kTot_inv_real F x i]
  have e10 : (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion) 1 0
      = (ringEquivRealOfIsReal i.2).symm (-Real.sin (θx F x i)) := by
    simp [rotAt_inv_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, e10]
  show (0 : i.1.Completion) * _ + 1 * (ringEquivRealOfIsReal i.2).symm (-Real.sin (θx F x i)) = _
  rw [zero_mul, zero_add, one_mul, map_neg, sin_θx, val_uR]

private theorem diagSnd_real (x : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    cA i.1 (borelDiagSnd (borelPart F x)) = (((uR x i : (i.1.Completion)ˣ) : i.1.Completion))⁻¹ := by
  rw [cA_diagSnd, map_mul, projArch_bigCell, projArch_kTot_inv_real F x i]
  have e01 : (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion) 0 1
      = (ringEquivRealOfIsReal i.2).symm (Real.sin (θx F x i)) := by
    simp [rotAt_inv_apply]
  have e11 : (((rotAt i.2 (θx F x i))⁻¹ : GL (Fin 2) i.1.Completion) : Matrix (Fin 2) (Fin 2) i.1.Completion) 1 1
      = (ringEquivRealOfIsReal i.2).symm (Real.cos (θx F x i)) := by
    simp [rotAt_inv_apply]
  have hx0 : ringEquivRealOfIsReal i.2 (x.1 i.1) = xr F x i := rfl
  have hx' : x.1 i.1 = (ringEquivRealOfIsReal i.2).symm (xr F x i) := by
    rw [← hx0, RingEquiv.symm_apply_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, e01, e11]
  show (1 : i.1.Completion) * (ringEquivRealOfIsReal i.2).symm (Real.sin (θx F x i))
      + x.1 i.1 * (ringEquivRealOfIsReal i.2).symm (Real.cos (θx F x i)) = _
  rw [one_mul, hx', ← map_mul, ← map_add, val_uR, ← map_inv₀, sin_add_mul_cos_θx]

private theorem diagFst_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    cA w.1 (borelDiagFst (borelPart F x)) = -((uC x w : (w.1.Completion)ˣ) : w.1.Completion) := by
  rw [cA_diagFst, map_mul, projArch_bigCell, projArch_kTot_inv_complex F x w]
  have e10 : (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion) 1 0
      = (ringEquivComplexOfIsComplex w.2).symm (-((ρR (zC F x w) : ℝ) : ℂ)) := by
    rw [uAt_inv_apply, star_uMat_apply_one_zero]
  rw [Matrix.mul_apply, Fin.sum_univ_two, e10]
  show (0 : w.1.Completion) * _ + 1 * (ringEquivComplexOfIsComplex w.2).symm (-((ρR (zC F x w) : ℝ) : ℂ)) = _
  rw [zero_mul, zero_add, one_mul, map_neg, val_uC]

private theorem diagSnd_complex (x : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    cA w.1 (borelDiagSnd (borelPart F x)) = (((uC x w : (w.1.Completion)ˣ) : w.1.Completion))⁻¹ := by
  rw [cA_diagSnd, map_mul, projArch_bigCell, projArch_kTot_inv_complex F x w]
  have e01 : (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion) 0 1
      = (ringEquivComplexOfIsComplex w.2).symm ((ρR (zC F x w) : ℝ) : ℂ) := by
    rw [uAt_inv_apply, star_uMat_apply_zero_one]
  have e11 : (((uAt w.2 (zC F x w))⁻¹ : GL (Fin 2) w.1.Completion) : Matrix (Fin 2) (Fin 2) w.1.Completion) 1 1
      = (ringEquivComplexOfIsComplex w.2).symm (((ρR (zC F x w) : ℝ) : ℂ) * (starRingEnd ℂ) (zC F x w)) := by
    rw [uAt_inv_apply, star_uMat_apply_one_one]
  have hz : ringEquivComplexOfIsComplex w.2 (x.1 w.1) = zC F x w := rfl
  have hx' : x.1 w.1 = (ringEquivComplexOfIsComplex w.2).symm (zC F x w) := by
    rw [← hz, RingEquiv.symm_apply_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_two, e01, e11]
  show (1 : w.1.Completion) * (ringEquivComplexOfIsComplex w.2).symm ((ρR (zC F x w) : ℝ) : ℂ)
      + x.1 w.1 * (ringEquivComplexOfIsComplex w.2).symm (((ρR (zC F x w) : ℝ) : ℂ) * (starRingEnd ℂ) (zC F x w))
        = _
  rw [one_mul, hx', ← map_mul, ← map_add, val_uC, ← map_inv₀, ρR_mul_one_add]

private theorem diagFst_fin (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    cF v (borelDiagFst (borelPart F x)) = ((uF x v : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
  rw [cF_diagFst, map_mul, projFin_bigCell, projFin_kTot_inv, map_mul, eval_finW, eval_kffInv]
  unfold locKinv uF
  split_ifs with h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagSnd_fin (x : AdeleRing (𝓞 F) F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    cF v (borelDiagSnd (borelPart F x)) = (((uF x v : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ := by
  rw [cF_diagSnd, map_mul, projFin_bigCell, projFin_kTot_inv, map_mul, eval_finW, eval_kffInv]
  unfold locKinv uF
  split_ifs with h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem borelDiagFst_borelPart (x : AdeleRing (𝓞 F) F) :
    borelDiagFst (borelPart F x) = signIdele F * pos x := by
  refine units_ext_of_components (fun w => ?_) (fun v => ?_)
  · rw [map_mul, cA_signIdele, neg_one_mul]
    rcases isReal_or_isComplex w with hw | hw
    · exact (diagFst_real x ⟨w, hw⟩).trans (congrArg Neg.neg (cA_pos_real x ⟨w, hw⟩).symm)
    · exact (diagFst_complex x ⟨w, hw⟩).trans (congrArg Neg.neg (cA_pos_complex x ⟨w, hw⟩).symm)
  · rw [map_mul, cF_signIdele, one_mul, diagFst_fin, cF_pos]

private theorem borelDiagSnd_borelPart (x : AdeleRing (𝓞 F) F) :
    borelDiagSnd (borelPart F x) = (pos x)⁻¹ := by
  refine units_ext_of_components (fun w => ?_) (fun v => ?_)
  · rw [map_inv]
    rcases isReal_or_isComplex w with hw | hw
    · exact (diagSnd_real x ⟨w, hw⟩).trans (congrArg Inv.inv (cA_pos_real x ⟨w, hw⟩).symm)
    · exact (diagSnd_complex x ⟨w, hw⟩).trans (congrArg Inv.inv (cA_pos_complex x ⟨w, hw⟩).symm)
  · rw [map_inv, diagSnd_fin, cF_pos]

private theorem chi_pR (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F) :
    (((μ * ν⁻¹) (pR x) : ℂˣ) : ℂ)
      = (∏ i : {w : InfinitePlace F // w.IsReal},
          Rr F μ ν i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                        ^ (-(1 / 2 : ℝ)))) := by
  unfold pR
  rw [map_prod, ← Units.coeHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.coeHom_apply, Rr, dif_pos (rpos _)]
  rfl

private theorem chi_pC (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F) :
    (((μ * ν⁻¹) (pC x) : ℂˣ) : ℂ)
      = (∏ w : {w : InfinitePlace F // w.IsComplex},
          Rc F μ ν w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                        ^ (-(1 / 2 : ℝ)))) := by
  unfold pC
  rw [map_prod, ← Units.coeHom_apply, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Units.coeHom_apply, Rc, dif_pos (rpos _)]
  rfl

private theorem finite_factor_of_mem (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hv : v ∈ badSet x) :
    (((μ * ν⁻¹) (finIdeleHom v (uF x v)) : ℂˣ) : ℂ)
      = ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          (fun _ => (1 : ℂ)) (x.2 v)
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt
                (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
            (x.2 v)) := by
  have h : (x.2 : FiniteAdeleRing (𝓞 F) F) v ∉ v.adicCompletionIntegers F := (mem_badSet x v).1 hv
  have h' : (x.2 : FiniteAdeleRing (𝓞 F) F) v ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := h
  rw [Set.indicator_apply, Set.indicator_apply, if_neg h', if_pos (Set.mem_compl h'), zero_add,
    LanglandsTunnell.TateLocal.charExt_of_ne_zero _ (ne_zero_of_not_mem x.2 h), MonoidHom.inv_apply,
    localChar_eq_finIdeleHom, ← map_inv, ← map_inv]
  unfold uF
  rw [dif_neg h]

private theorem mulSupport_finite_factor (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
        (fun _ => (1 : ℂ)) (x.2 v)
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt
              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
          (x.2 v))) ⊆ ↑(badSet x) := by
  intro v hv
  rw [Function.mem_mulSupport] at hv
  rw [Finset.mem_coe, mem_badSet]
  intro hmem
  have hmem' : (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hmem
  apply hv
  rw [Set.indicator_apply, Set.indicator_apply, if_pos hmem', if_neg (fun h => (Set.mem_compl_iff _ _).1 h hmem'),
    add_zero]

private theorem chi_pF (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F) :
    (((μ * ν⁻¹) (pF x) : ℂˣ) : ℂ)
      = (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
            (fun _ => (1 : ℂ)) (x.2 v)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
                  (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
              (x.2 v))) := by
  rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_finite_factor μ ν x)]
  unfold pF
  rw [map_prod, ← Units.coeHom_apply, map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Units.coeHom_apply, finite_factor_of_mem μ ν x hv]

private theorem chi_pos (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : AdeleRing (𝓞 F) F) :
    (((μ * ν⁻¹) (pos x) : ℂˣ) : ℂ)
      = (∏ i : {w : InfinitePlace F // w.IsReal},
          Rr F μ ν i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                        ^ (-(1 / 2 : ℝ))))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
          Rc F μ ν w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                        ^ (-(1 / 2 : ℝ))))
        * (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
              (fun _ => (1 : ℂ)) (x.2 v)
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt
                    (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
                (x.2 v))) := by
  unfold pos
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, chi_pR, chi_pC, chi_pF]

end ChiBracket
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

private theorem Rr_pin (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ)
    (hu : 0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion)) :
    Rr F μ ν i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
      = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ) := by
  have hu' : realUnit i hu = u :=
    Units.ext (RingEquiv.symm_apply_apply (Completion.ringEquivRealOfIsReal i.2) (u : i.1.Completion))
  unfold Rr
  rw [dif_pos hu, hu']

private theorem Rc_pin (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (hu : Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ)) :
    Rc F μ ν w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) := by
  have hu' : complexUnit w hr = u := by
    refine Units.ext ?_
    show (Completion.ringEquivComplexOfIsComplex w.2).symm (r : ℂ) = (u : w.1.Completion)
    rw [← hu]
    exact RingEquiv.symm_apply_apply (Completion.ringEquivComplexOfIsComplex w.2) (u : w.1.Completion)
  unfold Rc
  rw [dif_pos hr, hu']

open scoped Classical in

private theorem chi_part (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (x : AdeleRing (𝓞 F) F) :
    ((μ (borelDiagFst (borelPart F x)) : ℂˣ) : ℂ) * ((ν (borelDiagSnd (borelPart F x)) : ℂˣ) : ℂ)
      = ((μ (signIdele F) : ℂˣ) : ℂ)
        * (∏ i : {w : InfinitePlace F // w.IsReal},
            Rr F μ ν i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                          ^ (-(1 / 2 : ℝ))))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
            Rc F μ ν w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                          ^ (-(1 / 2 : ℝ))))
              * (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                  ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
                      (fun _ => (1 : ℂ)) (x.2 v)
                    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                        (fun y => LanglandsTunnell.TateLocal.charExt
                            (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
                        (x.2 v))) := by
  have hχ := chi_pos μ ν x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] at hχ
  rw [borelDiagFst_borelPart, borelDiagSnd_borelPart, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  linear_combination ((μ (signIdele F) : ℂˣ) : ℂ) * hχ

private theorem flatOne_kTot (F : Type) [Field F] [NumberField F] (s : ℂ) (x : AdeleRing (𝓞 F) F) :
    BigCellExpansion.Height.flatOne F s (BigCellExpansion.Iwasawa.kTot F x) = 1 := by
  have h := BigCellExpansion.Height.flatOne_spherical F s (BigCellExpansion.Iwasawa.kTot F x)
    (BigCellExpansion.Iwasawa.glFin_kTot_mem F x) (BigCellExpansion.Iwasawa.isRowIsometry_kTot F x) 1
  rw [one_mul] at h
  rw [h, BigCellExpansion.Height.flatOne_apply_one]

private theorem mem_integers_iff_norm_le_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    y ∈ v.adicCompletionIntegers F ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

private theorem max_one_norm_of_mem (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {y : v.adicCompletion F} (hy : y ∈ v.adicCompletionIntegers F) : max 1 ‖y‖ = 1 :=
  max_eq_left ((mem_integers_iff_norm_le_one F v y).1 hy)

private theorem max_one_norm_of_not_mem (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {y : v.adicCompletion F} (hy : y ∉ v.adicCompletionIntegers F) :
    max 1 ‖y‖ = ((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  exact max_eq_right (not_le.1 fun h => hy ((mem_integers_iff_norm_le_one F v y).2 h)).le

private theorem merge_tail (F : Type) [Field F] [NumberField F] (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (x : AdeleRing (𝓞 F) F) :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          (fun _ => (1 : ℂ)) (x.2 v)
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt
                (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
            (x.2 v)))
      * (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ((max 1 ‖x.2 v‖ : ℝ) : ℂ) ^ (-(2 * s + 1)))
      = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
            (fun _ => (1 : ℂ)) (x.2 v)
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt
                  (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
              (x.2 v)) := by
  have hfin := BigCellExpansion.FiniteShell.finite_setOf_not_mem x.2
  have hA : (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v)
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y)
            (x.2 v)).Finite := by
    refine hfin.subset fun v hv => ?_
    show x.2 v ∉ v.adicCompletionIntegers F
    intro hmem
    apply hv
    have hmem' : x.2 v ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hmem
    simp [Set.indicator_of_mem hmem, Set.indicator_of_notMem hmem']
  have hB : (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ((max 1 ‖x.2 v‖ : ℝ) : ℂ) ^ (-(2 * s + 1))).Finite := by
    refine hfin.subset fun v hv => ?_
    show x.2 v ∉ v.adicCompletionIntegers F
    intro hmem
    apply hv
    simp [max_one_norm_of_mem F v hmem]
  rw [← finprod_mul_distrib hA hB]
  refine finprod_congr fun v => ?_
  by_cases hv : x.2 v ∈ v.adicCompletionIntegers F
  · have hv' : x.2 v ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h => h hv
    simp [Set.indicator_of_mem hv, Set.indicator_of_notMem hv', max_one_norm_of_mem F v hv]
  · have hv' : x.2 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := hv
    simp only [Set.indicator_of_notMem hv, Set.indicator_of_mem hv', zero_add]
    rw [max_one_norm_of_not_mem F v hv]

private theorem eta_split (F : Type) [Field F] [NumberField F] (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (d₁ d₂ : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst μ α hα s d₁ : ℂˣ) : ℂ) * ((etaSnd ν α hα s d₂ : ℂˣ) : ℂ)
      = ((μ d₁ : ℂˣ) : ℂ) * ((ν d₂ : ℂˣ) : ℂ)
        * (((etaFst 1 α hα s d₁ : ℂˣ) : ℂ) * ((etaSnd 1 α hα s d₂ : ℂˣ) : ℂ)) := by
  simp only [etaFst_apply, etaSnd_apply, MonoidHom.one_apply, Units.val_mul, one_mul]
  ring

open scoped Classical in

private theorem exists_const_bigCell_eq_mul_of_flat (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (s₀ : ℂ),
      ∃ (c : ℂ) (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
        (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ),
        (∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
          0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
          Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
            = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ)) ∧
        (∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
          Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
          Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) ∧
        ∀ (s : ℂ) (x : AdeleRing (𝓞 F) F),
          φ s (BigCellExpansion.Iwasawa.bigCell F x)
            = c
              * (∏ i : {w : InfinitePlace F // w.IsReal},
                  Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                          ^ (-(1 / 2 : ℝ)))
                    * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
                        ^ (-(s + 1 / 2)))
              * (∏ w : {w : InfinitePlace F // w.IsComplex},
                  Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                          ^ (-(1 / 2 : ℝ)))
                    * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                        ^ (-(2 * s + 1)))
              * (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                  ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
                      (fun _ => (1 : ℂ)) (x.2 v)
                    + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                        (fun y => LanglandsTunnell.TateLocal.charExt
                            (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                        (x.2 v)))
              * φ s₀ (BigCellExpansion.Iwasawa.kTot F x) := by
  intro α hα μ ν φ hφ hφflat s₀
  obtain ⟨-, -, hR3⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  refine ⟨((μ (signIdele F) : ℂˣ) : ℂ), Rr F μ ν, Rc F μ ν, fun i u hu => Rr_pin F μ ν i u hu,
    fun w u r hr hu => Rc_pin F μ ν w u r hr hu, fun s x => ?_⟩
  have hΦ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
      (BigCellExpansion.Height.flatOne F s) := hR3 hα s
  have h1 : φ s (BigCellExpansion.Iwasawa.bigCell F x)
      = ((etaFst μ α hα s (borelDiagFst (borelPart F x)) : ℂˣ) : ℂ)
          * ((etaSnd ν α hα s (borelDiagSnd (borelPart F x)) : ℂˣ) : ℂ)
          * φ s (BigCellExpansion.Iwasawa.kTot F x) := by
    rw [BigCellExpansion.Iwasawa.bigCell_eq_borel_mul_kTot F x]
    exact hφ s _ (borelPart F x).2 (BigCellExpansion.Iwasawa.kTot F x)
  have h2 : ((etaFst 1 α hα s (borelDiagFst (borelPart F x)) : ℂˣ) : ℂ)
        * ((etaSnd 1 α hα s (borelDiagSnd (borelPart F x)) : ℂˣ) : ℂ)
      = BigCellExpansion.Height.flatOne F s (BigCellExpansion.Iwasawa.bigCell F x) := by
    have h := hΦ _ (borelPart F x).2 (BigCellExpansion.Iwasawa.kTot F x)
    rw [flatOne_kTot F s x, mul_one] at h
    rw [BigCellExpansion.Iwasawa.bigCell_eq_borel_mul_kTot F x]
    exact h.symm
  have h4 : φ s (BigCellExpansion.Iwasawa.kTot F x) = φ s₀ (BigCellExpansion.Iwasawa.kTot F x) :=
    hφflat s s₀ _ (BigCellExpansion.Iwasawa.glFin_kTot_mem F x) (BigCellExpansion.Iwasawa.isRowIsometry_kTot F x)
  rw [h1, eta_split, chi_part F μ ν x, h2, h4,
    show BigCellExpansion.Iwasawa.bigCell F x = (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x from rfl,
    BigCellExpansion.FlatValue.flatOne_bigCell_eq F s x, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← merge_tail F μ ν s x]
  ring

end BigCellExpansion.BorelValue
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.AdelicHaar NumberField.AdelicLevel"
open NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace BigCellExpansion
namespace Assembly

private theorem adelicGL2_ext (F : Type) [Field F] [NumberField F] {g g' : AdelicGL2 (𝓞 F) F}
    (harch : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F g) = archComponent F w (glArch (𝓞 F) F g'))
    (hfin : glFin (𝓞 F) F g = glFin (𝓞 F) F g') : g = g' := by
  ext i j
  refine Prod.ext ?_ ?_
  · funext w
    have h := congrArg (fun m : GL (Fin 2) w.Completion =>
      (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (harch w)
    exact h
  · have h := congrArg (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) hfin
    exact h

private theorem kTot_eq_kF_mul_kInf (F : Type) [Field F] [NumberField F] (x : AdeleRing (𝓞 F) F) :
    BigCellExpansion.Iwasawa.kTot F x
      = BigCellExpansion.Iwasawa.kF F x * BigCellExpansion.Iwasawa.kInf F x := by
  apply adelicGL2_ext F
  · intro w
    simp only [BigCellExpansion.Iwasawa.kTot, map_mul, BigCellExpansion.Iwasawa.glArch_kF,
      mul_one, one_mul]
  · simp only [BigCellExpansion.Iwasawa.kTot, map_mul, BigCellExpansion.Iwasawa.glFin_kInf,
      mul_one, one_mul]

private theorem finprod_eq_prod_mul_finprod_subtype {X : Type*} (S : Finset X) (f : X → ℂ)
    (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ v, f v = (∏ v ∈ S, f v) * ∏ᶠ v : {v : X // v ∉ S}, f v.1 := by
  classical
  rw [← finprod_mem_univ f, ← finprod_mem_mul_diff' (Set.subset_univ (↑S : Set X))
      (by simpa using hf), finprod_mem_coe_finset, ← Set.compl_eq_univ_diff,
    ← finprod_set_coe_eq_finprod_mem]
  rfl

end BigCellExpansion.Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

namespace BigCellExpansion
namespace Assembly

p2m_open "NumberField P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.NumberField NumberField.InfinitePlace.NumberField"

private theorem archUnitHom_neg_one_sq (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    TateGlobal.archUnitHom w (-1) ^ 2 = 1 := by
  rw [← map_pow]
  simp

private theorem char_archUnitHom_neg_one_inv (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :
    (ν (TateGlobal.archUnitHom w (-1)))⁻¹ = ν (TateGlobal.archUnitHom w (-1)) := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ← map_pow, archUnitHom_neg_one_sq, map_one]

private theorem mul_apply_archUnitHom_neg_one_eq_mul_inv_apply (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :
    (μ * ν) (TateGlobal.archUnitHom w (-1)) = (μ * ν⁻¹) (TateGlobal.archUnitHom w (-1)) := by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, char_archUnitHom_neg_one_inv]

end BigCellExpansion.Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"
p2m_reactivate "P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.RealPlaces P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.BigCellExpansion.PlaceMeasure P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity.CircleParity"

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφc : ∀ s, Continuous (φ s))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0),
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (c : Fin n → ℂ)
        (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
        (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
        (m : ℕ) (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
        (Rc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℂ),
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
          (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
        1 ≤ m ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F,
          ∀ y ∈ v.adicCompletionIntegers F,
            Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A j v y = A j v x) ∧
        (∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
          Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B j v y = B j v x) ∧
        (∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
        (∀ v ∈ S, ∃ cN : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v cN,
          NumberField.TateGlobal.localChar (μ * ν⁻¹) v u = 1) ∧
        (∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
          0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
          Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
            = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ)) ∧
        (∀ (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
          Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
          Rc w r = (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) ∧
        (∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
          (-1 : ℂ) ^ (kdat j i)
            = (((μ * ν⁻¹)
                  (NumberField.TateGlobal.archUnitHom i.1 (-1 : (i.1.Completion)ˣ)) : ℂˣ) : ℂ)) ∧
        (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (u : (w.1.Completion)ˣ),
          ‖Completion.extensionEmbedding w.1 (u : w.1.Completion)‖ = 1 →
          (((μ * ν⁻¹) (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ) ≠ 1 →
          ¬ ((abm j w).1 = (abm j w).2.1 ∧ (abm j w).2.2 = 2 * (abm j w).1)) ∧
        ∀ (s : ℂ) (x : AdeleRing (𝓞 F) F),
          φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)
            = ∑ j : Fin n, c j
                * (∏ i : {w : InfinitePlace F // w.IsReal},
                    Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                            ^ (-(1 / 2 : ℝ)))
                      * ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ)
                            - Complex.I)
                          / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2)
                              : ℝ) : ℂ)) ^ (kdat j i)
                      * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ))
                          ^ (-(s + 1 / 2)))
                * (∏ w : {w : InfinitePlace F // w.IsComplex},
                    Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2)
                            ^ (-(1 / 2 : ℝ)))
                      * Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm j w).1
                      * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1))
                          ^ (abm j w).2.1
                      * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ))
                          ^ (-(2 * s + 1) - ((abm j w).2.2 : ℂ) / 2))
                * (∏ v ∈ S,
                    ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) (x.2 v)
                      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt
                              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))
                            * B j v y⁻¹) (x.2 v)))
                * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                    ((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                        (fun _ => (1 : ℂ)) (x.2 v.1)
                      + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt
                              (NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                          (x.2 v.1)) := by
  intro α hα μ ν φ hφ hφK hφf hφc hφflat hφne
  obtain ⟨s₀, g₀, hg₀⟩ := hφne
  obtain ⟨hcN, S₀, hS₀⟩ :=
    BigCellExpansion.QuotientChar.exists_finset_forall_localChar_eq_one_of_isInducedSection_of_isKfSmooth_of_ne_zero
      F hα μ ν s₀ (φ s₀) (hφ s₀) (hφf s₀) ⟨g₀, hg₀⟩
  obtain ⟨cC, Rr, Rc, hRr, hRc, hcell⟩ :=
    BigCellExpansion.BorelValue.exists_const_bigCell_eq_mul_of_flat F hα μ ν φ hφ hφflat (-(1 / 2 : ℂ))
  obtain ⟨n₁, c₁, kdat₁, abm₁, ψ', habm₁, hψ'f, hpar₁, hpole₁, harch⟩ :=
    BigCellExpansion.ArchExpansion.exists_sum_mul_atoms_mul_eq_of_isInducedSection F μ ν (φ (-(1 / 2 : ℂ)))
      (BigCellExpansion.EtaNegHalf.isInducedSection_of_neg_half (hφ (-(1 / 2 : ℂ)))) (hφK _) (hφc _) (hφf _)
  have hlev := fun j => BigCellExpansion.LevelExpansion.exists_finset_sum_prod_eq_of_isKfSmooth F (ψ' j) (hψ'f j)
  choose Sj mj hmj Nj dj Aj Bj hAj hBj hlevj using hlev
  have hmle : ∀ j : Fin n₁, mj j ≤ max (Finset.univ.sup mj) 1 := fun j =>
    (Finset.le_sup (f := mj) (Finset.mem_univ j)).trans (le_max_left _ _)
  have hvle : ∀ (j : Fin n₁) {v : HeightOneSpectrum (𝓞 F)} (z : v.adicCompletion F),
      Valued.v z ≤ Multiplicative.ofAdd (-((max (Finset.univ.sup mj) 1 : ℕ) : ℤ)) →
      Valued.v z ≤ Multiplicative.ofAdd (-(mj j : ℤ)) := fun j v z hz =>
    hz.trans (WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by
      have := hmle j
      omega)))
  have hSj : ∀ j : Fin n₁, Sj j ⊆ Finset.univ.biUnion Sj ∪ S₀ := fun j =>
    (Finset.subset_biUnion_of_mem Sj (Finset.mem_univ j)).trans Finset.subset_union_left
  refine ⟨Finset.univ.biUnion Sj ∪ S₀, ∑ j, Nj j,
    fun p => cC * c₁ ((finSigmaFinEquiv (n := Nj)).symm p).1 * dj ((finSigmaFinEquiv (n := Nj)).symm p).1 ((finSigmaFinEquiv (n := Nj)).symm p).2,
    fun p => kdat₁ ((finSigmaFinEquiv (n := Nj)).symm p).1,
    fun p => abm₁ ((finSigmaFinEquiv (n := Nj)).symm p).1,
    max (Finset.univ.sup mj) 1,
    fun p v => if v ∈ Sj ((finSigmaFinEquiv (n := Nj)).symm p).1 then Aj ((finSigmaFinEquiv (n := Nj)).symm p).1 ((finSigmaFinEquiv (n := Nj)).symm p).2 v else fun _ => 1,
    fun p v => if v ∈ Sj ((finSigmaFinEquiv (n := Nj)).symm p).1 then Bj ((finSigmaFinEquiv (n := Nj)).symm p).1 ((finSigmaFinEquiv (n := Nj)).symm p).2 v else fun _ => 1,
    Rr, Rc, fun p w => habm₁ _ w, le_max_right _ _, ?_, ?_, ?_, fun v _ => hcN v, hRr, hRc, ?_, ?_, ?_⟩
  · intro p v _ y hy z hz hyz
    dsimp only
    split_ifs with hvj
    · exact hAj _ _ v hvj y hy z hz (hvle _ _ hyz)
    · rfl
  · intro p v _ y z hyz
    dsimp only
    split_ifs with hvj
    · exact hBj _ _ v hvj y z (hvle _ _ hyz)
    · rfl
  · intro v hv u hu
    exact hS₀ v (fun h => hv (Finset.mem_union_right _ h)) u hu
  · intro p i
    rw [hpar₁ _ i]
    show ((μ (NumberField.TateGlobal.archUnitHom i.1 (-1)) : ℂˣ) : ℂ)
        * ((ν (NumberField.TateGlobal.archUnitHom i.1 (-1)) : ℂˣ) : ℂ) = _
    rw [← Units.val_mul, ← MonoidHom.mul_apply,
      BigCellExpansion.Assembly.mul_apply_archUnitHom_neg_one_eq_mul_inv_apply F i.1 μ ν]
  · intro p w u hu hne h
    exact hpole₁ _ w (BigCellExpansion.ArchExpansion.exists_torusBracket_ne_one μ ν w u hu hne) ⟨h.1.symm, h.2⟩
  · intro s x
    have hb : ∀ w : {w : InfinitePlace F // w.IsComplex}, (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := fun w =>
      Complex.ofReal_ne_zero.mpr (by positivity)
    have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x.2 v))).Finite := by
      refine (Filter.eventually_cofinite.mp x.2.2).subset ?_
      intro v hv hmem
      apply hv
      have hmem' : x.2 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hmem
      simp [hmem']
    have hR : ∀ j : Fin n₁,
        (∏ i : {w : InfinitePlace F // w.IsReal}, Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ))) * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))) * (∏ i : {w : InfinitePlace F // w.IsReal}, ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) : ℝ) : ℂ)) ^ (kdat₁ j i))
          = ∏ i : {w : InfinitePlace F // w.IsReal}, Rr i ((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) ^ (-(1 / 2 : ℝ))) * ((((Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2) : ℝ) : ℂ)) ^ (kdat₁ j i) * (((1 + Completion.extensionEmbeddingOfIsReal i.2 (x.1 i.1) ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2)) := by
      intro j
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    have hC : ∀ j : Fin n₁,
        (∏ w : {w : InfinitePlace F // w.IsComplex}, Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2) ^ (-(1 / 2 : ℝ))) * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1))) * (∏ w : {w : InfinitePlace F // w.IsComplex}, Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm₁ j w).1 * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1)) ^ (abm₁ j w).2.1 * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ)) ^ (-(((abm₁ j w).2.2 : ℂ) / 2)))
          = ∏ w : {w : InfinitePlace F // w.IsComplex}, Rc w ((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2) ^ (-(1 / 2 : ℝ))) * Completion.extensionEmbedding w.1 (x.1 w.1) ^ (abm₁ j w).1 * (starRingEnd ℂ) (Completion.extensionEmbedding w.1 (x.1 w.1)) ^ (abm₁ j w).2.1 * (((1 + ‖Completion.extensionEmbedding w.1 (x.1 w.1)‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - ((abm₁ j w).2.2 : ℂ) / 2) := by
      intro j
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [show -(2 * s + 1) - ((abm₁ j w).2.2 : ℂ) / 2 = -(2 * s + 1) + -(((abm₁ j w).2.2 : ℂ) / 2)
          from sub_eq_add_neg _ _, Complex.cpow_add _ _ (hb w)]
      ring
    have hLfin : ∀ (j : Fin n₁) (γ : Fin (Nj j)),
        (∏ v ∈ Finset.univ.biUnion Sj ∪ S₀,
            ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (if v ∈ Sj j then Aj j γ v else fun _ => 1) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * (if v ∈ Sj j then Bj j γ v else fun _ => 1) y⁻¹) (x.2 v)))
          = (∏ v ∈ Finset.univ.biUnion Sj ∪ S₀,
              ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x.2 v)))
            * ∏ v ∈ Sj j, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (Aj j γ v) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => Bj j γ v y⁻¹) (x.2 v)) := by
      intro j γ
      rw [show (∏ v ∈ Sj j, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (Aj j γ v) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => Bj j γ v y⁻¹) (x.2 v)))
            = ∏ v ∈ Finset.univ.biUnion Sj ∪ S₀, (if v ∈ Sj j then ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (Aj j γ v) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => Bj j γ v y⁻¹) (x.2 v)) else 1) from by
              rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (hSj j)],
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      by_cases hvj : v ∈ Sj j <;>
        by_cases hy : x.2 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) <;>
          simp [hvj, hy]
    rw [← Equiv.sum_comp (finSigmaFinEquiv (n := Nj))]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sigma]
    rw [show (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x = BigCellExpansion.Iwasawa.bigCell F x from rfl,
      hcell s x,
      BigCellExpansion.Assembly.finprod_eq_prod_mul_finprod_subtype (Finset.univ.biUnion Sj ∪ S₀) _ hfin,
      BigCellExpansion.Assembly.kTot_eq_kF_mul_kInf F x,
      harch (BigCellExpansion.Iwasawa.kF F x) (BigCellExpansion.Iwasawa.glArch_kF F x)]
    have hL : ∀ j : Fin n₁, ψ' j (BigCellExpansion.Iwasawa.kF F x)
        = ∑ γ : Fin (Nj j), dj j γ * ∏ v ∈ Sj j, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (Aj j γ v) (x.2 v) + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => Bj j γ v y⁻¹) (x.2 v)) := fun j =>
      hlevj j _ x.2 (BigCellExpansion.Iwasawa.glArch_kF F x) (BigCellExpansion.Iwasawa.glFin_kF F x)
    simp_rw [hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [Equiv.symm_apply_apply]
    dsimp only
    rw [← hR j, ← hC j, hLfin j γ]
    ring

end S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity
end P2MW
export P2MW.S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family_of_type_parity (solution)
