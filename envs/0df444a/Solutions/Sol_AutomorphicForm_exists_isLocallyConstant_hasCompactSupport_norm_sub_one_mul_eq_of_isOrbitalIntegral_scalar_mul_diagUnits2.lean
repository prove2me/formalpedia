-- Prove2me | solution 1 for AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8ecbdbde-ac16-524a-b54b-f1b33a8b8b76

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace R3C9

open AutomorphicForm Topology Filter

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K

theorem val_mul_apply {R : Type*} [CommRing R] (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

noncomputable def psi {R : Type*} [CommRing R] (q : Rˣ × Rˣ) : GL (Fin 2) R :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) q.2 * diagUnits2 q.1 1

theorem psi_val {R : Type*} [CommRing R] (q : Rˣ × Rˣ) (i j : Fin 2) :
    ((psi q : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (!![(q.2 : R) * (q.1 : R), 0; 0, (q.2 : R)] : Matrix (Fin 2) (Fin 2) R) i j := by
  unfold psi
  rw [val_mul_apply]
  change Matrix.scalar (Fin 2) (q.2 : R) i 0 * (!![(q.1 : R), 0; 0, ((1 : Rˣ) : R)] : Matrix (Fin 2) (Fin 2) R) 0 j +
    Matrix.scalar (Fin 2) (q.2 : R) i 1 * (!![(q.1 : R), 0; 0, ((1 : Rˣ) : R)] : Matrix (Fin 2) (Fin 2) R) 1 j = _
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

theorem psi_mul {R : Type*} [CommRing R] (p q : Rˣ × Rˣ) : psi (p * q) = psi p * psi q := by
  apply Units.ext; ext i j
  rw [psi_val, val_mul_apply, psi_val, psi_val, psi_val, psi_val]
  fin_cases i <;> fin_cases j <;> simp [mul_comm, mul_assoc, mul_left_comm]

theorem psi_mul_unipotent {R : Type*} [CommRing R] (q : Rˣ × Rˣ) (x : R) :
    psi q * unipotentGL2 x = unipotentGL2 ((q.1 : R) * x) * psi q := by
  apply Units.ext; ext i j
  rw [val_mul_apply, val_mul_apply, psi_val, psi_val, psi_val, psi_val]
  change _ * (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) 0 j + _ * (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) 1 j =
    (!![1, (q.1 : R) * x; 0, 1] : Matrix (Fin 2) (Fin 2) R) i 0 * _ + (!![1, (q.1 : R) * x; 0, 1] : Matrix (Fin 2) (Fin 2) R) i 1 * _
  fin_cases i <;> fin_cases j <;> simp [mul_comm, mul_assoc, mul_left_comm]

theorem det_psi_mul_unipotent_conj {R : Type*} [CommRing R] (q : Rˣ × Rˣ) (x : R) (k : GL (Fin 2) R) :
    Matrix.det ((k⁻¹ * psi q * unipotentGL2 x * k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (q.2 : R) * (q.2 : R) * (q.1 : R) := by
  have h1 : Matrix.det ((psi q : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (q.2 : R) * (q.2 : R) * (q.1 : R) := by
    rw [Matrix.det_fin_two, psi_val, psi_val, psi_val, psi_val]; simp; ring
  have h2 : Matrix.det ((unipotentGL2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 := by
    change Matrix.det (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) = 1
    rw [Matrix.det_fin_two]; simp
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, h1, h2]
  have h3 : Matrix.det ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * Matrix.det ((k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  calc Matrix.det ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * ((q.2 : R) * (q.2 : R) * (q.1 : R)) * 1 *
        Matrix.det ((k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = (Matrix.det ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * Matrix.det ((k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) *
        ((q.2 : R) * (q.2 : R) * (q.1 : R)) := by ring
    _ = _ := by rw [h3, one_mul]

theorem trace_psi_mul_unipotent_conj {R : Type*} [CommRing R] (q : Rˣ × Rˣ) (x : R) (k : GL (Fin 2) R) :
    Matrix.trace ((k⁻¹ * psi q * unipotentGL2 x * k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (q.2 : R) * ((q.1 : R) + 1) := by
  have hc : Matrix.trace ((k⁻¹ * psi q * unipotentGL2 x * k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.trace ((psi q * unipotentGL2 x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [show k⁻¹ * psi q * unipotentGL2 x * k = k⁻¹ * (psi q * unipotentGL2 x) * k by group, Units.val_mul, Units.val_mul,
      Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [hc, Matrix.trace_fin_two, val_mul_apply, val_mul_apply, psi_val, psi_val, psi_val, psi_val]
  change _ * (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) 0 0 + _ * (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) 1 0 +
    (_ * (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) 0 1 + _ * (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) 1 1) = _
  simp; ring

theorem continuous_psi {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (psi : Rˣ × Rˣ → GL (Fin 2) R) := by
  have h : ∀ q : Rˣ × Rˣ, (psi q)⁻¹ = psi q⁻¹ := fun q => by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← psi_mul, inv_mul_cancel]
    apply Units.ext; ext i j; rw [psi_val]; fin_cases i <;> fin_cases j <;> simp
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    refine (continuous_congr fun q : Rˣ × Rˣ => psi_val q i j).mpr ?_
    fin_cases i <;> fin_cases j
    · show Continuous fun q : Rˣ × Rˣ => (q.2 : R) * (q.1 : R)
      exact (Units.continuous_val.comp continuous_snd).mul (Units.continuous_val.comp continuous_fst)
    · exact continuous_const
    · exact continuous_const
    · show Continuous fun q : Rˣ × Rˣ => (q.2 : R)
      exact Units.continuous_val.comp continuous_snd
  · refine continuous_matrix fun i j => ?_
    refine (continuous_congr fun q : Rˣ × Rˣ => by rw [h q, psi_val]).mpr ?_
    fin_cases i <;> fin_cases j
    · show Continuous fun q : Rˣ × Rˣ => ((q⁻¹).2 : R) * ((q⁻¹).1 : R)
      exact (Units.continuous_coe_inv.comp continuous_snd).mul (Units.continuous_coe_inv.comp continuous_fst)
    · exact continuous_const
    · exact continuous_const
    · show Continuous fun q : Rˣ × Rˣ => ((q⁻¹).2 : R)
      exact Units.continuous_coe_inv.comp continuous_snd

theorem mem_integers_iff_norm_le_one (x : F) : x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans Valued.toNormedField.norm_le_one_iff.symm

theorem integral_comp_mul_left_of_norm_eq_one [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (a : F) (ha : ‖a‖ = 1) (g : F → ℂ) : ∫ x, g (a * x) ∂μ = ∫ x, g x ∂μ := by
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at ha; exact zero_ne_one ha
  let e : F ≃ₜ+ F :=
    { toFun := fun x => a * x
      invFun := fun x => a⁻¹ * x
      left_inv := fun x => by simp [ha0]
      right_inv := fun x => by simp [ha0]
      map_add' := fun x y => mul_add a x y
      continuous_toFun := continuous_mul_left a
      continuous_invFun := continuous_mul_left a⁻¹ }
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hOc : IsCompact (v.adicCompletionIntegers K : Set F) :=
    isCompact_iff_compactSpace.2 (NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hOo : IsOpen (v.adicCompletionIntegers K : Set F) := (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v
  let K₀ : TopologicalSpace.PositiveCompacts F :=
    { carrier := (v.adicCompletionIntegers K : Set F)
      isCompact' := hOc
      interior_nonempty' := by rw [hOo.interior_eq]; exact ⟨0, zero_mem _⟩ }
  have hpre : (e : F → F) ⁻¹' (v.adicCompletionIntegers K : Set F) = (v.adicCompletionIntegers K : Set F) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_integers_iff_norm_le_one]
    show ‖a * x‖ ≤ 1 ↔ ‖x‖ ≤ 1
    rw [norm_mul, ha, one_mul]
  have hmeas : Measurable (e : F → F) := e.continuous.measurable
  have hK : (Measure.map e μ) (K₀ : Set F) = μ (K₀ : Set F) := by
    show (Measure.map e μ) (v.adicCompletionIntegers K : Set F) = μ (v.adicCompletionIntegers K : Set F)
    rw [Measure.map_apply hmeas hOo.measurableSet, hpre]
  have hmap : Measure.map e μ = μ := by
    have e1 := Measure.addHaarMeasure_unique (Measure.map e μ) K₀
    have e2 := Measure.addHaarMeasure_unique μ K₀
    rw [e1, hK]; exact e2.symm
  calc ∫ x, g (a * x) ∂μ = ∫ x, g (e x) ∂μ := rfl
    _ = ∫ x, g x ∂(Measure.map e μ) := (integral_map_equiv e.toHomeomorph.toMeasurableEquiv g).symm
    _ = ∫ x, g x ∂μ := by rw [hmap]

theorem eventually_norm_eq_one : ∀ᶠ (a : Fˣ) in 𝓝 1, ‖(a : F)‖ = 1 := by
  have hOo : IsOpen (v.adicCompletionIntegers K : Set F) := (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v
  have h1 : ∀ᶠ (a : Fˣ) in 𝓝 1, (a : F) ∈ (v.adicCompletionIntegers K : Set F) :=
    Units.continuous_val.continuousAt.eventually_mem (hOo.mem_nhds (by rw [Units.val_one]; exact one_mem _))
  have h2 : ∀ᶠ (a : Fˣ) in 𝓝 1, ((a⁻¹ : Fˣ) : F) ∈ (v.adicCompletionIntegers K : Set F) :=
    Units.continuous_coe_inv.continuousAt.eventually_mem (hOo.mem_nhds (by rw [inv_one, Units.val_one]; exact one_mem _))
  filter_upwards [h1, h2] with a ha ha'
  rw [SetLike.mem_coe, mem_integers_iff_norm_le_one] at ha ha'
  refine le_antisymm ha ?_
  have h : ‖(a : F)‖ * ‖((a⁻¹ : Fˣ) : F)‖ = 1 := by rw [← norm_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, norm_one]
  nlinarith [norm_nonneg (a : F), norm_nonneg ((a⁻¹ : Fˣ) : F)]

theorem eventually_conj_mem (U : Subgroup (GL (Fin 2) F)) (hUo : IsOpen (U : Set (GL (Fin 2) F))) :
    ∀ᶠ δ in 𝓝 (1 : GL (Fin 2) F), ∀ k ∈ localIntegralSet K v, k⁻¹ * δ * k ∈ U := by
  refine (isCompact_localIntegralSet K v).eventually_forall_of_forall_eventually fun k _ => ?_
  have hc : Continuous fun z : GL (Fin 2) F × GL (Fin 2) F => z.2⁻¹ * z.1 * z.2 :=
    (continuous_snd.inv.mul continuous_fst).mul continuous_snd
  exact hc.continuousAt.eventually_mem (hUo.mem_nhds (by simp [one_mem]))

theorem psi_one {R : Type*} [CommRing R] : psi (1 : Rˣ × Rˣ) = 1 := by
  apply Units.ext; ext i j; rw [psi_val]; fin_cases i <;> fin_cases j <;> simp

section D
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

noncomputable def E (fv : GL (Fin 2) F → ℂ) (p : Fˣ × Fˣ) : ℂ :=
  letI := localGLBorel K v
  ∫ k, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
    (∫ x, fv (k⁻¹ * psi p * unipotentGL2 x * k) ∂μ) ∂(localHaar K v)

theorem isLocallyConstant_D (fv : GL (Fin 2) F → ℂ) (hfv : IsLocalTestFn K v fv) :
    IsLocallyConstant (fun p : Fˣ × Fˣ => (‖((p.1 : Fˣ) : F)‖ : ℂ) * E K v μ fv p) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p₀
  obtain ⟨U, hUo, hUK, hbi⟩ :=
    AutomorphicForm.exists_subgroup_isOpen_subset_localIntegralSet_forall_mul_eq_of_isLocalTestFn K v fv hfv
  have hV := eventually_conj_mem K v U hUo
  have hN := eventually_norm_eq_one K v
  have ht : Tendsto (fun p : Fˣ × Fˣ => p * p₀⁻¹) (𝓝 p₀) (𝓝 1) := by
    have h : Tendsto (fun p : Fˣ × Fˣ => p * p₀⁻¹) (𝓝 p₀) (𝓝 (p₀ * p₀⁻¹)) := (continuous_mul_right p₀⁻¹).tendsto p₀
    rwa [mul_inv_cancel] at h
  have hψ : Tendsto (psi : Fˣ × Fˣ → GL (Fin 2) F) (𝓝 1) (𝓝 1) := by
    have h := (continuous_psi (R := F)).tendsto (1 : Fˣ × Fˣ)
    rwa [psi_one] at h
  have h1 : ∀ᶠ p in 𝓝 p₀, ∀ k ∈ localIntegralSet K v, k⁻¹ * psi (p * p₀⁻¹) * k ∈ U :=
    ht.eventually (hψ.eventually hV)
  have hfst : Tendsto (fun q : Fˣ × Fˣ => q.1) (𝓝 1) (𝓝 1) := continuous_fst.tendsto (1 : Fˣ × Fˣ)
  have h2 : ∀ᶠ p in 𝓝 p₀, ‖(((p * p₀⁻¹).1 : Fˣ) : F)‖ = 1 := ht.eventually (hfst.eventually hN)
  filter_upwards [h1, h2] with p hp1 hp2
  set q : Fˣ × Fˣ := p * p₀⁻¹ with hq
  have hp : p = p₀ * q := by rw [hq, mul_comm, inv_mul_cancel_right]
  have hn : ‖((p.1 : Fˣ) : F)‖ = ‖((p₀.1 : Fˣ) : F)‖ := by
    rw [hp, Prod.fst_mul, Units.val_mul, norm_mul, hp2, mul_one]
  rw [hn]
  congr 1
  unfold E
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  show (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * _ = (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * _
  by_cases hk : k ∈ localIntegralSet K v
  · rw [Set.indicator_of_mem hk, one_mul, one_mul]
    have key : ∀ x : F, fv (k⁻¹ * psi p * unipotentGL2 x * k) = fv (k⁻¹ * psi p₀ * unipotentGL2 ((q.1 : F) * x) * k) := by
      intro x
      have e1 : k⁻¹ * psi p * unipotentGL2 x * k =
          1 * (k⁻¹ * psi p₀ * unipotentGL2 ((q.1 : F) * x) * k) * (k⁻¹ * psi q * k) := by
        rw [hp, psi_mul, one_mul,
          show k⁻¹ * (psi p₀ * psi q) * unipotentGL2 x * k = k⁻¹ * psi p₀ * (psi q * unipotentGL2 x) * k by group,
          psi_mul_unipotent]
        group
      rw [e1, hbi _ 1 U.one_mem _ (hp1 k hk)]
    calc ∫ x, fv (k⁻¹ * psi p * unipotentGL2 x * k) ∂μ
        = ∫ x, fv (k⁻¹ * psi p₀ * unipotentGL2 ((q.1 : F) * x) * k) ∂μ :=
          integral_congr_ae (Eventually.of_forall key)
      _ = ∫ x, fv (k⁻¹ * psi p₀ * unipotentGL2 x * k) ∂μ :=
          integral_comp_mul_left_of_norm_eq_one K v μ _ hp2 (fun x => fv (k⁻¹ * psi p₀ * unipotentGL2 x * k))
  · rw [Set.indicator_of_notMem hk, zero_mul, zero_mul]

theorem isCompact_annulus (a b : ℝ) (ha : 0 < a) :
    IsCompact {u : Fˣ | a ≤ ‖(u : F)‖ ∧ ‖(u : F)‖ ≤ b} := by
  rw [Units.isEmbedding_val₀.isInducing.isCompact_iff]
  have hB : IsCompact {x : F | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : F)) (r := b)).subset fun x hx => ?_
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx.2
  convert hB using 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem hasCompactSupport_D (fv : GL (Fin 2) F → ℂ) (hfv : IsLocalTestFn K v fv) :
    HasCompactSupport (fun p : Fˣ × Fˣ => (‖((p.1 : Fˣ) : F)‖ : ℂ) * E K v μ fv p) := by
  set C := tsupport fv with hC
  have hCc : IsCompact C := hfv.2

  have hdet : Continuous fun g : GL (Fin 2) F => ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) F)‖ :=
    (Units.continuous_val.matrix_det).norm
  have hdet0 : ∀ g : GL (Fin 2) F, ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) F)‖ ≠ 0 := fun g =>
    norm_ne_zero_iff.mpr (Matrix.isUnits_det_units g).ne_zero
  have hdeti : Continuous fun g : GL (Fin 2) F => ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) F)‖⁻¹ := hdet.inv₀ hdet0
  have htr : Continuous fun g : GL (Fin 2) F => ‖Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)‖ :=
    (Units.continuous_val.matrix_trace).norm
  obtain ⟨M, hM⟩ := hCc.bddAbove_image hdet.continuousOn
  obtain ⟨Mi, hMi⟩ := hCc.bddAbove_image hdeti.continuousOn
  obtain ⟨Mt, hMt⟩ := hCc.bddAbove_image htr.continuousOn
  rw [mem_upperBounds] at hM hMi hMt
  have hM' : ∀ g ∈ C, ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) F)‖ ≤ max M 1 := fun g hg =>
    (hM _ ⟨g, hg, rfl⟩).trans (le_max_left _ _)
  have hMi' : ∀ g ∈ C, ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) F)‖⁻¹ ≤ max Mi 1 := fun g hg =>
    (hMi _ ⟨g, hg, rfl⟩).trans (le_max_left _ _)
  have hMt' : ∀ g ∈ C, ‖Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)‖ ≤ max Mt 1 := fun g hg =>
    (hMt _ ⟨g, hg, rfl⟩).trans (le_max_left _ _)
  set M₁ := max M 1 with hM1
  set M₂ := max Mi 1 with hM2
  set M₃ := max Mt 1 with hM3
  have hM1p : 1 ≤ M₁ := le_max_right _ _
  have hM2p : 1 ≤ M₂ := le_max_right _ _
  have hM3p : 1 ≤ M₃ := le_max_right _ _

  set a₁ : ℝ := (M₂ * M₃ ^ 2)⁻¹ with ha1
  set b₁ : ℝ := M₂ * M₃ ^ 2 with hb1
  have hb1p : 1 ≤ b₁ := by rw [hb1]; nlinarith
  have ha1p : 0 < a₁ := by rw [ha1]; positivity
  have ha1le : a₁ ≤ 1 := by rw [ha1]; exact inv_le_one_of_one_le₀ hb1p
  set a₂ : ℝ := Real.sqrt ((M₂ * b₁)⁻¹) with ha2
  set b₂ : ℝ := Real.sqrt (M₁ / a₁) with hb2
  have ha2p : 0 < a₂ := by rw [ha2]; positivity
  set S : Set (Fˣ × Fˣ) := {u : Fˣ | a₁ ≤ ‖(u : F)‖ ∧ ‖(u : F)‖ ≤ b₁} ×ˢ {z : Fˣ | a₂ ≤ ‖(z : F)‖ ∧ ‖(z : F)‖ ≤ b₂}
    with hS
  have hSc : IsCompact S := (isCompact_annulus K v a₁ b₁ ha1p).prod (isCompact_annulus K v a₂ b₂ ha2p)
  refine HasCompactSupport.intro hSc fun p hp => ?_

  by_contra hne
  have hE : E K v μ fv p ≠ 0 := by
    intro h0; exact hne (by rw [h0, mul_zero])

  have hex : ∃ k x, k ∈ localIntegralSet K v ∧ fv (k⁻¹ * psi p * unipotentGL2 x * k) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hE
    unfold E
    refine integral_eq_zero_of_ae (Eventually.of_forall fun k => ?_)
    show (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k * _ = 0
    by_cases hk : k ∈ localIntegralSet K v
    · rw [Set.indicator_of_mem hk, one_mul]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
      exact hall k x hk
    · rw [Set.indicator_of_notMem hk, zero_mul]
  obtain ⟨k, x, hk, hfx⟩ := hex
  set g := k⁻¹ * psi p * unipotentGL2 x * k with hg
  have hgC : g ∈ C := subset_tsupport _ hfx
  have hdg : ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) F)‖ = ‖((p.2 : Fˣ) : F)‖ ^ 2 * ‖((p.1 : Fˣ) : F)‖ := by
    rw [hg, det_psi_mul_unipotent_conj, norm_mul, norm_mul, pow_two]
  have htg : ‖Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)‖ = ‖((p.2 : Fˣ) : F)‖ * ‖((p.1 : Fˣ) : F) + 1‖ := by
    rw [hg, trace_psi_mul_unipotent_conj, norm_mul]
  have b_det : ‖((p.2 : Fˣ) : F)‖ ^ 2 * ‖((p.1 : Fˣ) : F)‖ ≤ M₁ := hdg ▸ hM' g hgC
  have b_deti : (‖((p.2 : Fˣ) : F)‖ ^ 2 * ‖((p.1 : Fˣ) : F)‖)⁻¹ ≤ M₂ := hdg ▸ hMi' g hgC
  have b_tr : ‖((p.2 : Fˣ) : F)‖ * ‖((p.1 : Fˣ) : F) + 1‖ ≤ M₃ := htg ▸ hMt' g hgC
  set nu := ‖((p.1 : Fˣ) : F)‖ with hnu
  set nz := ‖((p.2 : Fˣ) : F)‖ with hnz
  have hnu0 : 0 < nu := norm_pos_iff.mpr (p.1).ne_zero
  have hnz0 : 0 < nz := norm_pos_iff.mpr (p.2).ne_zero
  have hd0 : 0 < nz ^ 2 * nu := by positivity
  have b_deti' : 1 ≤ M₂ * (nz ^ 2 * nu) := by
    have := mul_le_mul_of_nonneg_right b_deti hd0.le
    rwa [inv_mul_cancel₀ hd0.ne'] at this

  have hu_up : nu ≤ b₁ := by
    rcases lt_or_ge 1 nu with h1 | h1
    · have hadd : ‖((p.1 : Fˣ) : F) + 1‖ = nu := by
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h1.ne'), norm_one,
          max_eq_left h1.le]
      rw [hadd] at b_tr

      have h2 : (nz * nu) ^ 2 ≤ M₃ ^ 2 := pow_le_pow_left₀ (by positivity) b_tr 2
      have h3 : nu ≤ M₂ * (nz * nu) ^ 2 := by nlinarith
      rw [hb1]; nlinarith
    · exact h1.trans hb1p
  have hu_lo : a₁ ≤ nu := by
    rcases lt_or_ge nu 1 with h1 | h1
    · have hadd : ‖((p.1 : Fˣ) : F) + 1‖ = 1 := by
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h1.ne), norm_one,
          max_eq_right h1.le]
      rw [hadd, mul_one] at b_tr

      have h2 : nz ^ 2 ≤ M₃ ^ 2 := pow_le_pow_left₀ hnz0.le b_tr 2
      have h3 : 1 ≤ M₂ * M₃ ^ 2 * nu := by
        calc (1 : ℝ) ≤ M₂ * (nz ^ 2 * nu) := b_deti'
          _ ≤ M₂ * (M₃ ^ 2 * nu) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right h2 hnu0.le
          _ = M₂ * M₃ ^ 2 * nu := by ring
      rw [ha1]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      linarith
    · exact ha1le.trans h1

  have hz_up : nz ≤ b₂ := by
    have hsq : nz ^ 2 ≤ M₁ / a₁ := by
      rw [le_div_iff₀ ha1p]
      calc nz ^ 2 * a₁ ≤ nz ^ 2 * nu := mul_le_mul_of_nonneg_left hu_lo (sq_nonneg _)
        _ ≤ M₁ := b_det
    calc nz = Real.sqrt (nz ^ 2) := (Real.sqrt_sq hnz0.le).symm
      _ ≤ Real.sqrt (M₁ / a₁) := Real.sqrt_le_sqrt hsq
  have hz_lo : a₂ ≤ nz := by
    have hsq : (M₂ * b₁)⁻¹ ≤ nz ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      calc (1 : ℝ) ≤ M₂ * (nz ^ 2 * nu) := b_deti'
        _ ≤ M₂ * (nz ^ 2 * b₁) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hu_up (sq_nonneg _)
        _ = nz ^ 2 * (M₂ * b₁) := by ring
    calc a₂ = Real.sqrt ((M₂ * b₁)⁻¹) := rfl
      _ ≤ Real.sqrt (nz ^ 2) := Real.sqrt_le_sqrt hsq
      _ = nz := Real.sqrt_sq hnz0.le
  exact hp ⟨⟨hu_lo, hu_up⟩, ⟨hz_lo, hz_up⟩⟩

end D

end R3C9

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      ∀ (u z : (v.adicCompletion K)ˣ), (u : v.adicCompletion K) ≠ 1 →
        ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1)) τ →
          τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fv I →
            (‖(u : v.adicCompletion K) - 1‖ : ℂ) * I = Φ (u, z)  := by
  classical
  letI mF : MeasurableSpace (v.adicCompletion K) := borel _
  haveI : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
  let μ : Measure (v.adicCompletion K) := Measure.addHaar
  set c₀ : ℝ := ((μ (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal)⁻¹ with hc₀
  refine ⟨fun p => (c₀ : ℂ) * ((‖((p.1 : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ : ℂ) * R3C9.E K v μ fv p),
    ?_, ?_, ?_⟩
  · exact (R3C9.isLocallyConstant_D K v μ fv hfv).comp (fun y => (c₀ : ℂ) * y)
  · exact (R3C9.hasCompactSupport_D K v μ fv hfv).mul_left
  intro u z hu τ hτ hτ1 I hI

  have hγv : ∀ i j : Fin 2, ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 :
      GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (!![(z : v.adicCompletion K) * (u : v.adicCompletion K), 0; 0, (z : v.adicCompletion K)] :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := R3C9.psi_val (u, z)
  have hz0 : (z : v.adicCompletion K) ≠ 0 := z.ne_zero
  have hu0 : (u : v.adicCompletion K) ≠ 0 := u.ne_zero
  have hu1 : (u : v.adicCompletion K) - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hreg : AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) := by
    rw [AutomorphicForm.isRegularSemisimple_iff_ne_zero, Matrix.trace_fin_two, Matrix.det_fin_two, hγv, hγv, hγv, hγv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    have : ((z : v.adicCompletion K) * u + z) ^ 2 - 4 * ((z : v.adicCompletion K) * u * z - 0 * 0) =
        ((z : v.adicCompletion K) * (u - 1)) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 (mul_ne_zero hz0 hu1)
  have h01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by rw [hγv]; simp
  have h10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by rw [hγv]; simp
  have hD := AutomorphicForm.eq_norm_inv_mul_integral_localIntegralSet_integral_conj_unipotentGL2_of_isOrbitalIntegral_of_diagonal
    K v _ hreg h01 h10 τ hτ μ fv hfv I hI

  have hτ1' : (τ {t : AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) |
      (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v}).toReal = 1 := by
    show (τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v)).toReal = 1
    rw [hτ1, ENNReal.toReal_one]
  have hquot : ‖1 - ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ =
      ‖(u : v.adicCompletion K) - 1‖ / ‖(u : v.adicCompletion K)‖ := by
    rw [hγv, hγv]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    rw [← norm_div]
    congr 1
    field_simp
  have hE : (letI := AutomorphicForm.localGLBorel K v
      ∫ k, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ)) k *
        (∫ x, fv (k⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) * AutomorphicForm.unipotentGL2 x) * k) ∂μ)
        ∂(AutomorphicForm.localHaar K v)) = R3C9.E K v μ fv (u, z) := by
    unfold R3C9.E R3C9.psi
    simp only [mul_assoc]
  rw [hτ1', hquot, hE, inv_one, one_mul] at hD
  rw [hD, hc₀]
  have hn1 : (‖(u : v.adicCompletion K) - 1‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hu1
  have hn0 : (‖(u : v.adicCompletion K)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hu0
  set m : ℝ := (μ (v.adicCompletionIntegers K : Set (v.adicCompletion K))).toReal with hm
  have key : ‖(u : v.adicCompletion K) - 1‖ * (m⁻¹ * (‖(u : v.adicCompletion K) - 1‖ / ‖(u : v.adicCompletion K)‖)⁻¹) =
      m⁻¹ * ‖(u : v.adicCompletion K)‖ := by
    field_simp
  simp only [← mul_assoc, ← Complex.ofReal_mul, key]

end S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2 (solution)
