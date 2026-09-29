-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4cf1c618-3c96-519b-8dc1-49fa21bb293b

import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_adelicKernel_eq_four_parts_of_localFiniteness
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R1EdCellSplit

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem isAddHaar : (adelicAddHaar (𝓞 K) K).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 K) K

attribute [local instance] isAddHaar

section HeightLocal

variable {k : Type*} [NormedField k]

private theorem coe_mul' (s g : GL (Fin 2) k) :
    ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
      = (s : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k) := rfl

theorem bottom_row_mul {s : GL (Fin 2) k} (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (g : GL (Fin 2) k) (j : Fin 2) :
    ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 j
      = (s : Matrix (Fin 2) (Fin 2) k) 1 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 j := by
  rw [coe_mul', Matrix.mul_apply, Fin.sum_univ_two, h10]
  ring

theorem norm_det_mul_of_upper {s : GL (Fin 2) k} (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (g : GL (Fin 2) k) :
    ‖((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det‖
      = ‖(s : Matrix (Fin 2) (Fin 2) k) 0 0‖ * ‖(s : Matrix (Fin 2) (Fin 2) k) 1 1‖
          * ‖(g : Matrix (Fin 2) (Fin 2) k).det‖ := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) k).det
      = (s : Matrix (Fin 2) (Fin 2) k) 0 0 * (s : Matrix (Fin 2) (Fin 2) k) 1 1 := by
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  rw [coe_mul', Matrix.det_mul, hdets, norm_mul, norm_mul]

theorem localHeight_mul_of_unipotent {s : GL (Fin 2) k} (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) k) 0 0 = 1) (h11 : (s : Matrix (Fin 2) (Fin 2) k) 1 1 = 1)
    (g : GL (Fin 2) k) : WindowedSiegel.localHeight (s * g) = WindowedSiegel.localHeight g := by
  have hrow := WindowedSiegel.rowNormSq_scalar_entries_mul (z := (s : Matrix (Fin 2) (Fin 2) k) 1 1) h10 rfl g
  unfold WindowedSiegel.localHeight
  rw [norm_det_mul_of_upper h10, hrow, h00, h11, norm_one]
  ring

theorem finLocalHeight_mul_of_unipotent {s : GL (Fin 2) k} (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) k) 0 0 = 1) (h11 : (s : Matrix (Fin 2) (Fin 2) k) 1 1 = 1)
    (g : GL (Fin 2) k) : finLocalHeight (s * g) = finLocalHeight g := by
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := by
    unfold rowMaxNorm
    rw [bottom_row_mul h10 g 0, bottom_row_mul h10 g 1, h11, one_mul, one_mul]
  unfold finLocalHeight
  rw [norm_det_mul_of_upper h10, hrow, h00, h11, norm_one, one_mul, one_mul]

theorem finLocalHeight_scalar_mul {a : k} (ha : a ≠ 0)
    (s g : GL (Fin 2) k)
    (h00 : (s : Matrix (Fin 2) (Fin 2) k) 0 0 = a) (h01 : (s : Matrix (Fin 2) (Fin 2) k) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) k) 1 1 = a) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hs : (s : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have hmul : ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = a • (g : Matrix (Fin 2) (Fin 2) k) := by
    rw [coe_mul', hs, smul_mul_assoc, one_mul]
  have hdet : ‖((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det‖ =
      ‖a‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) k).det‖ := by
    rw [hmul, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow]
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ‖a‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := by
    unfold rowMaxNorm
    rw [hmul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, norm_mul, norm_mul,
      mul_max_of_nonneg _ _ (norm_nonneg a)]
  have ha' : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hr : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) k) := rowMaxNorm_pos g
  unfold finLocalHeight
  rw [hdet, hrow, mul_pow]
  field_simp

end HeightLocal

section Height

theorem adelicHeight_unipotentGL2_mul (t : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    adelicHeight K (unipotentGL2 t * g) = adelicHeight K g := by
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · unfold WindowedSiegel.archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_mul, localHeight_mul_of_unipotent] <;> rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul, finLocalHeight_mul_of_unipotent] <;> rfl

theorem idele_arch_ne_zero (z : (AdeleRing (𝓞 K) K)ˣ) (v : InfinitePlace K) :
    (z : AdeleRing (𝓞 K) K).1 v ≠ 0 :=
  (Units.map ((archEval K v).comp (adeleArch (𝓞 K) K)).toMonoidHom z).ne_zero

theorem idele_fin_ne_zero (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (z : AdeleRing (𝓞 K) K).2 v ≠ 0 :=
  (Units.map ((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)).toMonoidHom z).ne_zero

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    adelicHeight K (centralScalar (𝓞 K) K z * g) = adelicHeight K g := by
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul K (z := (z : AdeleRing (𝓞 K) K).1)
      (idele_arch_ne_zero K z) ?_ ?_ ?_ ?_ _
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
    · rw [glArch_apply]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_mul (a := (z : AdeleRing (𝓞 K) K).2 v) (idele_fin_ne_zero K z v)
      _ _ ?_ ?_ ?_ ?_
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl

end Height

section Slices

variable {K}

theorem finite_setOf_exists_ne_zero {f : AdelicGL2 (𝓞 K) K → ℂ} (hfs : HasCompactSupport f)
    (x : AdelicGL2 (𝓞 K) K) {C : Set (AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) :
    {γ : GL (Fin 2) K | ∃ y ∈ C, f (x⁻¹ * globalPoints (𝓞 K) K γ * y) ≠ 0}.Finite := by
  have hC' : IsCompact ((fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => x * p.1 * p.2⁻¹) ''
      (tsupport f ×ˢ C)) :=
    (hfs.prod hC).image (by fun_prop)
  refine (AutomorphicForm.adelicKernelLocalFiniteness K _ hC' 1 1).subset fun γ hγ => ?_
  obtain ⟨y, hy, hne⟩ := hγ
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨(x⁻¹ * globalPoints (𝓞 K) K γ * y, y), ⟨subset_tsupport _ (Function.mem_support.2 hne), hy⟩, ?_⟩
  simp only
  group

theorem continuous_finsum_slice {f : AdelicGL2 (𝓞 K) K → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (S : Set (GL (Fin 2) K)) (x : AdelicGL2 (𝓞 K) K)
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] (c : P → AdelicGL2 (𝓞 K) K) (hc : Continuous c) :
    Continuous fun p => ∑ᶠ γ ∈ S, f (x⁻¹ * globalPoints (𝓞 K) K γ * c p) := by
  classical
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  have hfin := finite_setOf_exists_ne_zero hfs x (hN.image hc)
  set F : Finset (GL (Fin 2) K) := hfin.toFinset with hF

  have heq : (fun p => ∑ᶠ γ ∈ S, f (x⁻¹ * globalPoints (𝓞 K) K γ * c p)) =ᶠ[𝓝 p₀]
      fun p => ∑ γ ∈ F, S.indicator (fun γ => f (x⁻¹ * globalPoints (𝓞 K) K γ * c p)) γ := by
    filter_upwards [hNp] with p hp
    rw [finsum_mem_def]
    refine finsum_eq_sum_of_support_subset _ fun γ hγ => ?_
    rw [hF, Set.Finite.coe_toFinset]
    have hne : f (x⁻¹ * globalPoints (𝓞 K) K γ * c p) ≠ 0 := by
      intro h0
      apply hγ
      simp only [Set.indicator_apply_eq_zero]
      exact fun _ => h0
    exact ⟨c p, Set.mem_image_of_mem c hp, hne⟩
  refine ContinuousAt.congr ?_ heq.symm
  refine (continuous_finsetSum F fun γ _ => ?_).continuousAt
  by_cases hγ : γ ∈ S
  · simp only [Set.indicator_of_mem hγ]
    exact hfc.comp ((continuous_const.mul hc))
  · simp only [Set.indicator_of_notMem hγ]
    exact continuous_const

theorem integrable_finsum_slice_cond {f : AdelicGL2 (𝓞 K) K → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (S : Set (GL (Fin 2) K)) (x g : AdelicGL2 (𝓞 K) K) :
    Integrable (fun t : AdeleRing (𝓞 K) K => ∑ᶠ γ ∈ S, f (x⁻¹ * globalPoints (𝓞 K) K γ * (unipotentGL2 t * g)))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by
  have hcont : Continuous fun t : AdeleRing (𝓞 K) K =>
      ∑ᶠ γ ∈ S, f (x⁻¹ * globalPoints (𝓞 K) K γ * (unipotentGL2 t * g)) :=
    continuous_finsum_slice hfc hfs S x (fun t => unipotentGL2 t * g)
      ((AutomorphicForm.continuous_unipotentGL2).mul continuous_const)
  obtain ⟨C, hC, hbox⟩ := exists_isCompact_adelicBox_subset K
  have hint : IntegrableOn (fun t : AdeleRing (𝓞 K) K =>
      ∑ᶠ γ ∈ S, f (x⁻¹ * globalPoints (𝓞 K) K γ * (unipotentGL2 t * g))) (adelicBox K)
      (adelicAddHaar (𝓞 K) K) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hbox
  have hne : (adelicAddHaar (𝓞 K) K) (adelicBox K) ≠ 0 := (adelicAddHaar_adelicBox_pos K).ne'
  unfold ProbabilityTheory.cond
  exact hint.integrable.smul_measure (ENNReal.inv_ne_top.mpr hne)

end Slices

section Reduction

variable {K}

theorem exists_forall_apply_eq_zero_of_not_upper {f : AdelicGL2 (𝓞 K) K → ℂ} (hfs : HasCompactSupport f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ (x w : AdelicGL2 (𝓞 K) K) (γ : GL (Fin 2) K),
      (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → Real.exp R < adelicHeight K x →
        adelicHeight K (w * x) = adelicHeight K x → f (x⁻¹ * globalPoints (𝓞 K) K γ * (w * x)) = 0 := by
  obtain ⟨κ, Kup, hκ, hdist⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact K (tsupport f) hfs
  refine ⟨-(Real.log κ) / 2, fun R hR x w γ hγ hx hw => ?_⟩
  by_contra hne
  have hk : x⁻¹ * globalPoints (𝓞 K) K γ * (w * x) ∈ tsupport f := subset_tsupport _ (Function.mem_support.2 hne)
  have h1 := (hdist x _ hk).1
  have hxk : x * (x⁻¹ * globalPoints (𝓞 K) K γ * (w * x)) = globalPoints (𝓞 K) K γ * (w * x) := by group
  rw [hxk] at h1
  have hred := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ (w * x)
  rw [hw] at hred
  have hHpos : 0 < adelicHeight K x := adelicHeight_pos x

  have hle : κ * adelicHeight K x * adelicHeight K x ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right h1 hHpos.le) hred

  have hexp : κ⁻¹ ≤ Real.exp R * Real.exp R := by
    rw [← Real.exp_add, ← Real.exp_log (inv_pos.mpr hκ), Real.log_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlt : Real.exp R * Real.exp R < adelicHeight K x * adelicHeight K x :=
    mul_lt_mul'' hx hx (Real.exp_pos R).le (Real.exp_pos R).le
  have : κ⁻¹ < adelicHeight K x * adelicHeight K x := lt_of_le_of_lt hexp hlt
  have h2 : 1 < κ * (adelicHeight K x * adelicHeight K x) := by
    have := mul_lt_mul_of_pos_left this hκ
    rwa [mul_inv_cancel₀ hκ.ne'] at this
  linarith [mul_assoc κ (adelicHeight K x) (adelicHeight K x)]

end Reduction

section CTSplit

variable {K}

theorem indicator_constantTerm_adelicKernel_eq_add {f : AdelicGL2 (𝓞 K) K → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
      Set.indicator (highSet (adelicHeight K) (Real.exp R))
        (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun t => unipotentGL2 t) (fun y => adelicKernel K f x y)) (centralScalar (𝓞 K) K z * x) =
      Set.indicator (highSet (adelicHeight K) (Real.exp R))
        (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun t => unipotentGL2 t) (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
            f (x⁻¹ * globalPoints (𝓞 K) K γ * y))) (centralScalar (𝓞 K) K z * x) +
      Set.indicator (highSet (adelicHeight K) (Real.exp R))
        (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun t => unipotentGL2 t) (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
            f (x⁻¹ * globalPoints (𝓞 K) K γ * y))) (centralScalar (𝓞 K) K z * x) := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_apply_eq_zero_of_not_upper (K := K) hfs
  refine ⟨R₀, fun R hR x z => ?_⟩
  by_cases hhigh : centralScalar (𝓞 K) K z * x ∈ highSet (adelicHeight K) (Real.exp R)
  · rw [Set.indicator_of_mem hhigh, Set.indicator_of_mem hhigh, Set.indicator_of_mem hhigh]
    have hx : Real.exp R < adelicHeight K x := by
      have h := hhigh
      rw [mem_highSet_iff, adelicHeight_centralScalar_mul] at h
      exact h
    unfold constantTerm constantTermIntegrand
    rw [← integral_add (integrable_finsum_slice_cond hfc hfs _ x _) (integrable_finsum_slice_cond hfc hfs _ x _)]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only

    have hw : adelicHeight K (unipotentGL2 t * centralScalar (𝓞 K) K z * x) = adelicHeight K x := by
      rw [mul_assoc, adelicHeight_unipotentGL2_mul, adelicHeight_centralScalar_mul]
    have hvan : ∀ γ : GL (Fin 2) K, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 →
        f (x⁻¹ * globalPoints (𝓞 K) K γ * (unipotentGL2 t * (centralScalar (𝓞 K) K z * x))) = 0 := by
      intro γ hγ
      have h := hR₀ R hR x (unipotentGL2 t * centralScalar (𝓞 K) K z) γ hγ hx hw
      rw [mul_assoc (unipotentGL2 t)] at h
      exact h
    have hfin : (Function.support fun γ : GL (Fin 2) K =>
        f (x⁻¹ * globalPoints (𝓞 K) K γ * (unipotentGL2 t * (centralScalar (𝓞 K) K z * x)))).Finite := by
      refine (finite_setOf_exists_ne_zero hfs x (isCompact_singleton
        (x := unipotentGL2 t * (centralScalar (𝓞 K) K z * x)))).subset fun γ hγ => ?_
      exact ⟨_, Set.mem_singleton _, hγ⟩
    unfold adelicKernel
    rw [← finsum_mem_univ]
    have huniv : (Set.univ : Set (GL (Fin 2) K)) = {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1} ∪ {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1} ∪
        {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0} := by
      ext γ
      simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
      by_cases h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      · by_cases h1 : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1
        · exact Or.inl (Or.inr ⟨h10, h1⟩)
        · exact Or.inl (Or.inl ⟨h10, h1⟩)
      · exact Or.inr h10
    rw [huniv, finsum_mem_union' _ (hfin.subset Set.inter_subset_right) (hfin.subset Set.inter_subset_right),
      finsum_mem_union' _ (hfin.subset Set.inter_subset_right) (hfin.subset Set.inter_subset_right)]
    · rw [finsum_mem_eq_zero_of_forall_eq_zero (s := {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0})
        (fun γ hγ => hvan γ hγ), add_zero]
    · exact Set.disjoint_left.mpr fun γ h₁ h₂ => h₁.2 h₂.2
    · refine Set.disjoint_left.mpr fun γ h₁ h₂ => ?_
      rcases h₁ with h₁ | h₁
      · exact h₂ h₁.1
      · exact h₂ h₁.1
  · rw [Set.indicator_of_notMem hhigh, Set.indicator_of_notMem hhigh, Set.indicator_of_notMem hhigh, add_zero]

end CTSplit

section Algebra

variable {Q G : Type*} [Group G]

theorem lambdaT_eq_of_eq_four_of_indicator_eq_add {_mQ : MeasurableSpace Q} (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ)
    (φ : G → ℂ) (g : G) {a b c d I₁ I₂ : ℂ} (h4 : φ g = a + b + c + d)
    (hI : Set.indicator (highSet H T) (constantTerm μ u φ) g = I₁ + I₂) :
    lambdaT μ u H T φ g = (a + b) + (d - I₂) + (c - I₁) := by
  rw [lambdaT_apply, h4, hI]
  ring

end Algebra

end R1EdCellSplit

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ (x : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
        (@AutomorphicForm.lambdaT _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
              (fun y => AutomorphicForm.adelicKernel K f x y)
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) =
        (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) +
        ((AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) +
        ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) := by

  obtain ⟨R₀, hR₀⟩ := R1EdCellSplit.indicator_constantTerm_adelicKernel_eq_add (K := K) hf hfc
  refine ⟨R₀, fun R hR x z => ?_⟩

  exact R1EdCellSplit.lambdaT_eq_of_eq_four_of_indicator_eq_add _ _ _ _ _ _
    (AutomorphicForm.adelicKernel_eq_four_parts_of_localFiniteness K
      (AutomorphicForm.adelicKernelLocalFiniteness K) hfc.isCompact (subset_tsupport f) x _)
    (hR₀ R hR x z)

end S_AutomorphicForm_exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_lambdaT_adelicKernel_eq_centralElliptic_add_unipotentCell_add_hyperbolicCell (solution)
