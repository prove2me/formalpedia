-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5abf8f5e-ba9a-5f0d-8a83-b90a64467ccf

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
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Theorems.Thm_AutomorphicForm_norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Theorems.Thm_AutomorphicForm_sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4WinWindows

section Generic

variable {F : Type*} [NormedField F]

theorem triangular_facts (g : GL (Fin 2) F) (h : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 ∧
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = ((g : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ ∧
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = ((g : Matrix (Fin 2) (Fin 2) F) 1 1)⁻¹ ∧
    (g : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.det_fin_two, h, mul_zero, sub_zero]
  have hdet0 : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [hdet] at hdet0
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet0
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet0
  have hinvmul : ((g⁻¹ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [inv_mul_cancel]; rfl
  have hmulinv : ((g * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [mul_inv_cancel]; rfl
  have e00 := congrFun (congrFun hinvmul 0) 0
  have e11 := congrFun (congrFun hmulinv 1) 1
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, mul_zero, add_zero, Matrix.one_apply_eq] at e00
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, zero_add, Matrix.one_apply_eq] at e11
  refine ⟨h00, h11, ?_, ?_, hdet⟩
  · exact eq_inv_of_mul_eq_one_left e00
  · exact eq_inv_of_mul_eq_one_right e11

theorem exists_window_of_isCompact {M : Set (GL (Fin 2) F)} (hM : IsCompact M) :
    ∃ c : ℝ, ∀ g ∈ M, (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      |Real.log ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1 / (g : Matrix (Fin 2) (Fin 2) F) 0 0‖| ≤ c ∧
      Real.posLog ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1 / (g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ c := by
  have hval : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hinv : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) F => ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  obtain ⟨a00, ha00⟩ := hM.exists_bound_of_continuousOn (hval 0 0).continuousOn
  obtain ⟨a11, ha11⟩ := hM.exists_bound_of_continuousOn (hval 1 1).continuousOn
  obtain ⟨a01, ha01⟩ := hM.exists_bound_of_continuousOn (hval 0 1).continuousOn
  obtain ⟨b00, hb00⟩ := hM.exists_bound_of_continuousOn (hinv 0 0).continuousOn
  obtain ⟨b11, hb11⟩ := hM.exists_bound_of_continuousOn (hinv 1 1).continuousOn
  refine ⟨Real.posLog (a11 * b00) + Real.posLog (a00 * b11) + Real.posLog (a01 * b00), fun g hg h10 => ?_⟩
  obtain ⟨h00, h11, hi00, hi11, -⟩ := triangular_facts g h10
  have hp1 : 0 ≤ Real.posLog (a11 * b00) := Real.posLog_nonneg
  have hp2 : 0 ≤ Real.posLog (a00 * b11) := Real.posLog_nonneg
  have hp3 : 0 ≤ Real.posLog (a01 * b00) := Real.posLog_nonneg
  have hr1 : ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1 / (g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ a11 * b00 := by
    rw [div_eq_mul_inv, norm_mul, ← hi00]
    exact mul_le_mul (ha11 g hg) (hb00 g hg) (norm_nonneg _) ((norm_nonneg _).trans (ha11 g hg))
  have hr2 : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 1‖ ≤ a00 * b11 := by
    rw [div_eq_mul_inv, norm_mul, ← hi11]
    exact mul_le_mul (ha00 g hg) (hb11 g hg) (norm_nonneg _) ((norm_nonneg _).trans (ha00 g hg))
  have hr3 : ‖(g : Matrix (Fin 2) (Fin 2) F) 0 1 / (g : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ a01 * b00 := by
    rw [div_eq_mul_inv, norm_mul, ← hi00]
    exact mul_le_mul (ha01 g hg) (hb00 g hg) (norm_nonneg _) ((norm_nonneg _).trans (ha01 g hg))
  refine ⟨?_, ?_⟩
  · set r := ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1 / (g : Matrix (Fin 2) (Fin 2) F) 0 0‖ with hr
    have hrinv : r⁻¹ = ‖(g : Matrix (Fin 2) (Fin 2) F) 0 0 / (g : Matrix (Fin 2) (Fin 2) F) 1 1‖ := by
      rw [hr, ← norm_inv, inv_div]
    have hlog : Real.log r = Real.posLog r - Real.posLog r⁻¹ := (Real.posLog_sub_posLog_inv).symm
    have h1 : Real.posLog r ≤ Real.posLog (a11 * b00) := Real.posLog_le_posLog (norm_nonneg _) hr1
    have h2 : Real.posLog r⁻¹ ≤ Real.posLog (a00 * b11) := by
      rw [hrinv]; exact Real.posLog_le_posLog (norm_nonneg _) hr2
    have hq1 : 0 ≤ Real.posLog r := Real.posLog_nonneg
    have hq2 : 0 ≤ Real.posLog r⁻¹ := Real.posLog_nonneg
    rw [hlog, abs_le]
    constructor <;> linarith
  · exact (Real.posLog_le_posLog (norm_nonneg _) hr3).trans (by linarith)

theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

end Generic

section LocalGroup

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

local notation "Lw" => w.adicCompletion L
local notation "𝒦" => AutomorphicForm.localIntegralSet L w

theorem inv_mem_KL {k : GL (Fin 2) Lw} (hk : k ∈ 𝒦) : k⁻¹ ∈ 𝒦 :=
  ⟨hk.2, by rw [inv_inv]; exact hk.1⟩

theorem mul_apply_mem_integers {a b : Matrix (Fin 2) (Fin 2) Lw} (ha : ∀ i j, a i j ∈ w.adicCompletionIntegers L)
    (hb : ∀ i j, b i j ∈ w.adicCompletionIntegers L) (i j : Fin 2) :
    (a * b) i j ∈ w.adicCompletionIntegers L := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (ha i 0) (hb 0 j)) (mul_mem (ha i 1) (hb 1 j))

theorem mul_mem_KL {k k' : GL (Fin 2) Lw} (hk : k ∈ 𝒦) (hk' : k' ∈ 𝒦) : k * k' ∈ 𝒦 := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact mul_apply_mem_integers L w hk.1 hk'.1 i j
  · rw [mul_inv_rev, Units.val_mul]
    exact mul_apply_mem_integers L w hk'.2 hk.2 i j

theorem mul_mem_doubleCoset {ρ g k₁ k₂ : GL (Fin 2) Lw}
    (hg : g ∈ 𝒦 * ({ρ} : Set (GL (Fin 2) Lw)) * 𝒦) (hk₁ : k₁ ∈ 𝒦) (hk₂ : k₂ ∈ 𝒦) :
    k₁ * g * k₂ ∈ 𝒦 * ({ρ} : Set (GL (Fin 2) Lw)) * 𝒦 := by
  rw [Set.mem_mul] at hg
  obtain ⟨x, hx, l₂, hl₂, rfl⟩ := hg
  rw [Set.mem_mul] at hx
  obtain ⟨l₁, hl₁, y, hy, rfl⟩ := hx
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have : k₁ * (l₁ * ρ * l₂) * k₂ = (k₁ * l₁) * ρ * (l₂ * k₂) := by group
  rw [this]
  exact Set.mul_mem_mul (Set.mul_mem_mul (mul_mem_KL L w hk₁ hl₁) (Set.mem_singleton _)) (mul_mem_KL L w hl₂ hk₂)

theorem norm_le_one_of_mem_integers {y : Lw} (hy : y ∈ w.adicCompletionIntegers L) : ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hy
  exact (Valued.toNormedField.norm_le_one_iff).2 hy

theorem norm_diag_eq_one_of_mem_KL {g : GL (Fin 2) Lw} (hg : g ∈ 𝒦) (h10 : (g : Matrix (Fin 2) (Fin 2) Lw) 1 0 = 0) :
    ‖(g : Matrix (Fin 2) (Fin 2) Lw) 0 0‖ = 1 ∧ ‖(g : Matrix (Fin 2) (Fin 2) Lw) 1 1‖ = 1 ∧
      ‖(g : Matrix (Fin 2) (Fin 2) Lw) 0 1‖ ≤ 1 := by
  obtain ⟨h00, h11, hi00, hi11, -⟩ := triangular_facts g h10
  have n00 := norm_le_one_of_mem_integers L w (hg.1 0 0)
  have n11 := norm_le_one_of_mem_integers L w (hg.1 1 1)
  have n01 := norm_le_one_of_mem_integers L w (hg.1 0 1)
  have m00 := norm_le_one_of_mem_integers L w (hg.2 0 0)
  have m11 := norm_le_one_of_mem_integers L w (hg.2 1 1)
  rw [hi00, norm_inv] at m00
  rw [hi11, norm_inv] at m11
  have p00 : 0 < ‖(g : Matrix (Fin 2) (Fin 2) Lw) 0 0‖ := norm_pos_iff.2 h00
  have p11 : 0 < ‖(g : Matrix (Fin 2) (Fin 2) Lw) 1 1‖ := norm_pos_iff.2 h11
  refine ⟨le_antisymm n00 ?_, le_antisymm n11 ?_, n01⟩
  · rwa [inv_le_one₀ p00] at m00
  · rwa [inv_le_one₀ p11] at m11

end LocalGroup

theorem logs_of_sq_le {a b e μ : ℝ} (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) (hμ : 1 ≤ μ)
    (h1 : a ^ 2 ≤ μ * (a * b)) (h2 : b ^ 2 ≤ μ * (a * b)) (h3 : e ^ 2 ≤ μ * (a * b)) :
    |Real.log (b / a)| ≤ Real.log μ ∧ Real.posLog (e / a) ≤ Real.log μ := by
  have hμpos : 0 < μ := zero_lt_one.trans_le hμ
  have hab : 0 < a * b := mul_pos ha hb

  have hale : a ≤ μ * b := by
    have : a * a ≤ (μ * b) * a := by nlinarith
    exact le_of_mul_le_mul_right this ha
  have hble : b ≤ μ * a := by
    have : b * b ≤ (μ * a) * b := by nlinarith
    exact le_of_mul_le_mul_right this hb

  have hele : e ≤ μ * a := by
    have h4 : e ^ 2 ≤ (μ * a) ^ 2 := by nlinarith
    have hμa : 0 < μ * a := mul_pos hμpos ha
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [abs_le]
    constructor
    ·
      have : Real.log (a / b) ≤ Real.log μ :=
        Real.log_le_log (div_pos ha hb) ((div_le_iff₀ hb).2 hale)
      rw [Real.log_div ha.ne' hb.ne'] at this
      rw [Real.log_div hb.ne' ha.ne']
      linarith
    · exact Real.log_le_log (div_pos hb ha) ((div_le_iff₀ ha).2 hble)
  · calc Real.posLog (e / a) ≤ Real.posLog μ :=
          Real.posLog_le_posLog (div_nonneg he ha.le) ((div_le_iff₀ ha).2 hele)
      _ = Real.log μ := Real.posLog_eq_log (by rw [abs_of_pos hμpos]; exact hμ)

theorem auxT (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (ρ g : GL (Fin 2) (w.adicCompletion L))
    (hg : g ∈ AutomorphicForm.localIntegralSet L w * ({ρ} : Set (GL (Fin 2) (w.adicCompletion L))) *
      AutomorphicForm.localIntegralSet L w)
    {a b e : w.adicCompletion L}
    (ha : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 0 0 = a)
    (hb : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 1 1 = b)
    (he : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 0 1 = e)
    (h10 : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 1 0 = 0) {μ : ENNReal}
    (hμ : AutomorphicForm.localHaar L w (AutomorphicForm.localIntegralSet L w *
      ({ρ} : Set (GL (Fin 2) (w.adicCompletion L))) * AutomorphicForm.localIntegralSet L w) = μ) :
    |Real.log ‖b / a‖| ≤ 1 * (1 + Real.log μ.toReal) ∧ Real.posLog ‖e / a‖ ≤ 1 * (1 + Real.log μ.toReal) := by
  obtain ⟨hμ1, hμtop, hbound⟩ := AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det L w ρ
  rw [hμ] at hμ1 hμtop hbound
  have hμr1 : 1 ≤ μ.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hμtop.ne).2 hμ1
    simpa using this
  have hlogμ := Real.log_nonneg hμr1
  obtain ⟨-, hsq⟩ := hbound _ hg
  obtain ⟨h00, h11, -, -, hdet⟩ := triangular_facts _ h10
  have hapos := norm_pos_iff.2 h00
  have hbpos := norm_pos_iff.2 h11
  have s00 := hsq 0 0
  have s11 := hsq 1 1
  have s01 := hsq 0 1
  rw [hdet, norm_mul] at s00 s11 s01
  obtain ⟨hl, hp⟩ := logs_of_sq_le hapos hbpos (norm_nonneg _) hμr1 s00 s11 s01
  rw [ha, hb] at hl
  rw [ha, he] at hp
  rw [norm_div, norm_div]
  refine ⟨hl.trans ?_, hp.trans ?_⟩ <;> linarith

theorem auxT' (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (g : GL (Fin 2) (w.adicCompletion L)) (hg : g ∈ AutomorphicForm.localIntegralSet L w)
    {a b e : w.adicCompletion L}
    (ha : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 0 0 = a)
    (hb : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 1 1 = b)
    (he : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 0 1 = e)
    (h10 : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 1 0 = 0) {μ : ENNReal}
    (hμ1 : 1 ≤ μ) (hμtop : μ < ⊤) :
    |Real.log ‖b / a‖| ≤ 1 * (1 + Real.log μ.toReal) ∧ Real.posLog ‖e / a‖ ≤ 1 * (1 + Real.log μ.toReal) := by
  have hμr1 : 1 ≤ μ.toReal := by
    have := (ENNReal.toReal_le_toReal (by simp) hμtop.ne).2 hμ1
    simpa using this
  have hlogμ := Real.log_nonneg hμr1
  obtain ⟨n00, n11, n01⟩ := norm_diag_eq_one_of_mem_KL L w hg h10
  rw [ha] at n00
  rw [hb] at n11
  rw [he] at n01
  refine ⟨?_, ?_⟩
  · rw [norm_div, n00, n11, div_one, Real.log_one, abs_zero]; linarith
  · rw [norm_div, n00, div_one, (Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact n01)]
    linarith

theorem auxU (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (g : GL (Fin 2) (w.adicCompletion L)) (hg : g ∈ AutomorphicForm.localIntegralSet L w)
    {a b e : w.adicCompletion L}
    (ha : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 0 0 = a)
    (hb : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 1 1 = b)
    (he : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 0 1 = e)
    (h10 : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) 1 0 = 0) :
    ‖b / a‖ = 1 ∧ ‖e / a‖ ≤ 1 := by
  obtain ⟨n00, n11, n01⟩ := norm_diag_eq_one_of_mem_KL L w hg h10
  rw [ha] at n00
  rw [hb] at n11
  rw [he] at n01
  refine ⟨?_, ?_⟩
  · rw [norm_div, n00, n11, div_one]
  · rw [norm_div, n00, div_one]; exact n01

end R4WinWindows

namespace R4WinWindows

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev eW (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    L ⊗[K] v.adicCompletion K →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
      L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L)

abbrev plMap (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map (eW K L v w)

theorem continuous_eW (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) : Continuous (eW K L v w) := by
  show Continuous ((fun f : (Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) => f w) ∘
    (fun x => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x))
  refine (continuous_apply w).comp ?_
  have : (fun x => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x) =
      fun x => AutomorphicForm.semiLocalHomeomorph K L v x := by
    funext x; rw [AutomorphicForm.semiLocalHomeomorph_eq]
  rw [this]
  exact (AutomorphicForm.semiLocalHomeomorph K L v).continuous

theorem continuous_plMap (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) : Continuous (plMap K L v w) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact continuous_glMap _ (continuous_eW K L v w)

theorem plMap_semiLocalComponent_apply (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((plMap K L v w (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L g)) :
        GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 w.1 : w.1.adicCompletion L) := by
  show eW K L v w (AutomorphicForm.semiLocalEval K L v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2)) = _
  rw [AutomorphicForm.semiLocalEval_eq]
  show (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
    ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm _)) w = _
  rw [AlgEquiv.apply_symm_apply]

theorem archComponent_glArch_apply (w : InfinitePlace L) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((archComponent L w (glArch (𝓞 L) L g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 w : w.Completion) := rfl

theorem plMap_mem_localIntegralSet_of_mem (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    {k : AutomorphicForm.AdelicGL2 (𝓞 L) L} (hk : k ∈ AutomorphicForm.adelicMaximalCompact L) :
    plMap K L v w (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L k)) ∈
      AutomorphicForm.localIntegralSet L w.1 := by
  have h := fun i j => AutomorphicForm.valued_finComponent_apply_le_one hk w.1 i j
  have heq : plMap K L v w (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L k)) =
      finComponent (𝓞 L) L w.1 (glFin (𝓞 L) L k) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [plMap_semiLocalComponent_apply, finComponent_apply, glFin_apply]
  rw [heq]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h i j).1
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h i j).2

end R4WinWindows

set_option maxHeartbeats 3200000 in
open R4WinWindows AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∃ cS cinf : ℝ,
      ∀ (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) →
      ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      ∀ (b : AdelicGL2 (𝓞 L) L), b ∈ AutomorphicForm.adelicBorel (𝓞 L) L →
      ∀ (k : AdelicGL2 (𝓞 L) L), k ∈ AutomorphicForm.adelicMaximalCompact L →
      ∀ (z : (AdeleRing (𝓞 L) L)ˣ),
        φ ((b * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (b * k))) ≠ 0 →
      ∀ (A B E : AdeleRing (𝓞 L) L),
        ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = A →
        ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = B →
        ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = E →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T → ∀ w : v.Extension (𝓞 L),
            ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ = 1 ∧ ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ 1) ∧
        (∀ v ∈ T, ∀ w : v.Extension (𝓞 L),
            |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤
              A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal) ∧
            Real.posLog ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤
              A₀ * (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                semiLocalIntegralSet K L v)).toReal)) ∧
        (∀ v ∈ S, v ∉ T → ∀ w : v.Extension (𝓞 L),
            |Real.log ‖((B.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖| ≤ cS ∧ Real.posLog ‖((E.2 w.1 : (w.1).adicCompletion L) / (A.2 w.1 : (w.1).adicCompletion L))‖ ≤ cS) ∧
        (∀ w : NumberField.InfinitePlace L,
            |Real.log ‖((B.1 w : w.Completion) / (A.1 w : w.Completion))‖| ≤ cinf ∧ Real.posLog ‖((E.1 w : w.Completion) / (A.1 w : w.Completion))‖ ≤ cinf) := by
  intro T ws
  classical
  haveI hFT : ∀ v : HeightOneSpectrum (𝓞 K), Fintype (v.Extension (𝓞 L)) := fun v =>
    @Fintype.ofFinite _ (HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v)

  set G := AdelicGL2 (𝓞 L) L with hGdef
  set KK : Set G := (adelicMaximalCompact L : Set G) with hKK
  have hKKc : IsCompact KK := isCompact_adelicMaximalCompact (K := L)
  set gp := globalPoints (𝓞 L) L with hgp
  set σA := sigmaAdelicAct K L D σ with hσA
  set cs := centralScalar (𝓞 L) L with hcs

  set Mv : ∀ v : HeightOneSpectrum (𝓞 K), Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := fun v =>
    (fun p : G × GL (Fin 2) (L ⊗[K] v.adicCompletion K) × G =>
      semiLocalComponent K L v (glFin (𝓞 L) L p.1) * p.2.1 * (semiLocalComponent K L v (glFin (𝓞 L) L p.2.2))⁻¹) '' (KK ×ˢ tsupport (φS v) ×ˢ KK) with hMv
  have hMvc : ∀ v, IsCompact (tsupport (φS v)) → IsCompact (Mv v) := by
    intro v hv
    haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
    refine (hKKc.prod (hv.prod hKKc)).image ?_
    have hc : Continuous fun g : G => semiLocalComponent K L v (glFin (𝓞 L) L g) :=
      (continuous_semiLocalComponent K L v).comp (continuous_glFin (𝓞 L) L)
    exact ((hc.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
      ((hc.comp (continuous_snd.comp continuous_snd)).inv)
  set cSfun : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L) → ℝ := fun v w =>
    if h : IsCompact (tsupport (φS v)) then
      Classical.choose (exists_window_of_isCompact (((hMvc v h).image (continuous_plMap K L v w))))
    else 0 with hcSfun
  have hcSfun_spec : ∀ v (h : IsCompact (tsupport (φS v))) (w : v.Extension (𝓞 L)),
      ∀ g ∈ plMap K L v w '' Mv v, ((g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 →
        |Real.log ‖((g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 /
            ((g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0‖| ≤ cSfun v w ∧
        Real.posLog ‖((g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 1 /
            ((g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0‖ ≤ cSfun v w := by
    intro v h w
    have : cSfun v w = Classical.choose (exists_window_of_isCompact (((hMvc v h).image (continuous_plMap K L v w)))) := by
      simp only [hcSfun, dif_pos h]
    rw [this]
    exact Classical.choose_spec (exists_window_of_isCompact (((hMvc v h).image (continuous_plMap K L v w))))
  set cS : ℝ := ∑ v ∈ S, ∑ w : v.Extension (𝓞 L), max (cSfun v w) 0 with hcS
  have hcS_ge : ∀ v ∈ S, ∀ w : v.Extension (𝓞 L), cSfun v w ≤ cS := by
    intro v hv w
    calc cSfun v w ≤ max (cSfun v w) 0 := le_max_left _ _
      _ ≤ ∑ w' : v.Extension (𝓞 L), max (cSfun v w') 0 :=
          Finset.single_le_sum (f := fun w' => max (cSfun v w') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ w)
      _ ≤ cS := Finset.single_le_sum (f := fun v' => ∑ w' : v'.Extension (𝓞 L), max (cSfun v' w') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) hv
  set Minf : Set (GL (Fin 2) (InfiniteAdeleRing L)) :=
    (fun p : G × GL (Fin 2) (InfiniteAdeleRing L) × G =>
      glArch (𝓞 L) L p.1 * p.2.1 * (glArch (𝓞 L) L p.2.2)⁻¹) '' (KK ×ˢ tsupport φa ×ˢ KK) with hMinf
  have hMinfc : IsCompact (tsupport φa) → IsCompact Minf := by
    intro h
    refine (hKKc.prod (h.prod hKKc)).image ?_
    have hc : Continuous fun g : G => glArch (𝓞 L) L g := continuous_glArch (𝓞 L) L
    exact ((hc.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
      ((hc.comp (continuous_snd.comp continuous_snd)).inv)
  set cinfFun : InfinitePlace L → ℝ := fun w =>
    if h : IsCompact (tsupport φa) then
      Classical.choose (exists_window_of_isCompact (((hMinfc h).image (continuous_archComponent L w))))
    else 0 with hcinfFun
  have hcinfFun_spec : ∀ (h : IsCompact (tsupport φa)) (w : InfinitePlace L),
      ∀ g ∈ archComponent L w '' Minf, ((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 →
        |Real.log ‖((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 /
            ((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0‖| ≤ cinfFun w ∧
        Real.posLog ‖((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 /
            ((g : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0‖ ≤ cinfFun w := by
    intro h w
    have : cinfFun w = Classical.choose (exists_window_of_isCompact (((hMinfc h).image (continuous_archComponent L w)))) := by
      simp only [hcinfFun, dif_pos h]
    rw [this]
    exact Classical.choose_spec (exists_window_of_isCompact (((hMinfc h).image (continuous_archComponent L w))))
  set cinf : ℝ := ∑ w : InfinitePlace L, max (cinfFun w) 0 with hcinf
  have hcinf_ge : ∀ w, cinfFun w ≤ cinf := fun w =>
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun w' => max (cinfFun w') 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ w))
  refine ⟨1, zero_le_one, cS, cinf, ?_⟩

  intro ρ φ φf hfac t ht10 ht01 b hb k hk z hne A B E hA hB hE
  obtain ⟨hφa, hφf, hφS, hprod, hvan, hφ⟩ := hfac
  set g' : G := b⁻¹ * gp t * σA (cs z * b) with hg'
  set x : G := (b * k)⁻¹ * gp t * σA (cs z * (b * k)) with hxdef
  have hσk : σA k ∈ adelicMaximalCompact L :=
    (sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct K L D σ).1 ⟨k, hk⟩
  have hx : x = k⁻¹ * g' * σA k := by
    rw [hxdef, hg', ← mul_assoc (cs z) b k, map_mul σA (cs z * b) k, mul_inv_rev]; group
  have hg'x : g' = k * x * (σA k)⁻¹ := by rw [hx]; group

  have hg'10 : (g' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 := by
    have h1 : b⁻¹ ∈ adelicBorel (𝓞 L) L := (adelicBorel (𝓞 L) L).inv_mem hb
    have h2 : gp t ∈ adelicBorel (𝓞 L) L := by
      show ((gp t : G) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
      show algebraMap L (AdeleRing (𝓞 L) L) ((t : Matrix (Fin 2) (Fin 2) L) 1 0) = 0
      rw [ht10, map_zero]
    have h3 : cs z * b ∈ adelicBorel (𝓞 L) L := by
      refine (adelicBorel (𝓞 L) L).mul_mem ?_ hb
      show ((cs z : G) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
      show (Matrix.diagonal (fun _ => (z : AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
      exact Matrix.diagonal_apply_ne _ (by decide)
    have h4 : σA (cs z * b) ∈ adelicBorel (𝓞 L) L := by
      have h3' : ((cs z * b : G) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 := h3
      show ((σA (cs z * b) : G) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0
      show (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom (((cs z * b : G) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0) = 0
      rw [h3', map_zero]
    exact ((adelicBorel (𝓞 L) L).mul_mem ((adelicBorel (𝓞 L) L).mul_mem h1 h2) h4)

  have hne' : φ x ≠ 0 := hne
  rw [hφ x] at hne'
  have hφax : φa (glArch (𝓞 L) L x) ≠ 0 := left_ne_zero_of_mul hne'
  have hφfx : φf (glFin (𝓞 L) L x) ≠ 0 := right_ne_zero_of_mul hne'
  have hint : ∀ v ∉ S ∪ T, semiLocalComponent K L v (glFin (𝓞 L) L x) ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra hnot
    exact hφfx (hvan _ ⟨v, hv, hnot⟩)
  have hfactor : ∀ v ∈ S ∪ T,
      (if v ∈ T then fun y : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
            semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) y
        else φS v) (semiLocalComponent K L v (glFin (𝓞 L) L x)) ≠ 0 := by
    have h := hprod (glFin (𝓞 L) L x) hint
    rw [h] at hφfx
    exact fun v hv => (Finset.prod_ne_zero_iff.1 hφfx) v hv
  have hT : ∀ v ∈ T, semiLocalComponent K L v (glFin (𝓞 L) L x) ∈
      semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
        semiLocalIntegralSet K L v := by
    intro v hv
    have h := hfactor v (Finset.mem_union_right _ hv)
    simp only [if_pos hv] at h
    exact Set.mem_of_indicator_ne_zero h
  have hSm : ∀ v ∈ S, v ∉ T → semiLocalComponent K L v (glFin (𝓞 L) L x) ∈ tsupport (φS v) := by
    intro v hv hvT
    have h := hfactor v (Finset.mem_union_left _ hv)
    simp only [if_neg hvT] at h
    exact subset_tsupport _ h
  have hxarch : glArch (𝓞 L) L x ∈ tsupport φa := subset_tsupport _ hφax

  have hplg' : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)),
      plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) =
        plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L k)) * plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L x)) *
          (plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L (σA k))))⁻¹ := by
    intro v w
    rw [hg'x]
    simp only [map_mul, map_inv]
  have hentries : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)),
      ((plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 = A.2 w.1 ∧
      ((plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 = B.2 w.1 ∧
      ((plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 1 = E.2 w.1 ∧
      ((plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 := by
    intro v w
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [plMap_semiLocalComponent_apply]
    · rw [hA]
    · rw [hB]
    · rw [hE]
    · rw [hg'10, ← adeleFin_apply (𝓞 L) L, map_zero, ← finAdeleEval_apply (𝓞 L) L w.1, map_zero]
  have haentries : ∀ w : InfinitePlace L,
      ((archComponent L w (glArch (𝓞 L) L g') : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = A.1 w ∧
      ((archComponent L w (glArch (𝓞 L) L g') : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = B.1 w ∧
      ((archComponent L w (glArch (𝓞 L) L g') : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = E.1 w ∧
      ((archComponent L w (glArch (𝓞 L) L g') : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    intro w
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [archComponent_glArch_apply]
    · rw [hA]
    · rw [hB]
    · rw [hE]
    · rw [hg'10, ← adeleArch_apply (𝓞 L) L, map_zero, ← archEval_apply L w (0 : InfiniteAdeleRing L), map_zero]

  have hkw : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)),
      plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L k)) ∈ localIntegralSet L w.1 :=
    fun v w => plMap_mem_localIntegralSet_of_mem K L v w hk
  have hσkw : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)),
      plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L (σA k))) ∈ localIntegralSet L w.1 :=
    fun v w => plMap_mem_localIntegralSet_of_mem K L v w hσk

  have hcard := fun v : HeightOneSpectrum (𝓞 K) =>
    AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
      K L v
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro v hv w
    obtain ⟨h1, -, -, -, -⟩ := hcard v
    have hxw : plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L x)) ∈ localIntegralSet L w.1 :=
      (h1 _).1 (hint v hv) w
    have hg'w : plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) ∈ localIntegralSet L w.1 := by
      rw [hplg']
      exact mul_mem_KL L w.1 (mul_mem_KL L w.1 (hkw v w) hxw) (inv_mem_KL L w.1 (hσkw v w))
    obtain ⟨e00, e11, e01, e10⟩ := hentries v w
    exact auxU L w.1 _ hg'w e00 e11 e01 e10
  ·
    intro v hv w
    obtain ⟨h1, -, h3, h4, -⟩ := hcard v
    obtain ⟨hxw0, hxw⟩ := (h3 (ws v) (ρ v) _).1 (hT v hv)
    have hHaar := h4 (ws v) (ρ v)
    rcases eq_or_ne w (ws v) with rfl | hw
    · obtain ⟨e00, e11, e01, e10⟩ := hentries v (ws v)
      have hg'w : plMap K L v (ws v) (semiLocalComponent K L v (glFin (𝓞 L) L g')) ∈
          localIntegralSet L (ws v).1 * ({ρ v} : Set (GL (Fin 2) ((ws v).1.adicCompletion L))) *
            localIntegralSet L (ws v).1 := by
        rw [hplg']
        exact mul_mem_doubleCoset L (ws v).1 hxw0 (hkw v (ws v)) (inv_mem_KL L (ws v).1 (hσkw v (ws v)))
      exact auxT L (ws v).1 (ρ v) _ hg'w e00 e11 e01 e10 hHaar.symm
    · obtain ⟨e00, e11, e01, e10⟩ := hentries v w
      have hg'w : plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) ∈ localIntegralSet L w.1 := by
        rw [hplg']
        exact mul_mem_KL L w.1 (mul_mem_KL L w.1 (hkw v w) (hxw w hw)) (inv_mem_KL L w.1 (hσkw v w))
      obtain ⟨hμ1, hμtop, -⟩ :=
        AutomorphicForm.norm_apply_sq_le_localHaar_doubleCoset_mul_norm_det L (ws v).1 (ρ v)
      rw [← hHaar] at hμ1 hμtop
      exact auxT' L w.1 _ hg'w e00 e11 e01 e10 hμ1 hμtop
  ·
    intro v hv hvT w
    have hcpt : IsCompact (tsupport (φS v)) := by
      have h := hφS v (Finset.mem_union_left _ hv)
      simp only [if_neg hvT] at h
      exact h.2.isCompact
    have hcomp : semiLocalComponent K L v (glFin (𝓞 L) L g') =
        semiLocalComponent K L v (glFin (𝓞 L) L k) * semiLocalComponent K L v (glFin (𝓞 L) L x) *
          (semiLocalComponent K L v (glFin (𝓞 L) L (σA k)))⁻¹ := by
      rw [hg'x]; simp only [map_mul, map_inv]
    have hmem : plMap K L v w (semiLocalComponent K L v (glFin (𝓞 L) L g')) ∈ plMap K L v w '' Mv v :=
      ⟨semiLocalComponent K L v (glFin (𝓞 L) L g'),
        ⟨⟨k, semiLocalComponent K L v (glFin (𝓞 L) L x), σA k⟩, ⟨hk, hSm v hv hvT, hσk⟩, hcomp.symm⟩, rfl⟩
    obtain ⟨e00, e11, e01, e10⟩ := hentries v w
    obtain ⟨hl, hp⟩ := hcSfun_spec v hcpt w _ hmem e10
    rw [e00, e11] at hl
    rw [e00, e01] at hp
    exact ⟨hl.trans (hcS_ge v hv w), hp.trans (hcS_ge v hv w)⟩
  ·
    intro w
    have hcpt : IsCompact (tsupport φa) := hφa.2.isCompact
    have hcomp : glArch (𝓞 L) L g' = glArch (𝓞 L) L k * glArch (𝓞 L) L x * (glArch (𝓞 L) L (σA k))⁻¹ := by
      rw [hg'x]; simp only [map_mul, map_inv]
    have hmem : archComponent L w (glArch (𝓞 L) L g') ∈ archComponent L w '' Minf :=
      ⟨glArch (𝓞 L) L g', ⟨⟨k, glArch (𝓞 L) L x, σA k⟩, ⟨hk, hxarch, hσk⟩, hcomp.symm⟩, rfl⟩
    obtain ⟨e00, e11, e01, e10⟩ := haentries w
    obtain ⟨hl, hp⟩ := hcinfFun_spec hcpt w _ hmem e10
    rw [e00, e11] at hl
    rw [e00, e01] at hp
    exact ⟨hl.trans (hcinf_ge w), hp.trans (hcinf_ge w)⟩

end

end S_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero (solution)
