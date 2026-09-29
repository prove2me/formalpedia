-- Prove2me | solution 1 for AutomorphicForm.eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f80510a1-354f-5f54-9287-1ba107083cdc

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped NNReal

noncomputable section

namespace R4LevelVoid

open AutomorphicForm Matrix

section FieldMatrices

variable {k : Type*} [Field k]

def dg (a b : kˣ) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : k), 0; 0, (b : k)]
    (by rw [Matrix.det_fin_two_of]; simp [a.ne_zero, b.ne_zero])

def lowerU (y : k) : GL (Fin 2) k := gl2Weyl * unipotentGL2 y * gl2Weyl

theorem dg_val (a b : kˣ) : ((dg a b : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![(a : k), 0; 0, (b : k)] :=
  rfl

theorem lowerU_val (y : k) : ((lowerU y : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, 0; y, 1] := by
  rw [lowerU, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val,
    unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerU_zero : (lowerU (0 : k)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [lowerU_val]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_dg (a : kˣ) (y : k) :
    unipotentGL2 ((a : k) * y) * dg a 1 = dg a 1 * unipotentGL2 y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, dg_val, unipotentGL2_coe,
    unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_dg (a b : kˣ) :
    (gl2Weyl : GL (Fin 2) k) * dg a b = dg b a * gl2Weyl := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, dg_val, dg_val, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerU_mul_dg (a : kˣ) (y : k) :
    lowerU y * dg a 1 = dg a 1 * lowerU ((a : k) * y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, dg_val, lowerU_val, lowerU_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def bU (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(M : Matrix (Fin 2) (Fin 2) k).det / (M : Matrix (Fin 2) (Fin 2) k) 1 1, (M : Matrix (Fin 2) (Fin 2) k) 0 1;
      0, (M : Matrix (Fin 2) (Fin 2) k) 1 1]
    (by
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ h]
      exact Matrix.GeneralLinearGroup.det_ne_zero M)

theorem bU_val (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0) :
    ((bU M h : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(M : Matrix (Fin 2) (Fin 2) k).det / (M : Matrix (Fin 2) (Fin 2) k) 1 1, (M : Matrix (Fin 2) (Fin 2) k) 0 1;
        0, (M : Matrix (Fin 2) (Fin 2) k) 1 1] :=
  rfl

theorem eq_bU_mul_lowerU (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0) :
    M = bU M h * lowerU ((M : Matrix (Fin 2) (Fin 2) k) 1 0 / (M : Matrix (Fin 2) (Fin 2) k) 1 1) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, bU_val, lowerU_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  · field_simp
    ring
  · field_simp

def bW (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![-(M : Matrix (Fin 2) (Fin 2) k).det / (M : Matrix (Fin 2) (Fin 2) k) 1 0, (M : Matrix (Fin 2) (Fin 2) k) 0 0;
      0, (M : Matrix (Fin 2) (Fin 2) k) 1 0]
    (by
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ h, neg_ne_zero]
      exact Matrix.GeneralLinearGroup.det_ne_zero M)

theorem bW_val (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    ((bW M h : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![-(M : Matrix (Fin 2) (Fin 2) k).det / (M : Matrix (Fin 2) (Fin 2) k) 1 0, (M : Matrix (Fin 2) (Fin 2) k) 0 0;
        0, (M : Matrix (Fin 2) (Fin 2) k) 1 0] :=
  rfl

theorem eq_bW_mul_weyl_mul_unipotent (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    M = bW M h * ((gl2Weyl : GL (Fin 2) k) *
      unipotentGL2 ((M : Matrix (Fin 2) (Fin 2) k) 1 1 / (M : Matrix (Fin 2) (Fin 2) k) 1 0)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, bW_val, gl2Weyl_val,
    unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  · field_simp
    ring
  · field_simp

theorem dg_mem_borelSubgroup (a b : kˣ) : dg a b ∈ borelSubgroup k := by
  rw [mem_borelSubgroup_iff, dg_val]; simp

theorem bU_mem_borelSubgroup (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0) :
    bU M h ∈ borelSubgroup k := by
  rw [mem_borelSubgroup_iff, bU_val]; simp

theorem bW_mem_borelSubgroup (M : GL (Fin 2) k) (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    bW M h ∈ borelSubgroup k := by
  rw [mem_borelSubgroup_iff, bW_val]; simp

theorem mul_lowerU_apply_one_zero (M : GL (Fin 2) k) (y : k) :
    ((M * lowerU y : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 =
      (M : Matrix (Fin 2) (Fin 2) k) 1 0 + (M : Matrix (Fin 2) (Fin 2) k) 1 1 * y := by
  rw [Matrix.GeneralLinearGroup.coe_mul, lowerU_val, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem mul_unipotent_apply_one_one (M : GL (Fin 2) k) (y : k) :
    ((M * unipotentGL2 y : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 =
      (M : Matrix (Fin 2) (Fin 2) k) 1 0 * y + (M : Matrix (Fin 2) (Fin 2) k) 1 1 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem apply_one_one_ne_zero_of_apply_one_zero_eq_zero (M : GL (Fin 2) k)
    (h : (M : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) : (M : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0 := by
  intro h'
  apply Matrix.GeneralLinearGroup.det_ne_zero M
  rw [Matrix.det_fin_two]
  simp [h, h']

theorem apply_one_zero_ne_zero_of_apply_one_one_eq_zero (M : GL (Fin 2) k)
    (h : (M : Matrix (Fin 2) (Fin 2) k) 1 1 = 0) : (M : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
  intro h'
  apply Matrix.GeneralLinearGroup.det_ne_zero M
  rw [Matrix.det_fin_two]
  simp [h, h']

end FieldMatrices

section Vanishing

variable {F : Type} [Field F] [NumberField F]

theorem forall_eq_zero_of_apply_uniformizer_mul (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (hf : Continuous f) (ρ : ℂ) (hρ : 1 < ‖ρ‖)
    (hrel : ∀ y, f ((uniformizerUnit F v : v.adicCompletion F) * y) = ρ * f y) :
    ∀ y, f y = 0 := by
  intro y
  set ϖ : v.adicCompletion F := (uniformizerUnit F v : v.adicCompletion F) with hϖdef
  have hpow : ∀ n : ℕ, f (ϖ ^ n * y) = ρ ^ n * f y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hrel, ih, pow_succ', mul_assoc]
  have hϖ : Valued.v ϖ ≤ WithZero.exp (-1 : ℤ) := (valued_uniformizerUnit F v).le
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n * y) Filter.atTop (nhds 0) := by
    have := (Valued.tendsto_zero_pow_of_le_exp_neg_one hϖ).mul_const y
    simpa using this
  have hlim : Filter.Tendsto (fun n : ℕ => ρ ^ n * f y) Filter.atTop (nhds (f 0)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => f (ϖ ^ n * y)) Filter.atTop (nhds (f 0)) :=
      (hf.tendsto 0).comp ht
    refine h1.congr fun n => ?_
    exact hpow n
  by_contra hne
  have hpos : 0 < ‖f y‖ := norm_pos_iff.mpr hne
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop, ‖ρ ^ n * f y‖ < ‖f 0‖ + 1 :=
    hlim.norm.eventually (Iio_mem_nhds (lt_add_one _))
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop, (‖f 0‖ + 1) / ‖f y‖ + 1 ≤ ‖ρ‖ ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  rw [norm_mul, norm_pow] at hn1
  have h3 : (‖f 0‖ + 1) / ‖f y‖ * ‖f y‖ = ‖f 0‖ + 1 := div_mul_cancel₀ _ hpos.ne'
  have h4 : ((‖f 0‖ + 1) / ‖f y‖ + 1) * ‖f y‖ ≤ ‖ρ‖ ^ n * ‖f y‖ :=
    mul_le_mul_of_nonneg_right hn2 hpos.le
  rw [add_mul, h3, one_mul] at h4
  linarith

end Vanishing

section Adelic

variable {F : Type} [Field F] [NumberField F]

def iota (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) →* AdelicGL2 (𝓞 F) F :=
  (AdelicDock.finEmbed (𝓞 F) F).comp (AdelicDock.localEmbed (𝓞 F) F v)

variable (v : HeightOneSpectrum (𝓞 F))

theorem iota_coe_apply (m : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    ((iota v m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        AdelicDock.localMat (𝓞 F) F v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) :
        AdeleRing (𝓞 F) F) :=
  rfl

theorem glArch_iota (m : GL (Fin 2) (v.adicCompletion F)) : glArch (𝓞 F) F (iota v m) = 1 :=
  AdelicDock.glArch_finEmbed _ _ _

theorem glFin_iota (m : GL (Fin 2) (v.adicCompletion F)) :
    glFin (𝓞 F) F (iota v m) = AdelicDock.localEmbed (𝓞 F) F v m :=
  AdelicDock.glFin_finEmbed _ _ _

theorem finComponent_glFin_iota (m : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (iota v m)) = m := by
  rw [glFin_iota, AdelicDock.finComponent_localEmbed_self]

theorem iota_mul_comm (m : GL (Fin 2) (v.adicCompletion F)) {x : AdelicGL2 (𝓞 F) F}
    (hx : finComponent (𝓞 F) F v (glFin (𝓞 F) F x) = 1) : iota v m * x = x * iota v m := by
  refine AutomorphicForm.eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, glArch_iota, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_iota]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, AdelicDock.coe_localEmbed]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self]
      have h1 : (finAdeleEval (𝓞 F) F w).mapMatrix
          ((glFin (𝓞 F) F x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) _) = 1 := by
        ext i j
        have := (Matrix.GeneralLinearGroup.ext_iff _ _).mp hx i j
        rw [finComponent_apply, Units.val_one] at this
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, this]
      rw [h1, mul_one, one_mul]
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 F) F v _ hw, one_mul, mul_one]

theorem finComponent_glFin_compl (g : AdelicGL2 (𝓞 F) F) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F
      ((iota v (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)))⁻¹ * g)) = 1 := by
  rw [map_mul, map_mul, map_inv, map_inv, finComponent_glFin_iota, inv_mul_cancel]

theorem eq_iota_mul_compl (g : AdelicGL2 (𝓞 F) F) :
    g = iota v (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)) *
      ((iota v (finComponent (𝓞 F) F v (glFin (𝓞 F) F g)))⁻¹ * g) := by
  rw [mul_inv_cancel_left]

theorem iota_mem_adelicBorel {m : GL (Fin 2) (v.adicCompletion F)} (hm : m ∈ borelSubgroup (v.adicCompletion F)) :
    iota v m ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff] at hm
  show ((iota v m : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  rw [iota_coe_apply]
  refine Prod.ext ?_ ?_
  · show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0
    exact Matrix.one_apply_ne (by decide)
  · show AdelicDock.localMat (𝓞 F) F v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
    refine FiniteAdeleRing.ext F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.localMat_apply_self, hm]; rfl
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 F) F v _ _ _ hw, Matrix.one_apply_ne (by decide)]; rfl

def ideleAt (a : (v.adicCompletion F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v a)

theorem uniformizerIdele_eq : uniformizerIdele F v = ideleAt v (uniformizerUnit F v) := rfl

theorem ideleAt_one : ideleAt v (1 : (v.adicCompletion F)ˣ) = 1 := by
  rw [ideleAt, map_one, map_one]

theorem borelDiagFst_iota_dg (a b : (v.adicCompletion F)ˣ)
    (h : iota v (dg a b) ∈ adelicBorel (𝓞 F) F) :
    borelDiagFst (⟨iota v (dg a b), h⟩ : ↥(adelicBorel (𝓞 F) F)) = ideleAt v a := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((iota v (dg a b) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = _
  rw [iota_coe_apply]
  refine Prod.ext ?_ ?_
  · show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 = 1
    exact Matrix.one_apply_eq 0
  · show AdelicDock.localMat (𝓞 F) F v ((dg a b : GL (Fin 2) (v.adicCompletion F)) : Matrix _ _ _) 0 0 =
      ((localUnit (𝓞 F) F v a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
    refine FiniteAdeleRing.ext F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.localMat_apply_self, localUnit_apply_self, dg_val]
      simp
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 F) F v _ _ _ hw, localUnit_apply_of_ne (𝓞 F) F v _ hw,
        Matrix.one_apply_eq]

theorem borelDiagSnd_iota_dg (a b : (v.adicCompletion F)ˣ)
    (h : iota v (dg a b) ∈ adelicBorel (𝓞 F) F) :
    borelDiagSnd (⟨iota v (dg a b), h⟩ : ↥(adelicBorel (𝓞 F) F)) = ideleAt v b := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((iota v (dg a b) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = _
  rw [iota_coe_apply]
  refine Prod.ext ?_ ?_
  · show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 = 1
    exact Matrix.one_apply_eq 1
  · show AdelicDock.localMat (𝓞 F) F v ((dg a b : GL (Fin 2) (v.adicCompletion F)) : Matrix _ _ _) 1 1 =
      ((localUnit (𝓞 F) F v b : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
    refine FiniteAdeleRing.ext F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.localMat_apply_self, localUnit_apply_self, dg_val]
      simp
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 F) F v _ _ _ hw, localUnit_apply_of_ne (𝓞 F) F v _ hw,
        Matrix.one_apply_eq]

theorem iota_unipotentGL2 (y : v.adicCompletion F) :
    iota v (unipotentGL2 y) = unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt F v y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [iota_coe_apply, unipotentGL2_coe, unipotentGL2_coe, NumberField.StandardAddChar.adeleSingleAt_apply]
  have hloc : ∀ w : HeightOneSpectrum (𝓞 F),
      AdelicDock.localMat (𝓞 F) F v (!![(1 : v.adicCompletion F), y; 0, 1]) i j w =
        (!![(1 : FiniteAdeleRing (𝓞 F) F), NumberField.StandardAddChar.finAdeleSingleAt F v y; 0, 1] i j) w := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.localMat_apply_self]
      fin_cases i <;> fin_cases j <;>
        simp [NumberField.StandardAddChar.finAdeleSingleAt_apply_self, coe_one_apply, coe_zero_apply]
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 F) F v _ _ _ hw]
      fin_cases i <;> fin_cases j <;>
        simp [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F v y hw, coe_one_apply,
          coe_zero_apply]
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun w => ?_)
  · fin_cases i <;> fin_cases j <;> simp
    all_goals rfl
  · rw [hloc w]
    fin_cases i <;> fin_cases j <;> rfl

theorem continuous_unipotentGL2_adele :
    Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 F) F,
        (((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
          !![1, -x; 0, 1] :=
      fun x => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem continuous_iota_unipotentGL2 :
    Continuous fun y : v.adicCompletion F => iota v (unipotentGL2 y) := by
  have h : (fun y : v.adicCompletion F => iota v (unipotentGL2 y)) =
      fun y => (unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt F v y) : AdelicGL2 (𝓞 F) F) := by
    funext y; exact iota_unipotentGL2 v y
  rw [h]
  exact continuous_unipotentGL2_adele.comp (NumberField.StandardAddChar.continuous_adeleSingleAt F v)

theorem commute_adelicArchGLInclAt_of_glArch_eq_one (w : InfinitePlace F) (y : GL (Fin 2) w.Completion)
    {d : AdelicGL2 (𝓞 F) F} (hd : glArch (𝓞 F) F d = 1) :
    Commute (adelicArchGLInclAt F w y) d := by
  refine AutomorphicForm.eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hd, mul_one, one_mul]
  · rw [map_mul, map_mul, adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl, mul_one, one_mul]

theorem isArchKFinite_comp_mul {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchKFinite F φ)
    {d : AdelicGL2 (𝓞 F) F} (hd : glArch (𝓞 F) F d = 1) :
    IsArchKFinite F (fun x => φ (x * d)) := by
  classical
  intro w
  obtain ⟨s, hs⟩ := hφ w
  let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun f x => f (x * d)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨s.image L, fun k hk => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hk
  have hc : adelicArchGLInclAt F w y * d = d * adelicArchGLInclAt F w y :=
    commute_adelicArchGLInclAt_of_glArch_eq_one w y hd
  have hEq : (fun x => (fun x => φ (x * d)) (x * adelicArchGLInclAt F w y)) =
      L (fun x => φ (x * adelicArchGLInclAt F w y)) := by
    funext x
    show φ (x * adelicArchGLInclAt F w y * d) = φ (x * d * adelicArchGLInclAt F w y)
    rw [mul_assoc, hc, ← mul_assoc]
  rw [hEq, Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem (hs _ ⟨y, hy, rfl⟩)

theorem comp_mul_mem_archCutSubmodule {tys : ArchTypeFamily F} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ archCutSubmodule F tys) {d : AdelicGL2 (𝓞 F) F} (hd : glArch (𝓞 F) F d = 1) :
    (fun x => φ (x * d)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * d)) ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hφ w) ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archTypeSubmoduleAt F w (tys.rep w j)) i ?_
    exact comp_mul_mem_typeSubmodule_of_commute hfi d fun k' =>
      (commute_adelicArchGLInclAt_of_glArch_eq_one w _ hd).symm
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hw => Submodule.add_mem _ hu hw

end Adelic

section Character

variable {F : Type} [Field F] [NumberField F]

def chiB (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : ↥(adelicBorel (𝓞 F) F) →* ℂˣ :=
  (χ₁.comp borelDiagFst) * (χ₂.comp borelDiagSnd)

theorem chiB_apply (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (b : ↥(adelicBorel (𝓞 F) F)) :
    chiB χ₁ χ₂ b = χ₁ (borelDiagFst b) * χ₂ (borelDiagSnd b) := rfl

theorem apply_borel_mul {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) :
    φ (b * g) = ((chiB χ₁ χ₂ ⟨b, hb⟩ : ℂˣ) : ℂ) * φ g := by
  rw [hφ b hb g, chiB_apply, Units.val_mul]

theorem chiB_conj (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x y : ↥(adelicBorel (𝓞 F) F)) :
    chiB χ₁ χ₂ (x * y * x⁻¹) = chiB χ₁ χ₂ y := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

variable (v : HeightOneSpectrum (𝓞 F))

theorem apply_iota_mul_borel {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    {β E : GL (Fin 2) (v.adicCompletion F)} (hβ : β ∈ borelSubgroup (v.adicCompletion F))
    (hE : E ∈ borelSubgroup (v.adicCompletion F)) (rest : GL (Fin 2) (v.adicCompletion F))
    (x : AdelicGL2 (𝓞 F) F) :
    φ (iota v (β * E * rest) * x) =
      ((chiB χ₁ χ₂ ⟨iota v E, iota_mem_adelicBorel v hE⟩ : ℂˣ) : ℂ) * φ (iota v (β * rest) * x) := by
  have hβEβ : β * E * β⁻¹ ∈ borelSubgroup (v.adicCompletion F) := mul_mem (mul_mem hβ hE) (inv_mem hβ)
  have h1 : iota v (β * E * rest) * x = iota v (β * E * β⁻¹) * (iota v (β * rest) * x) := by
    simp only [map_mul, map_inv]
    group
  rw [h1, apply_borel_mul hφ (iota_mem_adelicBorel v hβEβ)]
  congr 2
  have h2 : (⟨iota v (β * E * β⁻¹), iota_mem_adelicBorel v hβEβ⟩ : ↥(adelicBorel (𝓞 F) F)) =
      ⟨iota v β, iota_mem_adelicBorel v hβ⟩ * ⟨iota v E, iota_mem_adelicBorel v hE⟩ *
        (⟨iota v β, iota_mem_adelicBorel v hβ⟩)⁻¹ := by
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h2, chiB_conj]

theorem chiB_iota_dg (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (a b : (v.adicCompletion F)ˣ) :
    chiB χ₁ χ₂ ⟨iota v (dg a b), iota_mem_adelicBorel v (dg_mem_borelSubgroup a b)⟩ =
      χ₁ (ideleAt v a) * χ₂ (ideleAt v b) := by
  rw [chiB_apply, borelDiagFst_iota_dg, borelDiagSnd_iota_dg]

end Character

section Main

variable {F : Type} [Field F] [NumberField F]

theorem eq_zero_of_mem_idealBall_bot {x : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ idealBall (𝓞 F) F (⊥ : Ideal (𝓞 F))) : x = 0 := by
  refine FiniteAdeleRing.ext F fun w => ?_
  have h : Valued.v (x w) ≤ 0 := by
    have := hx w
    rwa [idealBound_bot] at this
  exact (Valuation.zero_iff _).mp (le_antisymm h zero_le')

theorem eq_one_of_mem_principalLevel_bot {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ principalLevel (𝓞 F) F (⊥ : Ideal (𝓞 F)) ⊓ finiteAdelicGL2Subgroup F) : u = 1 := by
  have hpl : u ∈ principalLevel (𝓞 F) F (⊥ : Ideal (𝓞 F)) := (Subgroup.mem_inf.mp hu).1
  have hfin : u ∈ finiteAdelicGL2Subgroup F := (Subgroup.mem_inf.mp hu).2
  rw [mem_principalLevel_iff] at hpl
  obtain ⟨h1, h2⟩ := hpl
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  obtain ⟨u', hu'0, hconj⟩ := h2
  have hu' := mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp (hu'0 : u' ∈ levelOne (𝓞 F) F (⊥ : Ideal (𝓞 F))))
  have harch : glArch (𝓞 F) F u = 1 := hfin

  have h10 : ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0 :=
    eq_zero_of_mem_idealBall_bot h1.1.lowerLeft
  have h11 : ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 :=
    sub_eq_zero.mp (eq_zero_of_mem_idealBall_bot h1.1.lowerRight)
  have h10' : ((glFin (𝓞 F) F u' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0 :=
    eq_zero_of_mem_idealBall_bot hu'.1.lowerLeft
  have h11' : ((glFin (𝓞 F) F u' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 :=
    sub_eq_zero.mp (eq_zero_of_mem_idealBall_bot hu'.1.lowerRight)
  have hu_eq : u = weyl (𝓞 F) F * u' * (weyl (𝓞 F) F)⁻¹ := by rw [← hconj]; rfl
  have hwinv : (weyl (𝓞 F) F)⁻¹ = weyl (𝓞 F) F := Units.ext rfl
  have hW : ∀ i j : Fin 2, ((glFin (𝓞 F) F (weyl (𝓞 F) F) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j = !![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, 0] i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hfin_u : ∀ i j : Fin 2, ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j =
      ∑ b : Fin 2, ∑ a : Fin 2, !![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, 0] i a *
        ((glFin (𝓞 F) F u' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) a b *
          !![(0 : FiniteAdeleRing (𝓞 F) F), 1; 1, 0] b j := by
    intro i j
    conv_lhs => rw [hu_eq, hwinv, map_mul, map_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hW, hW]
  have h00 : ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 = 1 := by
    rw [hfin_u]; simp [Fin.sum_univ_two, h11']
  have h01 : ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 1 = 0 := by
    rw [hfin_u]; simp [Fin.sum_univ_two, h10']
  have hfin : glFin (𝓞 F) F u = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_one]
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11
  refine AutomorphicForm.eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [harch, map_one]
  · rw [hfin, map_one]

def contSubmodule (G : Type*) [TopologicalSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun c _ ha => ha.const_smul c

theorem eq_zero_of_finite (tysF : ArchTypeFamily F) (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hχ₁ : ‖((χ₁ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ < 1) (hχ₂ : 1 < ‖((χ₂ (uniformizerIdele F v) : ℂˣ) : ℂ)‖)
    (n : ℕ) (ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
    (H : ∀ φ₀ : AdelicGL2 (𝓞 F) F → ℂ, IsInducedSection (𝓞 F) F χ₁ χ₂ φ₀ → Continuous φ₀ →
      IsArchKFinite F φ₀ → φ₀ ∈ archCutSubmodule F tysF → φ₀ ∈ Submodule.span ℂ (Set.range ψ))
    (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (h1 : IsInducedSection (𝓞 F) F χ₁ χ₂ φ₀) (h2 : Continuous φ₀)
    (h3 : IsArchKFinite F φ₀) (h4 : φ₀ ∈ archCutSubmodule F tysF) : φ₀ = 0 := by
  classical

  let S : Set (AdelicGL2 (𝓞 F) F → ℂ) := {φ | IsInducedSection (𝓞 F) F χ₁ χ₂ φ ∧ Continuous φ ∧
    IsArchKFinite F φ ∧ φ ∈ archCutSubmodule F tysF}
  let W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ S
  have hWle : W ≤ Submodule.span ℂ (Set.range ψ) :=
    Submodule.span_le.mpr fun φ hφ => H φ hφ.1 hφ.2.1 hφ.2.2.1 hφ.2.2.2
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
  have hWind' : W ≤ inducedSectionSubmodule χ₁ χ₂ :=
    Submodule.span_le.mpr fun φ hφ => (mem_inducedSectionSubmodule_iff χ₁ χ₂).mpr hφ.1
  have hWind : ∀ φ ∈ W, IsInducedSection (𝓞 F) F χ₁ χ₂ φ := fun φ hφ =>
    (mem_inducedSectionSubmodule_iff χ₁ χ₂).mp (hWind' hφ)
  have hWcont' : W ≤ contSubmodule (AdelicGL2 (𝓞 F) F) :=
    Submodule.span_le.mpr fun φ hφ => show φ ∈ contSubmodule (AdelicGL2 (𝓞 F) F) from hφ.2.1
  have hWcont : ∀ φ ∈ W, Continuous φ := fun φ hφ => hWcont' hφ

  set ϖ : (v.adicCompletion F)ˣ := uniformizerUnit F v with hϖ
  let d : AdelicGL2 (𝓞 F) F := iota v (dg ϖ 1)
  have hd : glArch (𝓞 F) F d = 1 := glArch_iota v _
  let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun f x => f (x * d)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hLS : ∀ φ ∈ S, L φ ∈ S := fun φ hφ =>
    ⟨hφ.1.rightTranslate d, hφ.2.1.comp (continuous_mul_const d), isArchKFinite_comp_mul hφ.2.2.1 hd,
      comp_mul_mem_archCutSubmodule hφ.2.2.2 hd⟩
  have hLW : ∀ φ ∈ W, L φ ∈ W := by
    intro φ hφ
    have hmap : W.map L ≤ W := by
      rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨φ', hφ', rfl⟩
      exact Submodule.subset_span (hLS φ' hφ')
    exact hmap (Submodule.mem_map_of_mem hφ)
  let T : Module.End ℂ W := L.restrict hLW

  by_contra hne
  have hφ₀W : φ₀ ∈ W := Submodule.subset_span ⟨h1, h2, h3, h4⟩
  haveI : Nontrivial W := ⟨⟨⟨φ₀, hφ₀W⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨⟨φ, hφW⟩, hφev⟩ := hc.exists_hasEigenvector
  have hφne : φ ≠ 0 := fun h => hφev.2 (Subtype.ext h)
  have hTφ : ∀ x, φ (x * d) = c * φ x := by
    intro x
    have := congrArg (fun u : W => (u : AdelicGL2 (𝓞 F) F → ℂ) x) hφev.apply_eq_smul
    simp [T, LinearMap.restrict_apply] at this
    exact this
  have hind : IsInducedSection (𝓞 F) F χ₁ χ₂ φ := hWind φ hφW
  have hcont : Continuous φ := hWcont φ hφW
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hφne
    funext x
    have := hTφ (x * d⁻¹)
    rw [inv_mul_cancel_right, hc0, zero_mul] at this
    exact this

  have hval₁ : chiB χ₁ χ₂ ⟨iota v (dg ϖ 1), iota_mem_adelicBorel v (dg_mem_borelSubgroup ϖ 1)⟩ =
      χ₁ (uniformizerIdele F v) := by
    rw [chiB_iota_dg, ideleAt_one, map_one, mul_one, uniformizerIdele_eq]
  have hval₂ : chiB χ₁ χ₂ ⟨iota v (dg 1 ϖ), iota_mem_adelicBorel v (dg_mem_borelSubgroup 1 ϖ)⟩ =
      χ₂ (uniformizerIdele F v) := by
    rw [chiB_iota_dg, ideleAt_one, map_one, one_mul, uniformizerIdele_eq]

  have keyW : ‖c‖ ≤ 1 → ∀ (β : GL (Fin 2) (v.adicCompletion F)), β ∈ borelSubgroup (v.adicCompletion F) →
      ∀ x : AdelicGL2 (𝓞 F) F, finComponent (𝓞 F) F v (glFin (𝓞 F) F x) = 1 →
      ∀ y : v.adicCompletion F, φ (iota v (β * ((gl2Weyl : GL (Fin 2) (v.adicCompletion F)) * unipotentGL2 y)) * x) = 0 := by
    intro hcle β hβ x hx
    set f : v.adicCompletion F → ℂ :=
      fun y => φ (iota v (β * ((gl2Weyl : GL (Fin 2) (v.adicCompletion F)) * unipotentGL2 y)) * x) with hf
    have hfc : Continuous f := by
      have : f = fun y => φ (iota v (β * gl2Weyl) * iota v (unipotentGL2 y) * x) := by
        funext y; simp only [hf, map_mul, mul_assoc]
      rw [this]
      exact hcont.comp ((continuous_const.mul (continuous_iota_unipotentGL2 v)).mul continuous_const)
    set ρ : ℂ := ((χ₂ (uniformizerIdele F v) : ℂˣ) : ℂ) / c with hρ
    have hρ1 : 1 < ‖ρ‖ := by
      rw [hρ, norm_div, one_lt_div (norm_pos_iff.mpr hc0)]
      exact lt_of_le_of_lt hcle hχ₂
    have hrel : ∀ y, f ((ϖ : v.adicCompletion F) * y) = ρ * f y := by
      intro y

      have step1 : c * f ((ϖ : v.adicCompletion F) * y) =
          φ (iota v (β * dg 1 ϖ * ((gl2Weyl : GL (Fin 2) (v.adicCompletion F)) * unipotentGL2 y)) * x) := by
        rw [hf]
        dsimp only
        rw [← hTφ, mul_assoc (iota v _) x d, ← iota_mul_comm v _ hx, ← mul_assoc, ← map_mul]
        congr 3
        rw [mul_assoc, mul_assoc, unipotent_mul_dg, ← mul_assoc (gl2Weyl : GL (Fin 2) (v.adicCompletion F)),
          weyl_mul_dg, mul_assoc, mul_assoc]
      have step2 := apply_iota_mul_borel v hind hβ (dg_mem_borelSubgroup 1 ϖ)
        ((gl2Weyl : GL (Fin 2) (v.adicCompletion F)) * unipotentGL2 y) x
      rw [hval₂] at step2
      have : c * f ((ϖ : v.adicCompletion F) * y) = ((χ₂ (uniformizerIdele F v) : ℂˣ) : ℂ) * f y := by
        rw [step1, step2]
      rw [hρ, div_mul_eq_mul_div, ← this, mul_div_cancel_left₀ _ hc0]
    exact forall_eq_zero_of_apply_uniformizer_mul v f hfc ρ hρ1 hrel

  have keyL : 1 < ‖c‖ → ∀ (β : GL (Fin 2) (v.adicCompletion F)), β ∈ borelSubgroup (v.adicCompletion F) →
      ∀ x : AdelicGL2 (𝓞 F) F, finComponent (𝓞 F) F v (glFin (𝓞 F) F x) = 1 →
      ∀ y : v.adicCompletion F, φ (iota v (β * lowerU y) * x) = 0 := by
    intro hclt β hβ x hx
    set h : v.adicCompletion F → ℂ := fun y => φ (iota v (β * lowerU y) * x) with hh
    have hhc : Continuous h := by
      have : h = fun y => φ (iota v (β * gl2Weyl) * iota v (unipotentGL2 y) * (iota v gl2Weyl * x)) := by
        funext y; simp only [hh, lowerU, map_mul, mul_assoc]
      rw [this]
      exact hcont.comp ((continuous_const.mul (continuous_iota_unipotentGL2 v)).mul continuous_const)
    have hχ₁0 : ((χ₁ (uniformizerIdele F v) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    set ρ : ℂ := c / ((χ₁ (uniformizerIdele F v) : ℂˣ) : ℂ) with hρ
    have hρ1 : 1 < ‖ρ‖ := by
      rw [hρ, norm_div, one_lt_div (norm_pos_iff.mpr hχ₁0)]
      exact lt_trans hχ₁ hclt
    have hrel : ∀ y, h ((ϖ : v.adicCompletion F) * y) = ρ * h y := by
      intro y

      have step1 : c * h y = φ (iota v (β * dg ϖ 1 * lowerU ((ϖ : v.adicCompletion F) * y)) * x) := by
        rw [hh]
        dsimp only
        rw [← hTφ, mul_assoc (iota v _) x d, ← iota_mul_comm v _ hx, ← mul_assoc, ← map_mul]
        congr 3
        rw [mul_assoc, lowerU_mul_dg, ← mul_assoc]
      have step2 := apply_iota_mul_borel v hind hβ (dg_mem_borelSubgroup ϖ 1)
        (lowerU ((ϖ : v.adicCompletion F) * y)) x
      rw [hval₁] at step2
      have : c * h y = ((χ₁ (uniformizerIdele F v) : ℂˣ) : ℂ) * h ((ϖ : v.adicCompletion F) * y) := by
        rw [step1, step2]
      rw [hρ, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ hχ₁0]
    exact forall_eq_zero_of_apply_uniformizer_mul v h hhc ρ hρ1 hrel

  have hϖt : Filter.Tendsto (fun k : ℕ => (ϖ : v.adicCompletion F) ^ k) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_le_exp_neg_one (valued_uniformizerUnit F v).le
  have hϖne : ∀ k : ℕ, (ϖ : v.adicCompletion F) ^ k ≠ 0 := fun k => pow_ne_zero k ϖ.ne_zero

  apply hφne
  funext g
  set gv : GL (Fin 2) (v.adicCompletion F) := finComponent (𝓞 F) F v (glFin (𝓞 F) F g) with hgv
  set g' : AdelicGL2 (𝓞 F) F := (iota v gv)⁻¹ * g with hg'
  have hg'v : finComponent (𝓞 F) F v (glFin (𝓞 F) F g') = 1 := finComponent_glFin_compl v g
  have hgeq : g = iota v gv * g' := eq_iota_mul_compl v g
  show φ g = 0
  by_cases hcle : ‖c‖ ≤ 1
  ·
    have hcell : ∀ M : GL (Fin 2) (v.adicCompletion F), (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 →
        φ (iota v M * g') = 0 := by
      intro M hM
      rw [eq_bW_mul_weyl_mul_unipotent M hM]
      exact keyW hcle _ (bW_mem_borelSubgroup M hM) g' hg'v _
    by_cases h10 : (gv : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
    ·
      have h11 : (gv : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 :=
        apply_one_one_ne_zero_of_apply_one_zero_eq_zero gv h10
      have hseq : ∀ k : ℕ, φ (g * iota v (lowerU ((ϖ : v.adicCompletion F) ^ k))) = 0 := by
        intro k
        rw [hgeq, mul_assoc, ← iota_mul_comm v _ hg'v, ← mul_assoc, ← map_mul]
        apply hcell
        rw [mul_lowerU_apply_one_zero, h10, zero_add]
        exact mul_ne_zero h11 (hϖne k)
      have hlim : Filter.Tendsto (fun k : ℕ => φ (g * iota v (lowerU ((ϖ : v.adicCompletion F) ^ k))))
          Filter.atTop (nhds (φ g)) := by
        have hc' : Continuous fun y : v.adicCompletion F => φ (g * iota v (lowerU y)) := by
          have : (fun y : v.adicCompletion F => φ (g * iota v (lowerU y))) =
              fun y => φ (g * iota v gl2Weyl * iota v (unipotentGL2 y) * iota v gl2Weyl) := by
            funext y; simp only [lowerU, map_mul, mul_assoc]
          rw [this]
          exact hcont.comp ((continuous_const.mul (continuous_iota_unipotentGL2 v)).mul continuous_const)
        have := (hc'.tendsto 0).comp hϖt
        simpa [Function.comp_def, lowerU_zero] using this
      exact tendsto_nhds_unique (hlim.congr hseq) tendsto_const_nhds ▸ rfl
    · rw [hgeq]
      exact hcell gv h10
  ·
    have hclt : 1 < ‖c‖ := lt_of_not_ge hcle
    have hcell : ∀ M : GL (Fin 2) (v.adicCompletion F), (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 →
        φ (iota v M * g') = 0 := by
      intro M hM
      rw [eq_bU_mul_lowerU M hM]
      exact keyL hclt _ (bU_mem_borelSubgroup M hM) g' hg'v _
    by_cases h11 : (gv : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0
    ·
      have h10 : (gv : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 :=
        apply_one_zero_ne_zero_of_apply_one_one_eq_zero gv h11
      have hseq : ∀ k : ℕ, φ (g * iota v (unipotentGL2 ((ϖ : v.adicCompletion F) ^ k))) = 0 := by
        intro k
        rw [hgeq, mul_assoc, ← iota_mul_comm v _ hg'v, ← mul_assoc, ← map_mul]
        apply hcell
        rw [mul_unipotent_apply_one_one, h11, add_zero]
        exact mul_ne_zero h10 (hϖne k)
      have hlim : Filter.Tendsto (fun k : ℕ => φ (g * iota v (unipotentGL2 ((ϖ : v.adicCompletion F) ^ k))))
          Filter.atTop (nhds (φ g)) := by
        have hc' : Continuous fun y : v.adicCompletion F => φ (g * iota v (unipotentGL2 y)) :=
          hcont.comp (continuous_const.mul (continuous_iota_unipotentGL2 v))
        have := (hc'.tendsto 0).comp hϖt
        simpa [Function.comp_def] using this
      exact tendsto_nhds_unique (hlim.congr hseq) tendsto_const_nhds ▸ rfl
    · rw [hgeq]
      exact hcell gv h11

end Main

end R4LevelVoid

end

open AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (tysF : ArchTypeFamily F) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
      (t : ℝ) (n : ℕ) (ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ₀ : AdelicGL2 (𝓞 F) F → ℂ,
        IsInducedSection (𝓞 F) F (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite F φ₀ →
        (∀ (g : AdelicGL2 (𝓞 F) F), ∀ u ∈ principalLevel (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule F tysF →
        φ₀ ∈ Submodule.span ℂ (Set.range ψ)) →
    ∀ (φ₀ : AdelicGL2 (𝓞 F) F → ℂ),
      IsInducedSection (𝓞 F) F (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
      Continuous φ₀ → IsArchKFinite F φ₀ → φ₀ ∈ archCutSubmodule F tysF → φ₀ = 0 := by
  intro αm hαm μ ν hμ hν _ _ t n ψ H φ₀ h1 h2 h3 h4

  obtain ⟨v⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  have hnorm : NumberField.TateGlobal.ideleNorm F (uniformizerIdele F v) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := NumberField.TateGlobal.ideleNorm_uniformizerIdele F v
  have hq : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1' : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have : 2 ≤ Ideal.absNorm v.asIdeal := by omega
    exact_mod_cast this
  have hαv : ((αm (uniformizerIdele F v) : ℝˣ) : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
    rw [← hnorm]; rfl
  have hα_lt : ((αm (uniformizerIdele F v) : ℝˣ) : ℝ) < 1 := by
    rw [hαv]; exact inv_lt_one_of_one_lt₀ hq
  have hα_pos : 0 < ((αm (uniformizerIdele F v) : ℝˣ) : ℝ) := hαm _

  have hχ₁ : ‖((etaFst μ αm hαm ((t : ℂ) * Complex.I) (uniformizerIdele F v) : ℂˣ) : ℂ)‖ < 1 := by
    rw [norm_etaFst_apply_of_unitary hμ]
    have hre : ((t : ℂ) * Complex.I).re + 1 / 2 = 1 / 2 := by simp
    rw [hre]
    exact Real.rpow_lt_one hα_pos.le hα_lt (by norm_num)

  have hχ₂ : 1 < ‖((etaSnd ν αm hαm ((t : ℂ) * Complex.I) (uniformizerIdele F v) : ℂˣ) : ℂ)‖ := by
    rw [etaSnd_apply, Units.val_mul, norm_mul, hν, one_mul, norm_cpowChar_apply]
    have hre : (-((t : ℂ) * Complex.I + 1 / 2)).re = -(1 / 2) := by simp
    rw [hre]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hα_pos hα_lt (by norm_num)

  have H' : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsInducedSection (𝓞 F) F (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ →
      Continuous φ → IsArchKFinite F φ → φ ∈ archCutSubmodule F tysF → φ ∈ Submodule.span ℂ (Set.range ψ) := by
    intro φ hφ1 hφ2 hφ3 hφ4
    refine H φ hφ1 hφ2 hφ3 (fun g u hu => ?_) hφ4
    rw [R4LevelVoid.eq_one_of_mem_principalLevel_bot hu, mul_one]
  exact R4LevelVoid.eq_zero_of_finite tysF _ _ v hχ₁ hχ₂ n ψ H' φ₀ h1 h2 h3 h4

end S_AutomorphicForm_eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
end P2MW
export P2MW.S_AutomorphicForm_eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot (solution)
