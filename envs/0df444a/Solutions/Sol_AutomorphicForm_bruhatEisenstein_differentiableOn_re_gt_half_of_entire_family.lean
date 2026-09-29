-- Prove2me | solution 1 for AutomorphicForm.bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e1c66bbd-c0a0-5583-a345-66e6fc5c3dc3

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_WeylSelectors
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace SolE_j1

open AutomorphicForm AutomorphicForm.WeylIntegrable

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

private def bMat (ε y z : A) : Matrix (Fin 2) (Fin 2) A := !![1 - ε - ε * z, ε; 0, y]

private def mMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A := !![ε, 1 - ε; 1 - ε + ε * z, (1 - ε) * x + ε]

private def mInvMat (ε z x : A) : Matrix (Fin 2) (Fin 2) A :=
  !![(2 * ε - 1) * ((1 - ε) * x + ε), -((2 * ε - 1) * (1 - ε)); -((2 * ε - 1) * (1 - ε + ε * z)), (2 * ε - 1) * ε]

private theorem det_bMat (h : SelRel ε y z x) : (bMat ε y z).det = 1 - 2 * ε := by
  rw [bMat, Matrix.det_fin_two_of]
  linear_combination h.small - ε * h.yz

private theorem one_sub_two_mul_sq (h : SelRel ε y z x) : (1 - 2 * ε) * (1 - 2 * ε) = 1 := by
  linear_combination 4 * h.idem

private theorem isUnit_det_bMat (h : SelRel ε y z x) : IsUnit (bMat ε y z).det := by
  rw [det_bMat h]; exact (Units.mkOfMulEqOne _ _ (one_sub_two_mul_sq h)).isUnit

private def bFactor (h : SelRel ε y z x) : GL (Fin 2) A := Matrix.nonsingInvUnit (bMat ε y z) (isUnit_det_bMat h)

@[scoped simp] private theorem coe_bFactor (h : SelRel ε y z x) : (bFactor h : Matrix (Fin 2) (Fin 2) A) = bMat ε y z := rfl

private theorem bFactor_mem_borel (h : SelRel ε y z x) : bFactor h ∈ borelSubgroup A := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0
  simp [bMat]

private theorem borelDiagFst_bFactor_val (h : SelRel ε y z x) :
    ((borelDiagFst ⟨bFactor h, bFactor_mem_borel h⟩ : Aˣ) : A) = 1 - ε - ε * z := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 0 0 = _
  simp [bMat]

private theorem borelDiagSnd_bFactor_val (h : SelRel ε y z x) :
    ((borelDiagSnd ⟨bFactor h, bFactor_mem_borel h⟩ : Aˣ) : A) = y := by
  show (bFactor h : Matrix (Fin 2) (Fin 2) A) 1 1 = _
  simp [bMat]

private theorem bMat_mul_mMat (h : SelRel ε y z x) : bMat ε y z * mMat ε z x = !![0, 1; 1, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bMat, mMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-2) * h.idem
  · linear_combination (2 + z - x) * h.idem
  · linear_combination h.small + ε * h.yz
  · linear_combination x * h.small + h.big

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

omit [NumberField F] in
private theorem norm_inv_lt_one_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : ‖(a w)⁻¹‖ < 1 := by
  rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h

end Adelic

section Generic2

variable {A : Type*} [CommRing A] {ε y z x : A}

private def eUnit (h : SelRel ε y z x) : Aˣ := ⟨1 - 2 * ε, 1 - 2 * ε, one_sub_two_mul_sq h, one_sub_two_mul_sq h⟩

@[scoped simp] private theorem coe_eUnit (h : SelRel ε y z x) : (eUnit h : A) = 1 - 2 * ε := rfl

private theorem eUnit_mul_self (h : SelRel ε y z x) : eUnit h * eUnit h = 1 := Units.ext (one_sub_two_mul_sq h)

private theorem borelDiagFst_bFactor (h : SelRel ε y z x) : borelDiagFst ⟨bFactor h, bFactor_mem_borel h⟩ = eUnit h * (yUnit h)⁻¹ := by
  apply Units.ext
  rw [borelDiagFst_bFactor_val, Units.val_mul, coe_eUnit, coe_yUnit_inv]
  linear_combination (2 * z - 2) * h.idem

private theorem borelDiagSnd_bFactor (h : SelRel ε y z x) : borelDiagSnd ⟨bFactor h, bFactor_mem_borel h⟩ = yUnit h :=
  Units.ext (borelDiagSnd_bFactor_val h)

private theorem mMat_mul_mInvMat (h : SelRel ε y z x) : mMat ε z x * mInvMat ε z x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mMat, mInvMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (4 - (2 * ε - 1) * x + (2 * ε - 1) * z) * h.idem
  · ring
  · ring
  · linear_combination (4 + (2 * ε - 1) * z - (2 * ε - 1) * x) * h.idem

end Generic2

section Adelic2

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

private theorem adelicWeyl_inv' : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

private theorem coe_adelicWeyl_mul_unipotent (u : 𝔸) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, u] := by
  rw [adelicWeyl_inv', Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  have hw : ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) = !![0, 1; 1, 0] := by
    ext i j
    rw [adelicWeyl, globalPoints_apply]
    fin_cases i <;> fin_cases j <;> simp [gl2Weyl]
  rw [hw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def mFactor (a : 𝔸∞) (b : 𝔸f) : AdelicGL2 (𝓞 F) F :=
  (bFactor (selRel F a b))⁻¹ * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (toAdele' F a b))

private theorem weyl_unipotent_eq (u : 𝔸) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u = bFactor (selRel F u.1 u.2) * mFactor F u.1 u.2 := by
  rw [mFactor, mul_inv_cancel_left]; rfl

private theorem coe_mFactor (a : 𝔸∞) (b : 𝔸f) : ((mFactor F a b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) =
    mMat (selE F a b) (selZ F a b) (toAdele' F a b) := by
  rw [mFactor, Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl_mul_unipotent, ← bMat_mul_mMat (selRel F a b),
    ← Matrix.mul_assoc, Matrix.GeneralLinearGroup.coe_inv, coe_bFactor, Matrix.nonsing_inv_mul _ (isUnit_det_bMat (selRel F a b)),
    Matrix.one_mul]

private theorem coe_mFactor_inv (a : 𝔸∞) (b : 𝔸f) : (((mFactor F a b)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸) =
    mInvMat (selE F a b) (selZ F a b) (toAdele' F a b) := by
  rw [Matrix.GeneralLinearGroup.coe_inv, coe_mFactor]
  exact Matrix.inv_eq_right_inv (mMat_mul_mInvMat (selRel F a b))

end Adelic2

end SolE_j1
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

noncomputable section

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical

namespace SolE_j1

open AutomorphicForm AutomorphicForm.WeylIntegrable

section EntryBox

variable {A : Type*} [CommRing A]

private def matBox (C : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {M | ∀ i j, M i j ∈ C}

omit [CommRing A] in
private theorem isCompact_matBox [TopologicalSpace A] {C : Set A} (hC : IsCompact C) : IsCompact (matBox C) := by
  have : matBox C = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => C := by
    ext M; exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC

private def unitBox (C : Set A) : Set (GL (Fin 2) A) := {k | (k : Matrix (Fin 2) (Fin 2) A) ∈ matBox C ∧ ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ matBox C}

private theorem unitBox_eq_preimage (C : Set A) :
    unitBox C = Units.embedProduct (Matrix (Fin 2) (Fin 2) A) ⁻¹' (matBox C ×ˢ (MulOpposite.op '' matBox C)) := by
  ext k
  simp only [unitBox, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, M, hM, hMk⟩
    refine ⟨h1, ?_⟩
    have : M = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hMk
    rwa [← this]

private theorem isCompact_unitBox [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A} (hC : IsCompact C) :
    IsCompact (unitBox C) := by
  rw [unitBox_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_matBox hC).prod ((isCompact_matBox hC).image MulOpposite.continuous_op))

private theorem exists_bound_on_unitBox [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A} (hC : IsCompact C)
    {φ : GL (Fin 2) A → ℂ} (hφ : Continuous φ) (g : GL (Fin 2) A) : ∃ B : ℝ, ∀ k ∈ unitBox C, ‖φ (k * g)‖ ≤ B :=
  (isCompact_unitBox hC).exists_bound_of_continuousOn (hφ.comp (continuous_id.mul continuous_const)).continuousOn

private theorem exists_bound_on_unitBox_family_j1 [TopologicalSpace A] [IsTopologicalRing A] [T1Space A]
    {C : Set A} (hC : IsCompact C) {φ : ℂ → GL (Fin 2) A → ℂ}
    (hφ : Continuous (fun p : ℂ × GL (Fin 2) A => φ p.1 p.2)) {S : Set ℂ} (hS : IsCompact S)
    (g : GL (Fin 2) A) : ∃ B : ℝ, ∀ s ∈ S, ∀ k ∈ unitBox C, ‖φ s (k * g)‖ ≤ B := by
  have hpair : Continuous (fun p : ℂ × GL (Fin 2) A => (p.1, p.2 * g)) := by fun_prop
  obtain ⟨B, hB⟩ := (hS.prod (isCompact_unitBox hC)).exists_bound_of_continuousOn
    (hφ.comp hpair).continuousOn
  exact ⟨B, fun s hs k hk => hB (s, k) (Set.mk_mem_prod hs hk)⟩

end EntryBox
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

section NormBounds

variable {R : Type*} [NormedRing R]

private theorem norm_mul_le_of_le {a b : R} {s t : ℝ} (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ t) (hs : 0 ≤ s) : ‖a * b‖ ≤ s * t :=
  (norm_mul_le a b).trans (mul_le_mul ha hb (norm_nonneg _) hs)

private theorem entry_bounds [NormOneClass R] {e z p : R} (he : ‖e‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hp : ‖p‖ ≤ 1) :
    ‖e‖ ≤ 9 ∧ ‖1 - e‖ ≤ 9 ∧ ‖1 - e + e * z‖ ≤ 9 ∧ ‖p + e‖ ≤ 9 ∧
    ‖(2 * e - 1) * (p + e)‖ ≤ 9 ∧ ‖-((2 * e - 1) * (1 - e))‖ ≤ 9 ∧ ‖-((2 * e - 1) * (1 - e + e * z))‖ ≤ 9 ∧ ‖(2 * e - 1) * e‖ ≤ 9 := by
  have h1 : ‖(1 : R)‖ ≤ 1 := norm_one.le
  have h1e : ‖1 - e‖ ≤ 2 := (norm_sub_le_of_le h1 he).trans (by norm_num)
  have hsel : ‖2 * e - 1‖ ≤ 3 := by rw [two_mul]; exact (norm_sub_le_of_le (norm_add_le_of_le he he) h1).trans (by norm_num)
  have h3 : ‖1 - e + e * z‖ ≤ 3 := (norm_add_le_of_le h1e (norm_mul_le_of_le he hz zero_le_one)).trans (by norm_num)
  have h4 : ‖p + e‖ ≤ 2 := (norm_add_le_of_le hp he).trans (by norm_num)
  refine ⟨he.trans (by norm_num), h1e.trans (by norm_num), h3.trans (by norm_num), h4.trans (by norm_num), ?_, ?_, ?_, ?_⟩
  · exact (norm_mul_le_of_le hsel h4 (by norm_num)).trans (by norm_num)
  · rw [norm_neg]; exact (norm_mul_le_of_le hsel h1e (by norm_num)).trans (by norm_num)
  · rw [norm_neg]; exact (norm_mul_le_of_le hsel h3 (by norm_num)).trans (by norm_num)
  · exact (norm_mul_le_of_le hsel he (by norm_num)).trans (by norm_num)

end NormBounds
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

section AdelicBoxSec

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

private def slab (S : Set 𝔸∞) (T : Set 𝔸f) : Set 𝔸 := {x | x.1 ∈ S ∧ x.2 ∈ T}

private theorem mem_slab {S : Set 𝔸∞} {T : Set 𝔸f} {x : 𝔸} : x ∈ slab F S T ↔ x.1 ∈ S ∧ x.2 ∈ T := Iff.rfl

private def archBall : Set 𝔸∞ := {a | ∀ w, ‖a w‖ ≤ 9}

omit [NumberField F] in
private theorem isCompact_archBall : IsCompact (archBall F) := by
  haveI := fun w => AdelicBox.properSpace_completion F w
  have : archBall F = Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 9 := by
    ext a; exact ⟨fun h w _ => mem_closedBall_zero_iff.mpr (h w), fun h w => mem_closedBall_zero_iff.mp (h w (Set.mem_univ _))⟩
  rw [this]
  exact isCompact_univ_pi fun w => isCompact_closedBall _ _

private def entrySet : Set 𝔸 := slab F (archBall F) (integralFiniteAdeles (𝓞 F) F)

private theorem isCompact_entrySet : IsCompact (entrySet F) := by
  have : entrySet F = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (archBall F ×ˢ integralFiniteAdeles (𝓞 F) F) := by
    ext x; simp only [entrySet, mem_slab]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
  rw [this]
  exact ((isCompact_archBall F).prod (isCompact_integralFiniteAdeles F)).image continuous_id

private theorem mem_entrySet {u : 𝔸} : u ∈ entrySet F ↔ (∀ w, ‖u.1 w‖ ≤ 9) ∧ ∀ v, u.2 v ∈ v.adicCompletionIntegers F := Iff.rfl

private def cInf (w : InfinitePlace F) : 𝔸 →+* w.Completion := (Pi.evalRingHom _ w).comp (RingHom.fst 𝔸∞ 𝔸f)

private def cFin (v : HeightOneSpectrum (𝓞 F)) : 𝔸 →+* v.adicCompletion F where
  toFun u := u.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem cInf_apply (w : InfinitePlace F) (u : 𝔸) : cInf F w u = u.1 w := rfl
private theorem cFin_apply (v : HeightOneSpectrum (𝓞 F)) (u : 𝔸) : cFin F v u = u.2 v := rfl

private theorem norm_selE_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selE F a b).1 w‖ ≤ 1 := by
  rw [selE_fst]; split_ifs <;> simp

private theorem norm_selZ_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selZ F a b).1 w‖ ≤ 1 := by
  rw [selZ_fst]; split_ifs with h
  · exact (norm_inv_lt_one_of_bigInf F h).le
  · simp

private theorem norm_selP_le (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖((1 - selE F a b) * toAdele' F a b).1 w‖ ≤ 1 := by
  rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, toAdele'_fst]
  split_ifs with h
  · simp
  · rw [BigInf, not_lt] at h; simpa using h

private theorem selE_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [selE_snd]; split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem selZ_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [selZ_snd]; split_ifs with h
  · exact inv_mem_of_bigFin F h
  · exact one_mem _

private theorem selP_mem (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) :
    ((1 - selE F a b) * toAdele' F a b).2 v ∈ v.adicCompletionIntegers F := by
  rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, toAdele'_snd]
  split_ifs with h
  · simp
  · rw [BigFin, not_not] at h; simpa using h

private theorem entries_mem (ε z p : 𝔸)
    (hInf : ∀ w, ‖ε.1 w‖ ≤ 1 ∧ ‖z.1 w‖ ≤ 1 ∧ ‖p.1 w‖ ≤ 1)
    (hFin : ∀ v, ε.2 v ∈ v.adicCompletionIntegers F ∧ z.2 v ∈ v.adicCompletionIntegers F ∧ p.2 v ∈ v.adicCompletionIntegers F) :
    ε ∈ entrySet F ∧ 1 - ε ∈ entrySet F ∧ 1 - ε + ε * z ∈ entrySet F ∧ p + ε ∈ entrySet F ∧
    (2 * ε - 1) * (p + ε) ∈ entrySet F ∧ -((2 * ε - 1) * (1 - ε)) ∈ entrySet F ∧
    -((2 * ε - 1) * (1 - ε + ε * z)) ∈ entrySet F ∧ (2 * ε - 1) * ε ∈ entrySet F := by

  have I : ∀ (u : 𝔸), (∀ w, ‖cInf F w u‖ ≤ 9) → (∀ v, cFin F v u ∈ v.adicCompletionIntegers F) → u ∈ entrySet F :=
    fun u h1 h2 => (mem_entrySet F).mpr ⟨h1, h2⟩
  have two : ∀ v, (2 : v.adicCompletion F) * cFin F v ε - 1 ∈ v.adicCompletionIntegers F := fun v => by
    rw [two_mul]; exact sub_mem (add_mem (hFin v).1 (hFin v).1) (one_mem _)
  have B : ∀ w, _ := fun w => entry_bounds (hInf w).1 (hInf w).2.1 (hInf w).2.2
  refine ⟨I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_),
    I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_), I _ (fun w => ?_) (fun v => ?_)⟩
  · simpa only [cInf_apply] using (B w).1
  · simpa only [cFin_apply] using (hFin v).1
  · simpa only [map_sub, map_one, cInf_apply] using (B w).2.1
  · simpa only [map_sub, map_one, cFin_apply] using sub_mem (one_mem _) (hFin v).1
  · simpa only [map_add, map_sub, map_mul, map_one, cInf_apply] using (B w).2.2.1
  · simpa only [map_add, map_sub, map_mul, map_one, cFin_apply] using add_mem (sub_mem (one_mem _) (hFin v).1) (mul_mem (hFin v).1 (hFin v).2.1)
  · simpa only [map_add, cInf_apply] using (B w).2.2.2.1
  · simpa only [map_add, cFin_apply] using add_mem (hFin v).2.2 (hFin v).1
  · simpa only [map_add, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.1
  · simpa only [map_add, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using mul_mem (two v) (add_mem (hFin v).2.2 (hFin v).1)
  · simpa only [map_neg, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.1
  · simpa only [map_neg, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using neg_mem (mul_mem (two v) (sub_mem (one_mem _) (hFin v).1))
  · simpa only [map_neg, map_add, map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.2.1
  · simpa only [map_neg, map_add, map_sub, map_mul, map_one, map_ofNat, cFin_apply] using
      neg_mem (mul_mem (two v) (add_mem (sub_mem (one_mem _) (hFin v).1) (mul_mem (hFin v).1 (hFin v).2.1)))
  · simpa only [map_sub, map_mul, map_one, map_ofNat, cInf_apply] using (B w).2.2.2.2.2.2.2
  · simpa only [map_sub, map_mul, map_one, map_ofNat, cFin_apply] using mul_mem (two v) (hFin v).1

private theorem mFactor_mem_unitBox (a : 𝔸∞) (b : 𝔸f) : mFactor F a b ∈ unitBox (entrySet F) := by
  obtain ⟨m1, m2, m3, m4, i1, i2, i3, i4⟩ := entries_mem F (selE F a b) (selZ F a b) ((1 - selE F a b) * toAdele' F a b)
    (fun w => ⟨norm_selE_le F a b w, norm_selZ_le F a b w, norm_selP_le F a b w⟩)
    (fun v => ⟨selE_mem F a b v, selZ_mem F a b v, selP_mem F a b v⟩)
  constructor
  · intro i j
    rw [coe_mFactor]
    fin_cases i <;> fin_cases j
    · exact m1
    · exact m2
    · exact m3
    · exact m4
  · intro i j
    rw [coe_mFactor_inv]
    fin_cases i <;> fin_cases j
    · exact i1
    · exact i2
    · exact i3
    · exact i4

private theorem exists_bound_mFactor {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, ∀ (a : 𝔸∞) (b : 𝔸f), ‖φ (mFactor F a b * g)‖ ≤ B := by
  letI : TopologicalSpace 𝔸 := inferInstance
  obtain ⟨B, hB⟩ := exists_bound_on_unitBox (isCompact_entrySet F) hφ g
  exact ⟨B, fun a b => hB _ (mFactor_mem_unitBox F a b)⟩

end AdelicBoxSec
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end SolE_j1
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace SolE_j1

open AutomorphicForm AutomorphicForm.WeylIntegrable

section PositiveChar

variable {G : Type*} [Group G]

private theorem val_eq_one_of_mul_self_eq_one (α : G →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {e : G} (he : e * e = 1) :
    ((α e : ℝˣ) : ℝ) = 1 := by
  have h : ((α e : ℝˣ) : ℝ) * ((α e : ℝˣ) : ℝ) = 1 := by rw [← Units.val_mul, ← map_mul, he, map_one, Units.val_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · exact absurd (hα e) (by rw [h1]; norm_num)

end PositiveChar
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

section Pointwise

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

private theorem apply_weyl_unipotent_eq (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (u : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g) =
      ((etaFst μ α hα s (eUnit (selRel F u.1 u.2) * (yUnit (selRel F u.1 u.2))⁻¹) : ℂˣ) : ℂ) *
        ((etaSnd ν α hα s (yUnit (selRel F u.1 u.2)) : ℂˣ) : ℂ) * φ (mFactor F u.1 u.2 * g) := by
  rw [weyl_unipotent_eq F u, mul_assoc, hφ _ (bFactor_mem_borel (selRel F u.1 u.2)) (mFactor F u.1 u.2 * g),
    borelDiagFst_bFactor, borelDiagSnd_bFactor]

private theorem norm_apply_weyl_unipotent_eq (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (u : 𝔸) (g : AdelicGL2 (𝓞 F) F) :
    ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ =
      ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) * ‖φ (mFactor F u.1 u.2 * g)‖ := by
  set h := selRel F u.1 u.2
  set t : ℝ := ((α (yUnit h) : ℝˣ) : ℝ) with ht
  have htpos : 0 < t := hα _
  have he : ((α (eUnit h) : ℝˣ) : ℝ) = 1 := val_eq_one_of_mul_self_eq_one α hα (eUnit_mul_self h)
  have h1 : ‖((etaFst μ α hα s (eUnit h * (yUnit h)⁻¹) : ℂˣ) : ℂ)‖ = t⁻¹ ^ (s.re + 1 / 2) := by
    rw [etaFst_apply, Units.val_mul, norm_mul, hμ, one_mul, norm_cpowChar_apply, map_mul, map_inv, Units.val_mul, he, one_mul,
      Units.val_inv_eq_inv_val, ← ht]
    norm_num
  have h2 : ‖(((etaSnd ν α hα s (yUnit h)) : ℂˣ) : ℂ)‖ = t ^ (-(s.re + 1 / 2)) := by
    rw [etaSnd_apply, Units.val_mul, norm_mul, hν, one_mul, norm_cpowChar_apply, ← ht]
    norm_num
  rw [apply_weyl_unipotent_eq F α hα μ ν s φ hφ u g, norm_mul, norm_mul, h1, h2, Real.inv_rpow htpos.le, ← Real.rpow_neg htpos.le,
    ← Real.rpow_add htpos]
  congr 2
  ring

private theorem norm_apply_weyl_unipotent_le (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : 𝔸, ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
      B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by
  obtain ⟨B, hB⟩ := exists_bound_mFactor F hφc g
  refine ⟨max B 0, le_max_right _ _, fun u => ?_⟩
  rw [norm_apply_weyl_unipotent_eq F α hα μ ν s φ hμ hν hφ u g, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB u.1 u.2).trans (le_max_left _ _)) (Real.rpow_nonneg (hα _).le _)

end Pointwise
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end SolE_j1
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

noncomputable section

open NumberField IsDedekindDomain

namespace SolE_j1

open AutomorphicForm AutomorphicForm.WeylIntegrable NumberField.AdelicHeight

private theorem rpow_neg_le_add_j1 {t : ℝ} (ht : 0 < t) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    t ^ (-b) ≤ t ^ (-a) + t ^ (-c) := by
  rcases le_or_gt 1 t with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg hab)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge ht h1.le (neg_le_neg hbc)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

section Family

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

private theorem exists_family_bound_j1 (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    {S : Set ℂ} (hS : IsCompact S) (g : AdelicGL2 (𝓞 F) F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ S, ∀ u : 𝔸,
      ‖φ s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
        B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by
  letI : TopologicalSpace 𝔸 := inferInstance
  obtain ⟨B, hB⟩ := exists_bound_on_unitBox_family_j1 (isCompact_entrySet F) hjc hS g
  refine ⟨max B 0, le_max_right _ _, fun s hs u => ?_⟩
  rw [norm_apply_weyl_unipotent_eq F α hα μ ν s (φ s) hμ hν (hφ s) u g, mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((hB s hs _ (mFactor_mem_unitBox F u.1 u.2)).trans (le_max_left _ _))
    (Real.rpow_nonneg (hα _).le _)

private theorem summable_alpha_rpow_j1 (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hone : IsUnitaryChar (𝓞 F) F (1 : (𝔸)ˣ →* ℂˣ))
    (hflat : ∀ s : ℂ, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
      (fun k : AdelicGL2 (𝓞 F) F => ((adelicHeight F k : ℝ) : ℂ) ^ (s + 1 / 2)))
    (hsumm : ∀ (s : ℂ), 1 / 2 < s.re → ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) ψ → Continuous ψ →
      ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun ξ : F =>
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖))
    (σ : ℝ) (hσ : 1 / 2 < σ) (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun ξ : F =>
      ((α (yUnit (selRel F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2)) : ℝˣ) : ℝ) ^ (-(2 * σ + 1))) := by
  letI : TopologicalSpace 𝔸 := inferInstance
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun k => ((adelicHeight F k : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) with hψ
  have hψc : Continuous ψ :=
    (Complex.continuous_ofReal.comp (continuous_adelicHeight F)).cpow continuous_const
      (fun k => Complex.ofReal_mem_slitPlane.2 (adelicHeight_pos k))
  have hsum := hsumm (σ : ℂ) (by simpa using hσ) ψ (hflat (σ : ℂ)) hψc g
  have hKc : IsCompact (unitBox (entrySet F)) := isCompact_unitBox (isCompact_entrySet F)
  have hne : (unitBox (entrySet F)).Nonempty := ⟨_, mFactor_mem_unitBox F 0 0⟩
  have hcont : ContinuousOn (fun k : AdelicGL2 (𝓞 F) F => ‖ψ (k * g)‖) (unitBox (entrySet F)) :=
    (hψc.comp (continuous_id.mul continuous_const)).norm.continuousOn
  obtain ⟨k₀, -, hmin⟩ := hKc.exists_isMinOn hne hcont
  have hm₀ : 0 < ‖ψ (k₀ * g)‖ := by
    simp only [hψ]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos _)]
    exact Real.rpow_pos_of_pos (adelicHeight_pos _) _
  refine Summable.of_nonneg_of_le (fun ξ => Real.rpow_nonneg (hα _).le _) (fun ξ => ?_)
    (hsum.mul_left (‖ψ (k₀ * g)‖)⁻¹)
  show ((α (yUnit (selRel F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2)) : ℝˣ) : ℝ) ^ (-(2 * σ + 1)) ≤
    (‖ψ (k₀ * g)‖)⁻¹ * ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖
  have hid := norm_apply_weyl_unipotent_eq F α hα 1 1 (σ : ℂ) ψ hone hone (hflat (σ : ℂ))
    (algebraMap F 𝔸 ξ) g
  rw [adelicWeyl_inv' F, Complex.ofReal_re] at hid
  have hm : ‖ψ (k₀ * g)‖ ≤ ‖ψ (mFactor F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2 * g)‖ :=
    hmin (mFactor_mem_unitBox F _ _)
  rw [hid, ← div_eq_inv_mul, le_div_iff₀ hm₀]
  exact mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (hα _).le _)

end Family
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end SolE_j1
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

end
p2m_reactivate "P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.SolE_j1"

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    DifferentiableOn ℂ
      (fun s : ℂ => φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      {z : ℂ | 1 / 2 < z.re} := by
  intro α hα μ ν hμ hν φ hφ hjc hhol g
  have hpack := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  obtain ⟨-, hone, hflat⟩ := hpack
  have hsumm : ∀ (s : ℂ), 1 / 2 < s.re → ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) ψ → Continuous ψ →
      ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun ξ : F =>
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) :=
    fun s hs ψ hψ hψc g =>
      AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα 1 1 hone hone s hs ψ hψ hψc g
  intro s₀ hs₀
  have hre : (1 : ℝ) / 2 < s₀.re := hs₀
  obtain ⟨r, hr0, hσ₀⟩ : ∃ r : ℝ, 0 < r ∧ 1 / 2 < s₀.re - r :=
    ⟨(s₀.re - 1 / 2) / 2, by linarith, by linarith⟩
  obtain ⟨B, hB0, hB⟩ := SolE_j1.exists_family_bound_j1 F α hα μ ν hμ hν φ hφ hjc
    (isCompact_closedBall s₀ r) g
  have hsum₀ := SolE_j1.summable_alpha_rpow_j1 F α hα hone (hflat hα) hsumm (s₀.re - r) hσ₀ g
  have hsum₁ := SolE_j1.summable_alpha_rpow_j1 F α hα hone (hflat hα) hsumm (s₀.re + r)
    (by linarith) g
  have hM := (hsum₀.add hsum₁).mul_left B
  have hD : DifferentiableOn ℂ (fun s : ℂ => ∑' ξ : F,
      φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      (Metric.ball s₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun (ξ : F) (s : ℂ) =>
        φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      hM (fun ξ => (hhol _).differentiableOn) Metric.isOpen_ball (fun ξ s hs => ?_)
    have hwin : |s.re - s₀.re| < r := by
      have h1 : ‖s - s₀‖ < r := by simpa [Complex.dist_eq] using hs
      exact lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀)) h1
    obtain ⟨hw₁, hw₂⟩ := abs_lt.1 hwin
    have hs' : s ∈ Metric.closedBall s₀ r := Metric.ball_subset_closedBall hs
    show ‖φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ ≤
      B * (((α (AutomorphicForm.WeylIntegrable.yUnit (AutomorphicForm.WeylIntegrable.selRel F
                (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 (algebraMap F (AdeleRing (𝓞 F) F) ξ).2)) :
                ℝˣ) : ℝ) ^ (-(2 * (s₀.re - r) + 1)) +
            ((α (AutomorphicForm.WeylIntegrable.yUnit (AutomorphicForm.WeylIntegrable.selRel F
                (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 (algebraMap F (AdeleRing (𝓞 F) F) ξ).2)) :
                ℝˣ) : ℝ) ^ (-(2 * (s₀.re + r) + 1)))
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (SolE_j1.rpow_neg_le_add_j1 (hα _) (a := 2 * (s₀.re - r) + 1) (b := 2 * s.re + 1)
        (c := 2 * (s₀.re + r) + 1) (by linarith) (by linarith)) hB0)
    rw [← SolE_j1.adelicWeyl_inv' F]
    exact hB s hs' _
  have hall : DifferentiableOn ℂ (fun s : ℂ => φ s g + ∑' ξ : F,
      φ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      (Metric.ball s₀ r) :=
    (hhol g).differentiableOn.add hD
  exact (hall.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))).differentiableWithinAt

end S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family
end P2MW
export P2MW.S_AutomorphicForm_bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family (solution)
