-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8908e9f3-cbe8-58fe-a348-adfa487f520e

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Topology
open scoped NNReal

noncomputable section

namespace IwasWeyl

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

section Finite

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Ov" => (v.adicCompletionIntegers F : Set (v.adicCompletion F))

theorem isClopen_integers : IsClopen Ov :=
  ⟨Valued.isClosed_valuationSubring _, Valued.isOpen_valuationSubring _⟩

def kf (y : Fv) : Matrix (Fin 2) (Fin 2) Fv :=
  if y ∈ Ov then !![0, 1; 1, y] else !![1, 0; y⁻¹, 1]

def kfInv (y : Fv) : Matrix (Fin 2) (Fin 2) Fv :=
  if y ∈ Ov then !![-y, 1; 1, 0] else !![1, 0; -y⁻¹, 1]

theorem kf_mul_kfInv (y : Fv) : kf F v y * kfInv F v y = 1 := by
  unfold kf kfInv
  split_ifs with h
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hy : y ≠ 0 := fun h0 => h (h0 ▸ zero_mem _)
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy] <;> skip

theorem kfInv_mul_kf (y : Fv) : kfInv F v y * kf F v y = 1 := by
  unfold kf kfInv
  split_ifs with h
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hy : y ≠ 0 := fun h0 => h (h0 ▸ zero_mem _)
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy] <;> skip

theorem kf_mem (y : Fv) (i j : Fin 2) : kf F v y i j ∈ v.adicCompletionIntegers F := by
  unfold kf
  split_ifs with h
  · fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact one_mem _
    · exact one_mem _
    · exact h
  · have hy : y ≠ 0 := fun h0 => h (h0 ▸ zero_mem _)
    have hyinv : y⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h
      exact (inv_lt_one_of_one_lt₀ h).le
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact hyinv
    · exact one_mem _

theorem kfInv_mem (y : Fv) (i j : Fin 2) : kfInv F v y i j ∈ v.adicCompletionIntegers F := by
  unfold kfInv
  split_ifs with h
  · fin_cases i <;> fin_cases j
    · exact neg_mem h
    · exact one_mem _
    · exact one_mem _
    · exact zero_mem _
  · have hy : y ≠ 0 := fun h0 => h (h0 ▸ zero_mem _)
    have hyinv : y⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h
      exact (inv_lt_one_of_one_lt₀ h).le
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact zero_mem _
    · exact neg_mem hyinv
    · exact one_mem _

theorem continuous_kf_apply (i j : Fin 2) : Continuous fun y : Fv => kf F v y i j := by
  have hpc : ∀ (f g : Fv → Fv), Continuous f → ContinuousOn g Ovᶜ →
      Continuous fun y : Fv => if y ∈ Ov then f y else g y := by
    intro f g hf hg
    refine continuous_if (fun a ha => ?_) hf.continuousOn ?_
    · change a ∈ frontier Ov at ha
      rw [(isClopen_integers F v).frontier_eq] at ha; exact ha.elim
    · change ContinuousOn g (closure Ovᶜ)
      rwa [(isClopen_integers F v).compl.isClosed.closure_eq]
  have hinv : ContinuousOn (fun y : Fv => y⁻¹) Ovᶜ :=
    continuousOn_inv₀.mono fun y hy h0 => hy (h0 ▸ zero_mem _)
  fin_cases i <;> fin_cases j
  · refine (hpc (fun _ => 0) (fun _ => 1) continuous_const continuousOn_const).congr fun y => ?_
    unfold kf; split_ifs <;> simp
  · refine (hpc (fun _ => 1) (fun _ => 0) continuous_const continuousOn_const).congr fun y => ?_
    unfold kf; split_ifs <;> simp
  · refine (hpc (fun _ => 1) (fun y => y⁻¹) continuous_const hinv).congr fun y => ?_
    unfold kf; split_ifs <;> simp
  · refine (hpc (fun y => y) (fun _ => 1) continuous_id continuousOn_const).congr fun y => ?_
    unfold kf; split_ifs <;> simp

theorem continuous_kfInv_apply (i j : Fin 2) : Continuous fun y : Fv => kfInv F v y i j := by
  have hpc : ∀ (f g : Fv → Fv), Continuous f → ContinuousOn g Ovᶜ →
      Continuous fun y : Fv => if y ∈ Ov then f y else g y := by
    intro f g hf hg
    refine continuous_if (fun a ha => ?_) hf.continuousOn ?_
    · change a ∈ frontier Ov at ha
      rw [(isClopen_integers F v).frontier_eq] at ha; exact ha.elim
    · change ContinuousOn g (closure Ovᶜ)
      rwa [(isClopen_integers F v).compl.isClosed.closure_eq]
  have hinv0 : ContinuousOn (fun y : Fv => y⁻¹) Ovᶜ :=
    continuousOn_inv₀.mono fun y hy h0 => hy (h0 ▸ zero_mem _)
  have hinv : ContinuousOn (fun y : Fv => -y⁻¹) Ovᶜ := hinv0.neg
  fin_cases i <;> fin_cases j
  · refine (hpc (fun y => -y) (fun _ => 1) continuous_neg continuousOn_const).congr fun y => ?_
    unfold kfInv; split_ifs <;> simp
  · refine (hpc (fun _ => 1) (fun _ => 0) continuous_const continuousOn_const).congr fun y => ?_
    unfold kfInv; split_ifs <;> simp
  · refine (hpc (fun _ => 1) (fun y => -y⁻¹) continuous_const hinv).congr fun y => ?_
    unfold kfInv; split_ifs <;> simp
  · refine (hpc (fun _ => 0) (fun _ => 1) continuous_const continuousOn_const).congr fun y => ?_
    unfold kfInv; split_ifs <;> simp

theorem weylUnip_mul_kfInv_10 (y : Fv) : (!![(0 : Fv), 1; 1, y] * kfInv F v y) 1 0 = 0 := by
  unfold kfInv
  split_ifs with h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hy : y ≠ 0 := fun h0 => h (h0 ▸ zero_mem _)
    simp [Matrix.mul_apply, Fin.sum_univ_two, hy]

end Finite

section Arch

variable (w : InfinitePlace F)

local notation "L" => w.Completion

abbrev emb : L →+* ℂ := InfinitePlace.Completion.extensionEmbedding w

theorem emb_injective : Function.Injective (emb F w) := (emb F w).injective

theorem norm_emb (x : L) : ‖emb F w x‖ = ‖x‖ := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  exact h

theorem conj_mem_range (x : L) : starRingEnd ℂ (emb F w x) ∈ Set.range (emb F w) := by
  rcases w.isReal_or_isComplex with hw | hw
  · refine ⟨x, ?_⟩
    have : (emb F w x : ℂ) = ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x).symm
    rw [this, Complex.conj_ofReal]
  · exact (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw) _

theorem ofReal_mem_range (r : ℝ) : (r : ℂ) ∈ Set.range (emb F w) := by
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨x, hx⟩ := (InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw).2 r
    refine ⟨x, ?_⟩
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x, hx]
  · exact (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw) _

def cj (x : L) : L := Classical.choose (conj_mem_range F w x)

theorem emb_cj (x : L) : emb F w (cj F w x) = starRingEnd ℂ (emb F w x) := Classical.choose_spec (conj_mem_range F w x)

def ofR (r : ℝ) : L := Classical.choose (ofReal_mem_range F w r)

theorem emb_ofR (r : ℝ) : emb F w (ofR F w r) = (r : ℂ) := Classical.choose_spec (ofReal_mem_range F w r)

theorem continuous_cj : Continuous (cj F w) := by
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.continuous_iff]
  have : (emb F w) ∘ cj F w = starRingEnd ℂ ∘ emb F w := funext fun x => emb_cj F w x
  rw [show ((InfinitePlace.Completion.extensionEmbedding w : L → ℂ) ∘ cj F w) = starRingEnd ℂ ∘ emb F w from this]
  exact Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous

theorem continuous_ofR : Continuous (ofR F w) := by
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.continuous_iff (f := ofR F w)]
  have : (emb F w) ∘ ofR F w = fun r : ℝ => (r : ℂ) := funext fun r => emb_ofR F w r
  rw [show ((InfinitePlace.Completion.extensionEmbedding w : L → ℂ) ∘ ofR F w) = fun r : ℝ => (r : ℂ) from this]
  exact Complex.continuous_ofReal

def cc (z : L) : L := ofR F w (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹

theorem continuous_cc : Continuous (cc F w) := by
  unfold cc
  refine (continuous_ofR F w).comp ?_
  refine (Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))).inv₀ fun z => ?_
  exact (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2)).ne'

theorem emb_cc (z : L) : emb F w (cc F w z) = ((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ : ℝ) := by
  unfold cc; rw [emb_ofR]

def ka (z : L) : Matrix (Fin 2) (Fin 2) L := cc F w z • !![-(cj F w z), 1; 1, z]

def kaInv (z : L) : Matrix (Fin 2) (Fin 2) L := cc F w z • !![-z, 1; 1, cj F w z]

theorem cc_sq_mul (z : L) : cc F w z * cc F w z * (1 + z * cj F w z) = 1 := by
  apply emb_injective F w
  simp only [map_mul, map_add, map_one, emb_cj, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_emb]
  have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hr : ((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ * (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ * (1 + ‖z‖ ^ 2) : ℝ) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  exact_mod_cast hr

theorem cj_mul_comm (z : L) : cj F w z * z = z * cj F w z := mul_comm _ _

theorem ka_mul_kaInv (z : L) : ka F w z * kaInv F w z = 1 := by
  have h := cc_sq_mul F w z
  unfold ka kaInv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> linear_combination h

theorem kaInv_mul_ka (z : L) : kaInv F w z * ka F w z = 1 := by
  have h := cc_sq_mul F w z
  unfold ka kaInv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> linear_combination h

theorem continuous_ka_apply (i j : Fin 2) : Continuous fun z : L => ka F w z i j := by
  unfold ka
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  · exact ((continuous_cc F w).mul (continuous_cj F w)).neg
  · exact continuous_cc F w
  · exact continuous_cc F w
  · exact (continuous_cc F w).mul continuous_id

theorem continuous_kaInv_apply (i j : Fin 2) : Continuous fun z : L => kaInv F w z i j := by
  unfold kaInv
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  · exact ((continuous_cc F w).mul continuous_id).neg
  · exact continuous_cc F w
  · exact continuous_cc F w
  · exact (continuous_cc F w).mul (continuous_cj F w)

theorem weylUnip_mul_kaInv_10 (z : L) : (!![(0 : L), 1; 1, z] * kaInv F w z) 1 0 = 0 := by
  unfold kaInv
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  ring

theorem norm_det_ka (z : L) : ‖(ka F w z).det‖ = 1 := by
  have h := cc_sq_mul F w z
  have hdet : (ka F w z).det = -1 := by
    unfold ka
    rw [Matrix.det_smul, Matrix.det_fin_two]
    simp
    linear_combination (-1 : L) * h
  rw [hdet, norm_neg, norm_one]

theorem rowIso_ka (z a b : L) :
    ‖a * ka F w z 0 0 + b * ka F w z 1 0‖ ^ 2 + ‖a * ka F w z 0 1 + b * ka F w z 1 1‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by

  have key : ∀ u : L, ‖u‖ ^ 2 = ((emb F w u) * starRingEnd ℂ (emb F w u)).re := fun u => by
    rw [Complex.mul_conj, ← norm_emb F w u, Complex.normSq_eq_norm_sq]; norm_cast
  rw [key, key, key a, key b]
  unfold ka
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    map_add, map_mul, map_neg, map_one, emb_cj, Complex.conj_conj, emb_cc]
  set α := emb F w a
  set β := emb F w b
  set ζ := emb F w z
  set c : ℝ := (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ with hc
  have hc2 : (c : ℂ) * c * (1 + ζ * starRingEnd ℂ ζ) = 1 := by
    have := congrArg (emb F w) (cc_sq_mul F w z)
    simp only [map_mul, map_add, map_one, emb_cj, emb_cc] at this
    exact this
  rw [← Complex.add_re, ← Complex.add_re]
  congr 1
  simp only [map_add, map_mul, map_neg, map_one, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination (α * (starRingEnd ℂ) α + β * (starRingEnd ℂ) β) * hc2

end Arch

section Assembly

def finEntry (i j : Fin 2) : FiniteAdeleRing (𝓞 F) F → FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mapAlong (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) id Filter.tendsto_id
    (fun v y => kf F v y i j)
    (Filter.Eventually.of_forall fun v => by intro y _; exact kf_mem F v y i j)

def finEntryInv (i j : Fin 2) : FiniteAdeleRing (𝓞 F) F → FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mapAlong (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) id Filter.tendsto_id
    (fun v y => kfInv F v y i j)
    (Filter.Eventually.of_forall fun v => by intro y _; exact kfInv_mem F v y i j)

theorem finEntry_apply (i j : Fin 2) (y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finEntry F i j y v = kf F v (y v) i j := rfl

theorem finEntryInv_apply (i j : Fin 2) (y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finEntryInv F i j y v = kfInv F v (y v) i j := rfl

theorem continuous_finEntry (i j : Fin 2) : Continuous (finEntry F i j) :=
  RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ fun v => continuous_kf_apply F v i j

theorem continuous_finEntryInv (i j : Fin 2) : Continuous (finEntryInv F i j) :=
  RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ fun v => continuous_kfInv_apply F v i j

def kMat (x : AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((fun w : InfinitePlace F => ka F w (x.1 w) i j), finEntry F i j x.2)

def kMatInv (x : AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((fun w : InfinitePlace F => kaInv F w (x.1 w) i j), finEntryInv F i j x.2)

theorem mul_apply_fst (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (w : InfinitePlace F) :
    ((M * N) i j).1 w = ∑ k : Fin 2, (M i k).1 w * (N k j).1 w := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

theorem mul_apply_snd (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((M * N) i j).2 v = ∑ k : Fin 2, (M i k).2 v * (N k j).2 v := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

theorem adele_ext {a b : AdeleRing (𝓞 F) F} (h1 : ∀ w, a.1 w = b.1 w) (h2 : ∀ v, a.2 v = b.2 v) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)

theorem kMat_mul_kMatInv (x : AdeleRing (𝓞 F) F) : kMat F x * kMatInv F x = 1 := by
  ext i j
  refine adele_ext F (fun w => ?_) (fun v => ?_)
  · rw [mul_apply_fst]
    have h := congrFun (congrFun (ka_mul_kaInv F w (x.1 w)) i) j
    rw [Matrix.mul_apply] at h
    simp only [kMat, kMatInv, Matrix.of_apply]
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · rw [mul_apply_snd]
    have h := congrFun (congrFun (kf_mul_kfInv F v (x.2 v)) i) j
    rw [Matrix.mul_apply] at h
    simp only [kMat, kMatInv, Matrix.of_apply, finEntry_apply, finEntryInv_apply]
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl

theorem kMatInv_mul_kMat (x : AdeleRing (𝓞 F) F) : kMatInv F x * kMat F x = 1 := by
  ext i j
  refine adele_ext F (fun w => ?_) (fun v => ?_)
  · rw [mul_apply_fst]
    have h := congrFun (congrFun (kaInv_mul_ka F w (x.1 w)) i) j
    rw [Matrix.mul_apply] at h
    simp only [kMat, kMatInv, Matrix.of_apply]
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · rw [mul_apply_snd]
    have h := congrFun (congrFun (kfInv_mul_kf F v (x.2 v)) i) j
    rw [Matrix.mul_apply] at h
    simp only [kMat, kMatInv, Matrix.of_apply, finEntry_apply, finEntryInv_apply]
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl

def kappa (x : AdeleRing (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  ⟨kMat F x, kMatInv F x, kMat_mul_kMatInv F x, kMatInv_mul_kMat F x⟩

theorem coe_kappa (x : AdeleRing (𝓞 F) F) : ((kappa F x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = kMat F x := rfl
theorem coe_kappa_inv (x : AdeleRing (𝓞 F) F) :
    (((kappa F x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = kMatInv F x := rfl

theorem continuous_kMat : Continuous (kMat F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kMat, Matrix.of_apply]
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun w => (continuous_ka_apply F w i j).comp ((continuous_apply w).comp continuous_fst)
  · exact (continuous_finEntry F i j).comp continuous_snd

theorem continuous_kMatInv : Continuous (kMatInv F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kMatInv, Matrix.of_apply]
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun w => (continuous_kaInv_apply F w i j).comp ((continuous_apply w).comp continuous_fst)
  · exact (continuous_finEntryInv F i j).comp continuous_snd

theorem continuous_kappa : Continuous (kappa F) :=
  Units.continuous_iff.mpr ⟨continuous_kMat F, continuous_kMatInv F⟩

end Assembly

section Props

theorem glFin_kappa_apply (x : AdeleRing (𝓞 F) F) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((glFin (𝓞 F) F (kappa F x) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
      = kf F v (x.2 v) i j := by
  rw [glFin_apply]; rfl

theorem glFin_kappa_inv_apply (x : AdeleRing (𝓞 F) F) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) :
    (((glFin (𝓞 F) F (kappa F x))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
      = kfInv F v (x.2 v) i j := by
  rw [← map_inv, glFin_apply]; rfl

theorem glFin_kappa_mem (x : AdeleRing (𝓞 F) F) : glFin (𝓞 F) F (kappa F x) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  exact ⟨fun i j v => by rw [glFin_kappa_apply]; exact kf_mem F v _ i j,
    fun i j v => by rw [glFin_kappa_inv_apply]; exact kfInv_mem F v _ i j⟩

theorem archComponent_kappa_coe (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    ((archComponent F w (glArch (𝓞 F) F (kappa F x)) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
      = ka F w (x.1 w) := by
  ext i j
  rw [archComponent_apply, glArch_apply]; rfl

theorem isRowIsometry_kappa (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    IsRowIsometry (archComponent F w (glArch (𝓞 F) F (kappa F x))) := by
  refine ⟨?_, fun a b => ?_⟩
  · rw [archComponent_kappa_coe]; exact norm_det_ka F w _
  · simp only [archComponent_kappa_coe]; exact rowIso_ka F w _ a b

theorem coe_weylInv_mul_unipotent (x : AdeleRing (𝓞 F) F) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, x] := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  have hw : ((globalPoints (𝓞 F) F gl2Weyl : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
    ext i j
    change algebraMap F (AdeleRing (𝓞 F) F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  rw [hw]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weylInv_mul_unipotent_mul_kappa_inv_mem (x : AdeleRing (𝓞 F) F) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (kappa F x)⁻¹ ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff, Matrix.GeneralLinearGroup.coe_mul, coe_weylInv_mul_unipotent, coe_kappa_inv]
  refine adele_ext F (fun w => ?_) (fun v => ?_)
  · rw [mul_apply_fst]
    have h := weylUnip_mul_kaInv_10 F w (x.1 w)
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    simp only [kMatInv, Matrix.of_apply, Fin.sum_univ_two]
    change (1 : w.Completion) * kaInv F w (x.1 w) 0 0 + x.1 w * kaInv F w (x.1 w) 1 0 = 0
    simpa using h
  · rw [mul_apply_snd]
    have h := weylUnip_mul_kfInv_10 F v (x.2 v)
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    simp only [kMatInv, Matrix.of_apply, Fin.sum_univ_two, finEntryInv_apply]
    change (1 : v.adicCompletion F) * kfInv F v (x.2 v) 0 0 + x.2 v * kfInv F v (x.2 v) 1 0 = 0
    simpa using h

theorem finComponent_kappa_eq {x y : AdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)} (h : x.2 v = y.2 v) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (kappa F x)) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (kappa F y)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [finComponent_apply, finComponent_apply, glFin_kappa_apply, glFin_kappa_apply, h]

theorem glArch_kappa_eq {x y : AdeleRing (𝓞 F) F} (h : x.1 = y.1) :
    glArch (𝓞 F) F (kappa F x) = glArch (𝓞 F) F (kappa F y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, glArch_apply]
  change (kMat F x i j).1 = (kMat F y i j).1
  simp only [kMat, Matrix.of_apply, h]

end Props

section Height

theorem archComponent_weylUnip_coe (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    ((archComponent F w (glArch (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = !![0, 1; 1, x.1 w] := by
  ext i j
  rw [archComponent_apply, glArch_apply, coe_weylInv_mul_unipotent]
  fin_cases i <;> fin_cases j <;> rfl

theorem finComponent_weylUnip_coe (x : AdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![0, 1; 1, x.2 v] := by
  ext i j
  rw [finComponent_apply, glFin_apply, coe_weylInv_mul_unipotent]
  fin_cases i <;> fin_cases j <;> rfl

theorem localHeight_weylUnip (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    localHeight (archComponent F w (glArch (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x))) = (1 + ‖x.1 w‖ ^ 2)⁻¹ := by
  rw [localHeight, rowNormSq, archComponent_weylUnip_coe, Matrix.det_fin_two]
  simp

theorem finLocalHeight_weylUnip (x : AdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x))) =
      (max 1 ‖x.2 v‖ ^ 2)⁻¹ := by
  rw [finLocalHeight, rowMaxNorm, finComponent_weylUnip_coe, Matrix.det_fin_two]
  simp

def bor (x : AdeleRing (𝓞 F) F) : adelicBorel (𝓞 F) F :=
  ⟨(adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (kappa F x)⁻¹, weylInv_mul_unipotent_mul_kappa_inv_mem F x⟩

theorem bor_mul_kappa (x : AdeleRing (𝓞 F) F) :
    ((bor F x : adelicBorel (𝓞 F) F) : AdelicGL2 (𝓞 F) F) * kappa F x = (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x := by
  change (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (kappa F x)⁻¹ * kappa F x = _
  rw [inv_mul_cancel_right]

theorem coe_bor (x : AdeleRing (𝓞 F) F) :
    (((bor F x : adelicBorel (𝓞 F) F) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      !![0, 1; 1, x] * kMatInv F x := by
  simp only [bor]
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_weylInv_mul_unipotent, coe_kappa_inv]

theorem bor_fst_arch (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    ((borelDiagFst (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = cc F w (x.1 w) ∧
    ((borelDiagSnd (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = cc F w (x.1 w) * (1 + x.1 w * cj F w (x.1 w)) := by
  rw [borelDiagFst_apply_val, borelDiagSnd_apply_val, coe_bor, mul_apply_fst, mul_apply_fst]
  simp only [Fin.sum_univ_two, kMatInv, Matrix.of_apply]
  change (0 : w.Completion) * kaInv F w (x.1 w) 0 0 + 1 * kaInv F w (x.1 w) 1 0 = _ ∧
    (1 : w.Completion) * kaInv F w (x.1 w) 0 1 + x.1 w * kaInv F w (x.1 w) 1 1 = _
  unfold kaInv
  constructor <;> simp [Matrix.smul_apply] <;> ring

theorem bor_fst_fin (x : AdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((borelDiagFst (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = kfInv F v (x.2 v) 1 0 ∧
    ((borelDiagSnd (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = kfInv F v (x.2 v) 0 1 + x.2 v * kfInv F v (x.2 v) 1 1 := by
  rw [borelDiagFst_apply_val, borelDiagSnd_apply_val, coe_bor, mul_apply_snd, mul_apply_snd]
  simp only [Fin.sum_univ_two, kMatInv, Matrix.of_apply, finEntryInv_apply]
  change (0 : v.adicCompletion F) * kfInv F v (x.2 v) 0 0 + 1 * kfInv F v (x.2 v) 1 0 = _ ∧
    (1 : v.adicCompletion F) * kfInv F v (x.2 v) 0 1 + x.2 v * kfInv F v (x.2 v) 1 1 = _
  constructor <;> ring

def tor (x : AdeleRing (𝓞 F) F) : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst (bor F x) * (borelDiagSnd (bor F x))⁻¹

theorem norm_tor_arch (x : AdeleRing (𝓞 F) F) (w : InfinitePlace F) :
    ‖((tor F x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ = (1 + ‖x.1 w‖ ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := bor_fst_arch F x w
  have ht : tor F x * borelDiagSnd (bor F x) = borelDiagFst (bor F x) := by
    unfold tor; rw [inv_mul_cancel_right]
  have hmul : ((tor F x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w *
      ((borelDiagSnd (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w =
      ((borelDiagFst (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w := by
    have := congrArg (fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).1 w) ht
    simp only [Units.val_mul] at this
    exact this
  rw [h1, h2] at hmul

  have hc : ‖cc F w (x.1 w)‖ ≠ 0 := by
    rw [← norm_emb, emb_cc, norm_ne_zero_iff, Complex.ofReal_ne_zero]
    exact (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))).ne'
  have hn : ‖(1 : w.Completion) + x.1 w * cj F w (x.1 w)‖ = 1 + ‖x.1 w‖ ^ 2 := by
    rw [← norm_emb, map_add, map_one, map_mul, emb_cj, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_emb]
    have : (1 : ℂ) + ((‖x.1 w‖ ^ 2 : ℝ) : ℂ) = ((1 + ‖x.1 w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h := congrArg (fun t => ‖t‖) hmul
  simp only [norm_mul, hn] at h
  have hpos : (0 : ℝ) < 1 + ‖x.1 w‖ ^ 2 := by positivity
  field_simp at h
  field_simp
  linarith [h]

theorem norm_le_one_iff_mem (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    ‖y‖ ≤ 1 ↔ y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem norm_tor_fin (x : AdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ‖((tor F x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = (max 1 ‖x.2 v‖ ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := bor_fst_fin F x v
  have ht : tor F x * borelDiagSnd (bor F x) = borelDiagFst (bor F x) := by
    unfold tor; rw [inv_mul_cancel_right]
  have hmul : ((tor F x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v *
      ((borelDiagSnd (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v =
      ((borelDiagFst (bor F x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v := by
    have := congrArg (fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).2 v) ht
    simp only [Units.val_mul] at this
    exact this
  rw [h1, h2] at hmul
  set y := x.2 v with hy
  by_cases hO : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · have hle : ‖y‖ ≤ 1 := (norm_le_one_iff_mem F v y).mpr hO
    rw [max_eq_left hle, one_pow, inv_one]
    have h := congrArg (fun t => ‖t‖) hmul
    simp only [kfInv, if_pos hO] at h
    simpa using h
  · have hlt : 1 < ‖y‖ := lt_of_not_ge fun h => hO ((norm_le_one_iff_mem F v y).mp h)
    have hy0 : y ≠ 0 := fun h0 => hO (h0 ▸ zero_mem _)
    have hn0 : ‖y‖ ≠ 0 := (zero_lt_one.trans hlt).ne'
    rw [max_eq_right hlt.le]
    have h := congrArg (fun t => ‖t‖) hmul
    simp only [kfInv, if_neg hO] at h
    simp at h

    calc ‖((tor F x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖
        = ‖((tor F x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ * ‖y‖ / ‖y‖ := by field_simp
      _ = ‖y‖⁻¹ / ‖y‖ := by rw [h]
      _ = (‖y‖ ^ 2)⁻¹ := by rw [sq, mul_inv, div_eq_mul_inv]

theorem adelicHeight_weylUnip (x : AdeleRing (𝓞 F) F) :
    adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) = (distribHaarChar (AdeleRing (𝓞 F) F) (tor F x) : ℝ) := by
  rw [adelicHeight, archHeight, finHeight, NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by rw [localHeight_weylUnip, norm_tor_arch]
  · exact finprod_congr fun v => by rw [finLocalHeight_weylUnip, norm_tor_fin]

end Height

section Section

theorem cpow_div_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    ((a : ℂ)) ^ z * ((b : ℂ)) ^ (-z) = (((a * b⁻¹ : ℝ)) : ℂ) ^ z := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hb.le), Complex.cpow_neg,
    Complex.ofReal_inv, Complex.inv_cpow]
  rw [Complex.arg_ofReal_of_nonneg hb.le]
  exact Real.pi_ne_zero.symm

theorem section_weylUnip (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) t : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ) (x : AdeleRing (𝓞 F) F) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) =
      ((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ) : ℂ) ^ (s + 1 / 2) * φ (kappa F x) := by
  have h := hφ ((bor F x : adelicBorel (𝓞 F) F) : AdelicGL2 (𝓞 F) F) (bor F x).2 (kappa F x)
  rw [bor_mul_kappa] at h
  rw [h, adelicHeight_weylUnip]
  congr 1

  have e1 : ((etaFst 1 α hα s (borelDiagFst (bor F x)) : ℂˣ) : ℂ) =
      ((((α (borelDiagFst (bor F x)) : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
    rw [etaFst, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  have e2 : ((etaSnd 1 α hα s (borelDiagSnd (bor F x)) : ℂˣ) : ℂ) =
      ((((α (borelDiagSnd (bor F x)) : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
    rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  have e3 : (distribHaarChar (AdeleRing (𝓞 F) F) (tor F x) : ℝ) =
      ((α (borelDiagFst (bor F x)) : ℝˣ) : ℝ) * (((α (borelDiagSnd (bor F x)) : ℝˣ) : ℝ))⁻¹ := by
    rw [← hαv, tor, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]

  have e0 : (⟨((bor F x : adelicBorel (𝓞 F) F) : AdelicGL2 (𝓞 F) F), (bor F x).2⟩ : adelicBorel (𝓞 F) F) = bor F x := rfl
  rw [e0, e1, e2, e3, cpow_div_ofReal (hα _) (hα _)]

end Section

end IwasWeyl

end

open IwasWeyl in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)),
    ∃ κ : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F,
      Continuous κ ∧
      (∀ x, glFin (𝓞 F) F (κ x) ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (κ x)))) ∧
      (∀ x, (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (κ x)⁻¹ ∈ adelicBorel (𝓞 F) F) ∧
      (∀ x y : AdeleRing (𝓞 F) F, ∀ v : HeightOneSpectrum (𝓞 F), x.2 v = y.2 v →
        finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ x)) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ y))) ∧
      (∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → glArch (𝓞 F) F (κ x) = glArch (𝓞 F) F (κ y)) ∧
      (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ),
        IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ →
        ∀ x : AdeleRing (𝓞 F) F,
          φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) =
            ((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ) : ℂ) ^ (s + 1 / 2) * φ (κ x)) := by
  intro α hα
  have hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) t : ℝ) := fun t => rfl
  exact ⟨kappa F, continuous_kappa F, fun x => ⟨glFin_kappa_mem F x, isRowIsometry_kappa F x⟩,
    weylInv_mul_unipotent_mul_kappa_inv_mem F, fun x y v h => finComponent_kappa_eq F h,
    fun x y h => glArch_kappa_eq F h, fun s φ hφ x => section_weylUnip F α hα hαv s φ hφ x⟩

end S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent (solution)
