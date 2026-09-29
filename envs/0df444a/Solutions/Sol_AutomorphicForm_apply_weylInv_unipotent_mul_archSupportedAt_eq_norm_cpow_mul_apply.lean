-- Prove2me | solution 1 for AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/568b3028-b90d-507b-a54d-ed02d51b2104

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

noncomputable section

namespace MOEBW

open scoped Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private theorem adele_ext {a b : AdeleRing (𝓞 F) F} (h1 : ∀ w', a.1 w' = b.1 w') (h2 : ∀ u, a.2 u = b.2 u) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)

private theorem mul_apply_fst (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (w' : InfinitePlace F) :
    ((M * N) i j).1 w' = ∑ k : Fin 2, (M i k).1 w' * (N k j).1 w' := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

private theorem mul_apply_snd (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    ((M * N) i j).2 u = ∑ k : Fin 2, (M i k).2 u * (N k j).2 u := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

private theorem coe_weylInv_mul_unipotent (x : AdeleRing (𝓞 F) F) :
    (((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, x] := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, unipotentGL2_coe]
  have hw : ((globalPoints (𝓞 F) F gl2Weyl : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
    ext i j
    change algebraMap F (AdeleRing (𝓞 F) F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  rw [hw]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section Beta

variable (t₁ c t₂ : w.Completion) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)

private def βloc : Matrix (Fin 2) (Fin 2) w.Completion := !![t₁, c; 0, t₂]
private def βlocInv : Matrix (Fin 2) (Fin 2) w.Completion := !![t₁⁻¹, -c * (t₁⁻¹ * t₂⁻¹); 0, t₂⁻¹]

include h₁ h₂ in
private theorem βloc_mul : βloc F w t₁ c t₂ * βlocInv F w t₁ c t₂ = 1 := by
  unfold βloc βlocInv
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h₁, h₂] <;> field_simp <;> ring

include h₁ h₂ in
private theorem βlocInv_mul : βlocInv F w t₁ c t₂ * βloc F w t₁ c t₂ = 1 := by
  unfold βloc βlocInv
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h₁, h₂] <;> field_simp <;> ring

private def BM : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((fun w' : InfinitePlace F => if h : w' = w then (h ▸ βloc F w t₁ c t₂ i j : w'.Completion)
      else (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j), (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private def BMinv : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((fun w' : InfinitePlace F => if h : w' = w then (h ▸ βlocInv F w t₁ c t₂ i j : w'.Completion)
      else (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j), (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private theorem BM_fst_self (i j : Fin 2) : (BM F w t₁ c t₂ i j).1 w = βloc F w t₁ c t₂ i j := by
  simp [BM]
private theorem BM_fst_of_ne (i j : Fin 2) {w' : InfinitePlace F} (hw : w' ≠ w) :
    (BM F w t₁ c t₂ i j).1 w' = (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j := by
  simp [BM, hw]
private theorem BM_snd (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    (BM F w t₁ c t₂ i j).2 u = (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) i j := by
  change ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) u = _
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
private theorem BMinv_fst_self (i j : Fin 2) : (BMinv F w t₁ c t₂ i j).1 w = βlocInv F w t₁ c t₂ i j := by
  simp [BMinv]
private theorem BMinv_fst_of_ne (i j : Fin 2) {w' : InfinitePlace F} (hw : w' ≠ w) :
    (BMinv F w t₁ c t₂ i j).1 w' = (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j := by
  simp [BMinv, hw]
private theorem BMinv_snd (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    (BMinv F w t₁ c t₂ i j).2 u = (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) i j := by
  change ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) u = _
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl

private theorem one_fst (i j : Fin 2) (w' : InfinitePlace F) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w' = (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
private theorem one_snd (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 u = (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl

include h₁ h₂ in
private theorem BM_mul_BMinv : BM F w t₁ c t₂ * BMinv F w t₁ c t₂ = 1 := by
  ext i j
  refine adele_ext F (fun w' => ?_) (fun u => ?_)
  · rw [mul_apply_fst, one_fst]
    by_cases hw : w' = w
    · subst hw
      simp only [BM_fst_self, BMinv_fst_self]
      have h := congrFun (congrFun (βloc_mul F w' t₁ c t₂ h₁ h₂) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
    · simp only [BM_fst_of_ne F w t₁ c t₂ _ _ hw, BMinv_fst_of_ne F w t₁ c t₂ _ _ hw]
      have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) w'.Completion)) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
  · rw [mul_apply_snd, one_snd]
    simp only [BM_snd, BMinv_snd]
    have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) i) j
    rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h

include h₁ h₂ in
private theorem BMinv_mul_BM : BMinv F w t₁ c t₂ * BM F w t₁ c t₂ = 1 := by
  ext i j
  refine adele_ext F (fun w' => ?_) (fun u => ?_)
  · rw [mul_apply_fst, one_fst]
    by_cases hw : w' = w
    · subst hw
      simp only [BM_fst_self, BMinv_fst_self]
      have h := congrFun (congrFun (βlocInv_mul F w' t₁ c t₂ h₁ h₂) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
    · simp only [BM_fst_of_ne F w t₁ c t₂ _ _ hw, BMinv_fst_of_ne F w t₁ c t₂ _ _ hw]
      have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) w'.Completion)) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
  · rw [mul_apply_snd, one_snd]
    simp only [BM_snd, BMinv_snd]
    have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) i) j
    rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h

private def Bel : AdelicGL2 (𝓞 F) F :=
  ⟨BM F w t₁ c t₂, BMinv F w t₁ c t₂, BM_mul_BMinv F w t₁ c t₂ h₁ h₂, BMinv_mul_BM F w t₁ c t₂ h₁ h₂⟩

private theorem Bel_mem : Bel F w t₁ c t₂ h₁ h₂ ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff]
  change BM F w t₁ c t₂ 1 0 = 0
  refine adele_ext F (fun w' => ?_) (fun u => ?_)
  · by_cases hw : w' = w
    · subst hw; rw [BM_fst_self]; rfl
    · rw [BM_fst_of_ne F w t₁ c t₂ _ _ hw, Matrix.one_apply_ne (by decide)]; rfl
  · rw [BM_snd, Matrix.one_apply_ne (by decide)]; rfl

private theorem distribHaarChar_fst :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨Bel F w t₁ c t₂ h₁ h₂, Bel_mem F w t₁ c t₂ h₁ h₂⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t₁‖ ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagFst_apply_val]
  change (∏ w' : InfinitePlace F, ‖(BM F w t₁ c t₂ 0 0).1 w'‖ ^ w'.mult) * ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(BM F w t₁ c t₂ 0 0).2 u‖ = _
  rw [finprod_eq_one_of_forall_eq_one fun u => by rw [BM_snd, Matrix.one_apply_eq, norm_one], mul_one]
  rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [BM_fst_of_ne F w t₁ c t₂ _ _ hw', Matrix.one_apply_eq, norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ w) h), BM_fst_self]
  rfl

private theorem distribHaarChar_snd :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨Bel F w t₁ c t₂ h₁ h₂, Bel_mem F w t₁ c t₂ h₁ h₂⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t₂‖ ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagSnd_apply_val]
  change (∏ w' : InfinitePlace F, ‖(BM F w t₁ c t₂ 1 1).1 w'‖ ^ w'.mult) * ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(BM F w t₁ c t₂ 1 1).2 u‖ = _
  rw [finprod_eq_one_of_forall_eq_one fun u => by rw [BM_snd, Matrix.one_apply_eq, norm_one], mul_one]
  rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [BM_fst_of_ne F w t₁ c t₂ _ _ hw', Matrix.one_apply_eq, norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ w) h), BM_fst_self]
  rfl

end Beta

section Ext

theorem gl_ext {g h : AdelicGL2 (𝓞 F) F} (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ u, finComponent (𝓞 F) F u (glFin (𝓞 F) F g) = finComponent (𝓞 F) F u (glFin (𝓞 F) F h)) :
    g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) h₁) i) j
    beta_reduce at this
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun u => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion F) => (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) (h₂ u)) i) j
    beta_reduce at this
    rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

theorem glArch_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ w' : InfinitePlace F, archComponent F w' g = archComponent F w' h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => funext fun w' => ?_)
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) w'.Completion => (m : Matrix (Fin 2) (Fin 2) w'.Completion)) (H w')) i) j
  beta_reduce at this
  rwa [archComponent_apply, archComponent_apply] at this

theorem archComponent_weylUnip (x : AdeleRing (𝓞 F) F) (w' : InfinitePlace F) :
    ((archComponent F w' (glArch (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) w'.Completion) :
        Matrix (Fin 2) (Fin 2) w'.Completion) = !![0, 1; 1, x.1 w'] := by
  ext i j
  rw [archComponent_apply, glArch_apply, coe_weylInv_mul_unipotent]
  fin_cases i <;> fin_cases j <;> rfl

theorem finComponent_weylUnip (x : AdeleRing (𝓞 F) F) (u : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F u (glFin (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) (u.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) = !![0, 1; 1, x.2 u] := by
  ext i j
  rw [finComponent_apply, glFin_apply, coe_weylInv_mul_unipotent]
  fin_cases i <;> fin_cases j <;> rfl

end Ext

section BelComponents

variable (t₁ c t₂ : w.Completion) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)

private theorem archComponent_Bel_self :
    ((archComponent F w (glArch (𝓞 F) F (Bel F w t₁ c t₂ h₁ h₂)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = βloc F w t₁ c t₂ := by
  ext i j
  rw [archComponent_apply, glArch_apply]
  exact BM_fst_self F w t₁ c t₂ i j

private theorem archComponent_Bel_of_ne {w' : InfinitePlace F} (hw : w' ≠ w) :
    archComponent F w' (glArch (𝓞 F) F (Bel F w t₁ c t₂ h₁ h₂)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, glArch_apply]
  exact BM_fst_of_ne F w t₁ c t₂ i j hw

private theorem finComponent_Bel (u : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F u (glFin (𝓞 F) F (Bel F w t₁ c t₂ h₁ h₂)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [finComponent_apply, glFin_apply]
  exact BM_snd F w t₁ c t₂ i j u

end BelComponents

section Main

variable (k : AdelicGL2 (𝓞 F) F) (hkf : glFin (𝓞 F) F k = 1)
  (hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)

local notation "KW" => (((archComponent F w (glArch (𝓞 F) F k)) : GL (Fin 2) (InfinitePlace.Completion w)) :
  Matrix (Fin 2) (Fin 2) (InfinitePlace.Completion w))

theorem det_ne : Matrix.det KW ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero

def moeb (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F :=
  (Function.update x.1 w ((KW 0 1 + x.1 w * KW 1 1) / (KW 0 0 + x.1 w * KW 1 0)), x.2)

theorem moeb_fst_self (x : AdeleRing (𝓞 F) F) :
    (moeb F w k x).1 w = (KW 0 1 + x.1 w * KW 1 1) / (KW 0 0 + x.1 w * KW 1 0) := by
  simp [moeb]

theorem moeb_fst_of_ne (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F} (hw : w' ≠ w) :
    (moeb F w k x).1 w' = x.1 w' := by
  simp [moeb, hw]

theorem moeb_snd (x : AdeleRing (𝓞 F) F) : (moeb F w k x).2 = x.2 := rfl

theorem local_identity {K : Type*} [Field K] (x : K) (M : Matrix (Fin 2) (Fin 2) K) (t : K)
    (ht : t = M 0 0 + x * M 1 0) (h : t ≠ 0) :
    !![(0 : K), 1; 1, x] * M = !![M.det / t, M 1 0; 0, t] * !![(0 : K), 1; 1, (M 0 1 + x * M 1 1) / t] := by
  conv_lhs => rw [Matrix.eta_fin_two M]
  simp only [Matrix.mul_fin_two, Matrix.det_fin_two, zero_mul, one_mul, zero_add, mul_one, mul_zero]
  rw [mul_div_cancel₀ _ h, ← ht]
  congr
  field_simp
  rw [ht]; ring

include hkf hka in
theorem bruhat (x : AdeleRing (𝓞 F) F) (hx : KW 0 0 + x.1 w * KW 1 0 ≠ 0) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k =
      Bel F w (Matrix.det KW / (KW 0 0 + x.1 w * KW 1 0)) (KW 1 0) (KW 0 0 + x.1 w * KW 1 0)
          (div_ne_zero (det_ne F w k) hx) hx *
        ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (moeb F w k x)) := by
  set A : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hA
  set A' : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (moeb F w k x) with hA'
  refine gl_ext F (glArch_ext F fun w' => ?_) fun u => ?_
  · simp only [map_mul]
    rcases eq_or_ne w' w with rfl | hw
    · refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hA, hA', archComponent_weylUnip, archComponent_weylUnip, archComponent_Bel_self,
        moeb_fst_self]
      exact local_identity (x.1 _) _ _ rfl hx
    · rw [hka w' hw, archComponent_Bel_of_ne F w _ _ _ _ _ hw, mul_one, one_mul]
      refine Units.ext ?_
      rw [hA, hA', archComponent_weylUnip, archComponent_weylUnip, moeb_fst_of_ne F w k x hw]
  · simp only [map_mul]
    rw [hkf, finComponent_Bel, map_one, mul_one, one_mul]
    refine Units.ext ?_
    rw [hA, hA', finComponent_weylUnip, finComponent_weylUnip, moeb_snd]

theorem cpow_scalar {D A : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (s : ℂ) :
    (((D / A : ℝ)) : ℂ) ^ (s + 1 / 2) * ((A : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = ((D : ℝ) : ℂ) ^ (s + 1 / 2) * ((A : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have harg : ((A : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hA.le]; exact Real.pi_ne_zero.symm
  have h2 : ((A : ℝ) : ℂ) ^ (-(2 * s + 1)) = ((A : ℝ) : ℂ) ^ (-(s + 1 / 2)) * ((A : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
    rw [← Complex.cpow_add _ _ hA0]; congr 1; ring
  rw [h2, div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hD (inv_nonneg.mpr hA.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  ring

theorem etaFst_one_val (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst 1 α hα s t : ℂˣ) : ℂ) = ((((α t) : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) := by
  rw [etaFst, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]

theorem etaSnd_one_val (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaSnd 1 α hα s t : ℂˣ) : ℂ) = ((((α t) : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
  rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]

include hkf hka in
theorem main (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) t : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (x : AdeleRing (𝓞 F) F) (hx : KW 0 0 + x.1 w * KW 1 0 ≠ 0) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
      = (((‖Matrix.det KW‖ ^ w.mult : ℝ)) : ℂ) ^ (s + 1 / 2)
        * (((‖KW 0 0 + x.1 w * KW 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (moeb F w k x)) := by
  rw [bruhat F w k hkf hka x hx, hφ _ (Bel_mem F w _ _ _ _ _)]
  congr 1
  rw [etaFst_one_val, etaSnd_one_val, hαv, hαv, distribHaarChar_fst, distribHaarChar_snd, norm_div, div_pow]
  exact cpow_scalar (pow_nonneg (norm_nonneg _) _) (pow_pos (norm_pos_iff.mpr hx) _) s

end Main

end MOEBW

end

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F)
      (_hkf : glFin (𝓞 F) F k = 1)
      (_hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)
      (x : AdeleRing (𝓞 F) F),
    let kw : Matrix (Fin 2) (Fin 2) w.Completion := (archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion)
    ∀ (_hx : kw 0 0 + x.1 w * kw 1 0 ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (Function.update x.1 w ((kw 0 1 + x.1 w * kw 1 1) / (kw 0 0 + x.1 w * kw 1 0)), x.2)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
      = (((‖kw.det‖ ^ w.mult : ℝ)) : ℂ) ^ (s + 1 / 2)
        * (((‖kw 0 0 + x.1 w * kw 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by
  intro α hα s φ hφ w k hkf hka x kw hx
  exact MOEBW.main F w k hkf hka α hα (fun t => rfl) s φ hφ x hx

end S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
end P2MW
export P2MW.S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply (solution)
