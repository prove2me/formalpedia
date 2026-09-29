-- Prove2me | solution 1 for AutomorphicForm.exists_uniform_iwasawa_mul_of_glFin_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d3cfb094-70c4-575b-b9de-ed810a98a60f

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

namespace IwCompact32

section Local

variable {L : Type*} [NormedField L]

noncomputable def entrySq (A : Matrix (Fin 2) (Fin 2) L) : ℝ :=
  (‖A 0 0‖ ^ 2 + ‖A 1 0‖ ^ 2) + (‖A 0 1‖ ^ 2 + ‖A 1 1‖ ^ 2)

theorem entrySq_nonneg (A : Matrix (Fin 2) (Fin 2) L) : 0 ≤ entrySq A := by
  unfold entrySq; positivity

theorem norm_add_mul_sq_le (x y a b : L) :
    ‖x * a + y * b‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h1 : ‖x * a + y * b‖ ≤ ‖x‖ * ‖a‖ + ‖y‖ * ‖b‖ := by
    calc ‖x * a + y * b‖ ≤ ‖x * a‖ + ‖y * b‖ := norm_add_le _ _
      _ = ‖x‖ * ‖a‖ + ‖y‖ * ‖b‖ := by rw [norm_mul, norm_mul]
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have h0 : 0 ≤ ‖x * a + y * b‖ := norm_nonneg _
  calc ‖x * a + y * b‖ ^ 2 ≤ (‖x‖ * ‖a‖ + ‖y‖ * ‖b‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
        nlinarith [sq_nonneg (‖x‖ * ‖b‖ - ‖y‖ * ‖a‖), mul_nonneg hx ha, mul_nonneg hy hb]

theorem rowNormSq_mul_le (A B : Matrix (Fin 2) (Fin 2) L) :
    rowNormSq (A * B) ≤ rowNormSq A * entrySq B := by
  have h : ∀ j : Fin 2, (A * B) 1 j = A 1 0 * B 0 j + A 1 1 * B 1 j := by
    intro j; rw [Matrix.mul_apply, Fin.sum_univ_two]
  unfold rowNormSq entrySq
  rw [h 0, h 1, mul_add]
  exact add_le_add (norm_add_mul_sq_le _ _ _ _) (norm_add_mul_sq_le _ _ _ _)

theorem rowNormSq_eq_one_of_isRowIsometry {k : GL (Fin 2) L} (hk : IsRowIsometry k) :
    rowNormSq (k : Matrix (Fin 2) (Fin 2) L) = 1 := by
  have h := hk.2 0 1
  rw [zero_mul, one_mul, zero_add, zero_mul, one_mul, zero_add, norm_zero, norm_one, one_pow,
    zero_pow two_ne_zero, zero_add] at h
  exact h

theorem entrySq_pos (g : GL (Fin 2) L) : 0 < entrySq (g : Matrix (Fin 2) (Fin 2) L) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rcases (entrySq_nonneg (g : Matrix (Fin 2) (Fin 2) L)).lt_or_eq with h | h
  · exact h
  exfalso
  apply hdet
  have hn := fun i j => sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) i j‖
  have h' := h.symm
  unfold entrySq at h'
  have a00 : ‖(g : Matrix (Fin 2) (Fin 2) L) 0 0‖ ^ 2 = 0 := by linarith [hn 0 0, hn 0 1, hn 1 0, hn 1 1]
  have a01 : ‖(g : Matrix (Fin 2) (Fin 2) L) 0 1‖ ^ 2 = 0 := by linarith [hn 0 0, hn 0 1, hn 1 0, hn 1 1]
  have b00 : (g : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp a00)
  have b01 : (g : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp a01)
  rw [Matrix.det_fin_two, b00, b01, zero_mul, zero_mul, sub_zero]

theorem local_bounds (k g B k₀ : GL (Fin 2) L) (hk : IsRowIsometry k) (hk₀ : IsRowIsometry k₀)
    (hB : (B : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h : k * g = B * k₀) :
    Real.sqrt (entrySq ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))⁻¹
        ≤ ‖(B : Matrix (Fin 2) (Fin 2) L) 1 1‖ ∧
    ‖(B : Matrix (Fin 2) (Fin 2) L) 1 1‖ ≤ Real.sqrt (entrySq (g : Matrix (Fin 2) (Fin 2) L)) ∧
    ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ / entrySq (g : Matrix (Fin 2) (Fin 2) L)
        ≤ ‖(B : Matrix (Fin 2) (Fin 2) L) 0 0‖ * ‖(B : Matrix (Fin 2) (Fin 2) L) 1 1‖⁻¹ ∧
    ‖(B : Matrix (Fin 2) (Fin 2) L) 0 0‖ * ‖(B : Matrix (Fin 2) (Fin 2) L) 1 1‖⁻¹
        ≤ ‖(g : Matrix (Fin 2) (Fin 2) L).det‖
            * entrySq ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  set E := entrySq (g : Matrix (Fin 2) (Fin 2) L) with hE
  set E' := entrySq ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hE'
  set D := ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ with hD
  set t := ‖(B : Matrix (Fin 2) (Fin 2) L) 1 1‖ with ht
  set s := ‖(B : Matrix (Fin 2) (Fin 2) L) 0 0‖ with hs
  set ρ2 := rowNormSq ((k * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hρ2
  have hk1 : rowNormSq (k : Matrix (Fin 2) (Fin 2) L) = 1 := rowNormSq_eq_one_of_isRowIsometry hk
  have hup : ρ2 ≤ E := by
    have h1 := rowNormSq_mul_le (k : Matrix (Fin 2) (Fin 2) L) (g : Matrix (Fin 2) (Fin 2) L)
    rw [hk1, one_mul] at h1
    exact h1
  have hlow : 1 ≤ ρ2 * E' := by
    have h1 := rowNormSq_mul_le ((k * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
    rwa [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel_right, hk1] at h1
  have hρt : ρ2 = t ^ 2 := by
    rw [hρ2, h, rowNormSq_mul_rowIsometry B hk₀]
    show ‖(B : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(B : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2 = t ^ 2
    rw [hB, norm_zero, zero_pow two_ne_zero, zero_add]
  have hst : s * t = D := by
    have h1 : ‖((k * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det‖ = D := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, hk.1, one_mul]
    have h2 : ‖((B * k₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det‖ = s * t := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, hk₀.1, mul_one,
        Matrix.det_fin_two, hB, mul_zero, sub_zero, norm_mul]
    rw [← h1, h, h2]
  have ht0 : 0 ≤ t := norm_nonneg _
  have hE'0 : 0 ≤ E' := entrySq_nonneg _
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [hρt, ← h'] at hlow; norm_num at hlow
  have hρpos : 0 < ρ2 := by rw [hρt]; positivity
  have hE'pos : 0 < E' := by
    rcases hE'0.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at hlow; norm_num at hlow
  have hD0 : 0 ≤ D := norm_nonneg _
  have hsD : s * t⁻¹ = D / ρ2 := by
    rw [← hst, hρt]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Real.sqrt E'⁻¹ ≤ Real.sqrt (t ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          rw [← hρt, inv_eq_one_div, div_le_iff₀ hE'pos]
          exact hlow
      _ = t := Real.sqrt_sq ht0
  · calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht0).symm
      _ ≤ Real.sqrt E := by
          refine Real.sqrt_le_sqrt ?_
          rw [← hρt]
          exact hup
  · rw [hsD]
    exact div_le_div_of_nonneg_left hD0 hρpos hup
  · rw [hsD, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    rw [inv_eq_one_div, div_le_iff₀ hρpos, mul_comm]
    exact hlow

end Local

theorem gl2_ext {R : Type*} [CommRing R] {A B : GL (Fin 2) R}
    (h00 : (A : Matrix (Fin 2) (Fin 2) R) 0 0 = (B : Matrix (Fin 2) (Fin 2) R) 0 0)
    (h01 : (A : Matrix (Fin 2) (Fin 2) R) 0 1 = (B : Matrix (Fin 2) (Fin 2) R) 0 1)
    (h10 : (A : Matrix (Fin 2) (Fin 2) R) 1 0 = (B : Matrix (Fin 2) (Fin 2) R) 1 0)
    (h11 : (A : Matrix (Fin 2) (Fin 2) R) 1 1 = (B : Matrix (Fin 2) (Fin 2) R) 1 1) : A = B :=
  Matrix.GeneralLinearGroup.ext fun i j => by
    fin_cases i <;> fin_cases j
    exacts [h00, h01, h10, h11]

section Adelic

variable (K : Type) [Field K] [NumberField K]

noncomputable def archUnit (t : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((t : AdeleRing (𝓞 K) K).1, 1)
  inv := (((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1, 1)
  val_inv := by
    refine Prod.ext ?_ (mul_one 1)
    show (t : AdeleRing (𝓞 K) K).1 * ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1
      = (1 : AdeleRing (𝓞 K) K).1
    exact congrArg Prod.fst t.mul_inv
  inv_val := by
    refine Prod.ext ?_ (mul_one 1)
    show ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * (t : AdeleRing (𝓞 K) K).1
      = (1 : AdeleRing (𝓞 K) K).1
    exact congrArg Prod.fst t.inv_mul

theorem archUnit_val_fst (t : (AdeleRing (𝓞 K) K)ˣ) :
    ((archUnit K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = (t : AdeleRing (𝓞 K) K).1 := rfl

theorem archUnit_val_snd (t : (AdeleRing (𝓞 K) K)ˣ) :
    ((archUnit K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem nzd_entries (ν : AdeleRing (𝓞 K) K) (z b : (AdeleRing (𝓞 K) K)ˣ) :
    ((unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = (z : AdeleRing (𝓞 K) K) * b ∧
    ((unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = ν * z ∧
    ((unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
    ((unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = z := by
  have hn : ((unipotentGL2 ν : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = !![1, ν; 0, 1] := rfl
  have hz : ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = Matrix.diagonal fun _ => (z : AdeleRing (𝓞 K) K) := rfl
  have hb : ((diagOne b : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = Matrix.diagonal ![(b : AdeleRing (𝓞 K) K), 1] := rfl
  simp only [Matrix.GeneralLinearGroup.coe_mul, hn, hz, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isRowIsometry_arch_conj (w : InfinitePlace K) (P B k₀ : AdelicGL2 (𝓞 K) K)
    (hPB : archComponent K w (glArch (𝓞 K) K P) = archComponent K w (glArch (𝓞 K) K B))
    (hk₀ : IsRowIsometry (archComponent K w (glArch (𝓞 K) K k₀))) :
    IsRowIsometry (archComponent K w (glArch (𝓞 K) K (P⁻¹ * (B * k₀)))) := by
  rw [map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, hPB, inv_mul_cancel_left]
  exact hk₀

end Adelic

end IwCompact32

open IwCompact32 in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (g : AdelicGL2 (𝓞 K) K) (hg : glFin (𝓞 K) K g = 1) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (ν : AdeleRing (𝓞 K) K) (z b : (AdeleRing (𝓞 K) K)ˣ) (k' : AdelicGL2 (𝓞 K) K),
          ν.2 = 0 ∧ ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ((b : AdeleRing (𝓞 K) K)).2 = 1 ∧
          glFin (𝓞 K) K k' = 1 ∧
          (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k'))) ∧
          k * g = unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne b * k' ∧
          (∀ w : InfinitePlace K, m ≤ ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ∧ ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ≤ M ∧
            m ≤ ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ∧ ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ≤ M) := by
  classical

  let E : InfinitePlace K → ℝ := fun w =>
    entrySq ((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion)
  let E' : InfinitePlace K → ℝ := fun w =>
    entrySq (((archComponent K w (glArch (𝓞 K) K g))⁻¹ : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion)
  let D : InfinitePlace K → ℝ := fun w =>
    ‖((archComponent K w (glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).det‖
  let lo : InfinitePlace K → ℝ := fun w => min (Real.sqrt (E' w)⁻¹) (D w / E w)
  let hi : InfinitePlace K → ℝ := fun w => max (Real.sqrt (E w)) (D w * E' w)
  have hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
  have hlo_pos : ∀ w, 0 < lo w := by
    intro w
    have hEw : 0 < E w := entrySq_pos (archComponent K w (glArch (𝓞 K) K g))
    have hE'w : 0 < E' w := entrySq_pos (archComponent K w (glArch (𝓞 K) K g))⁻¹
    have hDw : 0 < D w := by
      refine norm_pos_iff.mpr ?_
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact lt_min (Real.sqrt_pos.mpr (inv_pos.mpr hE'w)) (div_pos hDw hEw)
  refine ⟨Finset.univ.inf' hne lo, max (Finset.univ.inf' hne lo) (Finset.univ.sup' hne hi),
    (Finset.lt_inf'_iff hne).mpr fun w _ => hlo_pos w, le_max_left _ _, ?_⟩
  intro k hk hkiso
  obtain ⟨b₀, k₀, hb₀, -, hk₀, hh⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K (k * g)
  have hb₀' : (b₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := hb₀
  let Bsub : ↥(adelicBorel (𝓞 K) K) := ⟨b₀, hb₀⟩
  let t₁ : (AdeleRing (𝓞 K) K)ˣ := borelDiagFst Bsub
  let t₂ : (AdeleRing (𝓞 K) K)ˣ := borelDiagSnd Bsub
  let u : AdeleRing (𝓞 K) K := (b₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1
  let z : (AdeleRing (𝓞 K) K)ˣ := archUnit K t₂
  let bb : (AdeleRing (𝓞 K) K)ˣ := archUnit K (t₁ * t₂⁻¹)
  let ν : AdeleRing (𝓞 K) K := ((u * ((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1, 0)
  let P : AdelicGL2 (𝓞 K) K := unipotentGL2 ν * centralScalar (𝓞 K) K z * diagOne bb
  have hP := nzd_entries K ν z bb

  have ht₂inv : ∀ w : InfinitePlace K,
      ((t₂ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
        * (((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := fun w =>
    congrArg (fun a : AdeleRing (𝓞 K) K => a.1 w) t₂.mul_inv
  have hPB : ∀ w : InfinitePlace K,
      archComponent K w (glArch (𝓞 K) K P) = archComponent K w (glArch (𝓞 K) K b₀) := by
    intro w
    refine gl2_ext ?_ ?_ ?_ ?_ <;>
      rw [archComponent_apply, glArch_apply, archComponent_apply, glArch_apply]
    · rw [hP.1]
      show ((t₂ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
          * (((t₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
            * (((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w)
        = ((t₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
      rw [mul_left_comm, ht₂inv w, mul_one]
    · rw [hP.2.1]
      show u.1 w * (((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w
          * ((t₂ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = u.1 w
      rw [mul_assoc, mul_comm ((((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w),
        ht₂inv w, mul_one]
    · rw [hP.2.2.1, hb₀']
    · rw [hP.2.2.2]
      rfl
  refine ⟨ν, z, bb, P⁻¹ * (k * g), rfl, rfl, rfl, ?_, ?_, (mul_inv_cancel_left P (k * g)).symm, ?_⟩
  ·
    rw [map_mul, map_mul, map_inv, hk, hg, mul_one, mul_one, inv_eq_one]
    refine gl2_ext ?_ ?_ ?_ ?_ <;> rw [glFin_apply, Matrix.GeneralLinearGroup.coe_one]
    · rw [hP.1]
      show (1 : FiniteAdeleRing (𝓞 K) K) * 1 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 0 0
      rw [mul_one, Matrix.one_apply_eq]
    · rw [hP.2.1]
      show (0 : FiniteAdeleRing (𝓞 K) K) * 1 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 0 1
      rw [mul_one, Matrix.one_apply_ne (by decide)]
    · rw [hP.2.2.1]
      show (0 : FiniteAdeleRing (𝓞 K) K) = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 0
      rw [Matrix.one_apply_ne (by decide)]
    · rw [hP.2.2.2]
      show (1 : FiniteAdeleRing (𝓞 K) K) = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) 1 1
      rw [Matrix.one_apply_eq]
  ·
    intro w
    rw [hh]
    exact isRowIsometry_arch_conj K w P b₀ k₀ (hPB w) (hk₀ w)
  ·
    intro w
    have hhw : archComponent K w (glArch (𝓞 K) K k) * archComponent K w (glArch (𝓞 K) K g)
        = archComponent K w (glArch (𝓞 K) K b₀) * archComponent K w (glArch (𝓞 K) K k₀) := by
      rw [← map_mul, ← map_mul, hh, map_mul, map_mul]
    have hBw : ((archComponent K w (glArch (𝓞 K) K b₀) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
      rw [archComponent_apply, glArch_apply, hb₀']
      rfl
    obtain ⟨h1, h2, h3, h4⟩ := local_bounds _ _ _ _ (hkiso w) (hk₀ w) hBw hhw
    have hzw : ‖((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖
        = ‖((archComponent K w (glArch (𝓞 K) K b₀) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) 1 1‖ := rfl
    have hbw : ‖((bb : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖
        = ‖((archComponent K w (glArch (𝓞 K) K b₀) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) 0 0‖
          * ‖((archComponent K w (glArch (𝓞 K) K b₀) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) 1 1‖⁻¹ := by
      rw [← norm_inv, ← norm_mul]
      show ‖((t₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
          * (((t₂⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖
        = ‖((t₁ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
          * (((t₂ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w)⁻¹‖
      rw [inv_eq_of_mul_eq_one_right (ht₂inv w)]
    have hlo : Finset.univ.inf' hne lo ≤ lo w := Finset.inf'_le lo (Finset.mem_univ w)
    have hhi : hi w ≤ max (Finset.univ.inf' hne lo) (Finset.univ.sup' hne hi) :=
      (Finset.le_sup' hi (Finset.mem_univ w)).trans (le_max_right _ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hzw]; exact hlo.trans ((min_le_left _ _).trans h1)
    · rw [hzw]; exact (h2.trans (le_max_left _ _)).trans hhi
    · rw [hbw]; exact hlo.trans ((min_le_right _ _).trans h3)
    · rw [hbw]; exact (h4.trans (le_max_right _ _)).trans hhi

end S_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_uniform_iwasawa_mul_of_glFin_eq_one (solution)
