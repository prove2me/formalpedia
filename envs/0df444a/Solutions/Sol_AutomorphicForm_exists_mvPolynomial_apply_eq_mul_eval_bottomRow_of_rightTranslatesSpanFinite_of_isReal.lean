-- Prove2me | solution 1 for AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/74c14f1d-74a8-5896-80c3-094c9bf1d815

import Mathlib.Analysis.Fourier.AddCircle
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix
open scoped ComplexConjugate

namespace R4ArchPolyR

section FourierCore

open MeasureTheory AddCircle Submodule

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in

theorem fourier_arg_add (n : ℤ) (u v : AddCircle T) :
    fourier n (u + v) = fourier n u * fourier n v := by
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

omit hT in

theorem fourier_neg_neg (n : ℤ) (v : AddCircle T) :
    fourier (-n) (-v) = fourier n v := by
  have hsm : (-n : ℤ) • (-v) = n • v := by rw [neg_zsmul, zsmul_neg, neg_neg]
  rw [fourier_apply, hsm, ← fourier_apply]

omit hT in

theorem continuous_of_mem_span {s : Set (AddCircle T → ℂ)}
    (hs : ∀ f ∈ s, Continuous f) {v : AddCircle T → ℂ}
    (hv : v ∈ span ℂ s) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => exact continuous_const
  | add f g _ _ ihf ihg => exact ihf.add ihg
  | smul c f _ ih => exact ih.const_smul c

theorem integrable_of_continuous {v : AddCircle T → ℂ} (hv : Continuous v) :
    Integrable v (@haarAddCircle T hT) :=
  hv.integrable_of_hasCompactSupport (isClosed_tsupport v).isCompact

section Core

variable (h : C(AddCircle T, ℂ))

theorem fourierCoeff_translate (c : AddCircle T) (n : ℤ) :
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

theorem support_fourierCoeff_finite (s : Finset (AddCircle T → ℂ))
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

theorem eq_finite_sum_fourier (s : Finset (AddCircle T → ℂ))
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

end FourierCore

section Rot

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

scoped instance fact_two_pi_pos : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨two_pi_pos⟩

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotMat_mem (θ : ℝ) : rotMat θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    { simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      first
      | linear_combination Real.sin_sq_add_cos_sq θ
      | ring }

def rotO (θ : ℝ) : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) := ⟨rotMat θ, rotMat_mem θ⟩

theorem rotO_coe (θ : ℝ) : ((rotO θ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

theorem rotO_add (θ₁ θ₂ : ℝ) : rotO (θ₁ + θ₂) = rotO θ₁ * rotO θ₂ := by
  apply Subtype.ext
  change rotMat (θ₁ + θ₂) = rotMat θ₁ * rotMat θ₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    { simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add]
      try ring }

theorem rotO_periodic : Function.Periodic rotO (2 * Real.pi) := by
  intro θ
  apply Subtype.ext
  change rotMat (θ + 2 * Real.pi) = rotMat θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem continuous_rotMat : Continuous rotMat := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact Real.continuous_cos
  · exact Real.continuous_sin.neg
  · exact Real.continuous_sin
  · exact Real.continuous_cos

theorem continuous_rotO : Continuous rotO := continuous_rotMat.subtype_mk _

theorem entries_of_orthogonal_det_one {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ)
    (hdet : A.det = 1) : A 0 0 = A 1 1 ∧ A 0 1 = -A 1 0 ∧ A 1 0 ^ 2 + A 1 1 ^ 2 = 1 := by
  have hT : star A = Aᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have h1 : Aᵀ * A = 1 := by rw [← hT]; exact Matrix.mem_unitaryGroup_iff'.mp hA
  have h1' : A * Aᵀ = 1 := by rw [← hT]; exact Matrix.mem_unitaryGroup_iff.mp hA
  have h2 : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hadj : Aᵀ = A.adjugate := by
    calc Aᵀ = Aᵀ * (A * A.adjugate) := by rw [h2, mul_one]
      _ = (Aᵀ * A) * A.adjugate := by rw [mul_assoc]
      _ = A.adjugate := by rw [h1, one_mul]
  rw [Matrix.adjugate_fin_two] at hadj
  have e00 := congrFun (congrFun hadj 0) 0
  have e10 := congrFun (congrFun hadj 1) 0
  simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e10
  have e11 := congrFun (congrFun h1' 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq] at e11
  refine ⟨e00, e10, ?_⟩
  nlinarith [e11]

theorem rotO_arg_eq {A : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)}
    (hdet : (A : Matrix (Fin 2) (Fin 2) ℝ).det = 1) :
    rotO (Complex.arg ⟨(A : Matrix (Fin 2) (Fin 2) ℝ) 1 1, (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0⟩) = A := by
  obtain ⟨h00, h01, hsq⟩ := entries_of_orthogonal_det_one A.2 hdet
  set c := (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hd
  set z : ℂ := ⟨d, c⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have h : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      nlinarith [hsq]
    have h0 : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [h, h0]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hcos : Real.cos (Complex.arg z) = d := by
    rw [Complex.cos_arg hz0, hnorm, div_one]
  have hsin : Real.sin (Complex.arg z) = c := by
    rw [Complex.sin_arg, hnorm, div_one]
  apply Subtype.ext
  rw [rotO_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, hcos, hsin, h00, h01, hc, hd]

end Rot

section Circle

theorem periodic_comp_rotO (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) :
    Function.Periodic (fun θ : ℝ => Φ (rotO θ)) (2 * Real.pi) := fun θ => by
  show Φ (rotO (θ + 2 * Real.pi)) = Φ (rotO θ)
  rw [rotO_periodic θ]

def circleFn (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) : AddCircle (2 * Real.pi) → ℂ :=
  (periodic_comp_rotO Φ).lift

theorem circleFn_coe (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (θ : ℝ) :
    circleFn Φ (θ : AddCircle (2 * Real.pi)) = Φ (rotO θ) :=
  (periodic_comp_rotO Φ).lift_coe θ

theorem continuous_circleFn {Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ} (hΦ : Continuous Φ) :
    Continuous (circleFn Φ) := by
  have hqm : Topology.IsQuotientMap ((↑) : ℝ → AddCircle (2 * Real.pi)) := QuotientAddGroup.isQuotientMap_mk _
  rw [hqm.continuous_iff]
  have h : (circleFn Φ ∘ ((↑) : ℝ → AddCircle (2 * Real.pi))) = fun θ : ℝ => Φ (rotO θ) :=
    funext fun θ => circleFn_coe Φ θ
  rw [h]
  exact hΦ.comp continuous_rotO

def circleRestrict : (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) →ₗ[ℂ] (AddCircle (2 * Real.pi) → ℂ) where
  toFun Φ := circleFn Φ
  map_add' Φ₁ Φ₂ := by
    funext θq
    induction θq using QuotientAddGroup.induction_on with
    | H θ =>
      show circleFn (Φ₁ + Φ₂) ↑θ = circleFn Φ₁ ↑θ + circleFn Φ₂ ↑θ
      rw [circleFn_coe, circleFn_coe, circleFn_coe]
      rfl
  map_smul' a Φ := by
    funext θq
    induction θq using QuotientAddGroup.induction_on with
    | H θ =>
      show circleFn (a • Φ) ↑θ = a • circleFn Φ ↑θ
      rw [circleFn_coe, circleFn_coe]
      rfl

theorem circleFn_translate_eq (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (c : ℝ) :
    (fun θq : AddCircle (2 * Real.pi) => circleFn Φ (θq + ↑c)) = circleFn (fun A => Φ (A * rotO c)) := by
  funext θq
  induction θq using QuotientAddGroup.induction_on with
  | H θ =>
    have h1 : ((θ : AddCircle (2 * Real.pi)) + ↑c) = ((θ + c : ℝ) : AddCircle (2 * Real.pi)) := rfl
    show circleFn Φ ((θ : AddCircle (2 * Real.pi)) + ↑c) = _
    rw [h1, circleFn_coe, circleFn_coe, rotO_add]

theorem circleFn_translates_mem_span {Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ}
    (hK : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ), ∀ A' : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
      (fun A => Φ (A * A')) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ s' : Finset (AddCircle (2 * Real.pi) → ℂ), ∀ cq : AddCircle (2 * Real.pi),
      (fun θq => circleFn Φ (θq + cq)) ∈ Submodule.span ℂ (s' : Set (AddCircle (2 * Real.pi) → ℂ)) := by
  classical
  obtain ⟨s, hs⟩ := hK
  refine ⟨s.image fun ψ => circleFn ψ, fun cq => ?_⟩
  induction cq using QuotientAddGroup.induction_on with
  | H c =>
    rw [circleFn_translate_eq Φ c]
    have hmem := hs (rotO c)
    have hmap := Submodule.mem_map_of_mem (f := circleRestrict) hmem
    rw [Submodule.map_span] at hmap
    have himg : circleRestrict '' (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))
        = ((s.image fun ψ => circleFn ψ : Finset (AddCircle (2 * Real.pi) → ℂ)) : Set (AddCircle (2 * Real.pi) → ℂ)) := by
      rw [Finset.coe_image]
      rfl
    rw [himg] at hmap
    exact hmap

theorem comp_rotO_expansion {Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ} (hΦc : Continuous Φ)
    (hK : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ), ∀ A' : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
      (fun A => Φ (A * A')) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ tfin : Finset ℤ, ∀ θ : ℝ,
      Φ (rotO θ) = ∑ n ∈ tfin, fourierCoeff (circleFn Φ) n * fourier n (θ : AddCircle (2 * Real.pi)) := by
  obtain ⟨s', hs'⟩ := circleFn_translates_mem_span hK
  obtain ⟨tfin, ht⟩ := eq_finite_sum_fourier (⟨circleFn Φ, continuous_circleFn hΦc⟩ : C(AddCircle (2 * Real.pi), ℂ)) s' hs'
  refine ⟨tfin, fun θ => ?_⟩
  have hθ := ht ↑θ
  rw [← circleFn_coe Φ θ]
  exact hθ

end Circle

section PolyBook

def fourierPoly (n : ℤ) : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ :=
  if 0 ≤ n then (MvPolynomial.X (Sum.inl 1) + MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inl 0)) ^ n.toNat
  else (MvPolynomial.X (Sum.inl 1) - MvPolynomial.C Complex.I * MvPolynomial.X (Sum.inl 0)) ^ (-n).toNat

theorem eval_fourierPoly (n : ℤ) (θ : ℝ) (v : Fin 2 ⊕ Fin 2 → ℂ)
    (h0 : v (Sum.inl 0) = (Real.sin θ : ℂ)) (h1 : v (Sum.inl 1) = (Real.cos θ : ℂ)) :
    MvPolynomial.eval v (fourierPoly n) = Complex.exp (θ * Complex.I) ^ n := by
  have hexp : Complex.exp (θ * Complex.I) = (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  have hexp' : (Complex.exp (θ * Complex.I))⁻¹ = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
    rw [← Complex.exp_neg]
    have : -(↑θ * Complex.I) = ↑(-θ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  unfold fourierPoly
  split_ifs with hn
  · simp only [map_pow, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, h0, h1]
    rw [← hexp, ← zpow_natCast, Int.toNat_of_nonneg hn]
  · simp only [map_pow, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, h0, h1]
    have hn' : 0 ≤ -n := by omega
    rw [← hexp', inv_pow, ← zpow_natCast, Int.toNat_of_nonneg hn', _root_.zpow_neg, inv_inv]

theorem fourier_coe_eq_exp_zpow (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * Real.pi)) = Complex.exp (θ * Complex.I) ^ n := by
  rw [fourier_coe_apply, ← Complex.exp_int_mul]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

end PolyBook

section Diag

variable {L : Type*} [NormedField L]

def diagGL (u : Lˣ) : GL (Fin 2) L where
  val := !![(u : L), 0; 0, 1]
  inv := !![((u⁻¹ : Lˣ) : L), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagGL_apply_00 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = u := rfl
theorem diagGL_apply_01 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := rfl
theorem diagGL_apply_10 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
theorem diagGL_apply_11 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl
theorem diagGL_inv_apply_10 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
theorem diagGL_inv_apply_11 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl
theorem diagGL_inv_apply_00 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((u⁻¹ : Lˣ) : L) := rfl
theorem diagGL_inv_apply_01 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := rfl

theorem diagGL_mem_borelSubgroup (u : Lˣ) : diagGL u ∈ borelSubgroup L := rfl

theorem det_diagGL (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = u := by
  rw [Matrix.det_fin_two, diagGL_apply_00, diagGL_apply_01, diagGL_apply_10, diagGL_apply_11]
  ring

theorem isRowIsometry_diagGL {u : Lˣ} (hu : ‖(u : L)‖ = 1) : IsRowIsometry (diagGL u) := by
  refine ⟨by rw [det_diagGL, hu], fun x y => ?_⟩
  rw [diagGL_apply_00, diagGL_apply_01, diagGL_apply_10, diagGL_apply_11, mul_zero, add_zero, mul_zero,
    zero_add, mul_one, norm_mul, hu, mul_one]

theorem borelDiagFst_diagGL (u : Lˣ) :
    borelDiagFst (⟨diagGL u, diagGL_mem_borelSubgroup u⟩ : ↥(borelSubgroup L)) = u := by
  apply Units.ext
  rfl

theorem borelDiagSnd_diagGL (u : Lˣ) :
    borelDiagSnd (⟨diagGL u, diagGL_mem_borelSubgroup u⟩ : ↥(borelSubgroup L)) = 1 := by
  apply Units.ext
  rfl

theorem diagGL_inv_mul_apply_one (u : Lˣ) (k : GL (Fin 2) L) (j : Fin 2) :
    ((((diagGL u)⁻¹ * k : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L) 1 j = (k : Matrix (Fin 2) (Fin 2) L) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, diagGL_inv_apply_10,
    diagGL_inv_apply_11, zero_mul, zero_add, one_mul]

theorem det_diagGL_det_inv_mul (k : GL (Fin 2) L) :
    ((((diagGL (Matrix.GeneralLinearGroup.det k))⁻¹ * k : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
  have h : (Matrix.GeneralLinearGroup.det ((diagGL (Matrix.GeneralLinearGroup.det k))⁻¹ * k) : Lˣ) = 1 := by
    rw [map_mul, map_inv]
    have hd : Matrix.GeneralLinearGroup.det (diagGL (Matrix.GeneralLinearGroup.det k)) =
        Matrix.GeneralLinearGroup.det k := by
      apply Units.ext
      exact det_diagGL _
    rw [hd, inv_mul_cancel]
  have := congrArg Units.val h
  simpa using this

end Diag

section Main

variable {F : Type} [Field F] {w : InfinitePlace F}

theorem main (hw : w.IsReal)
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (f : GL (Fin 2) w.Completion → ℂ) (hfc : Continuous f)
    (hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ,
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
        f k = ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
          * MvPolynomial.eval
              (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (fun i => starRingEnd ℂ
                  (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P := by
  classical
  set L := w.Completion
  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal F w hw

  set Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ := fun A => f ((e.symm A : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L)
    with hΦ_def
  have hΦc : Continuous Φ := hfc.comp (continuous_subtype_val.comp (map_continuous e.symm))
  have hΦfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
      ∀ A' : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
        (fun A => Φ (A * A')) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ)) := by
    obtain ⟨s, hs⟩ := hfK
    let r : (GL (Fin 2) L → ℂ) →ₗ[ℂ] (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) :=
      { toFun := fun g A => g ((e.symm A : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨s.image r, fun A' => ?_⟩
    set k' : GL (Fin 2) L := ((e.symm A' : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L) with hk'
    have hk'mem : k' ∈ rowIsometrySubgroup L := (e.symm A').2
    have hmem := hs k' hk'mem
    have heq : (fun A => Φ (A * A')) = r (fun x => f (x * k')) := by
      funext A
      simp only [hΦ_def, r, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Subgroup.coe_mul, hk']
    rw [heq, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  obtain ⟨tfin, htfin⟩ := comp_rotO_expansion hΦc hΦfin
  refine ⟨∑ n ∈ tfin, MvPolynomial.C (fourierCoeff (circleFn Φ) n) * fourierPoly n, fun k hk => ?_⟩

  set δ : Lˣ := Matrix.GeneralLinearGroup.det k with hδ
  have hδnorm : ‖(δ : L)‖ = 1 := hk.1
  set b : GL (Fin 2) L := diagGL δ with hb_def
  have hb : b ∈ borelSubgroup L := diagGL_mem_borelSubgroup δ
  have hbiso : IsRowIsometry b := isRowIsometry_diagGL hδnorm
  set k₀ : GL (Fin 2) L := b⁻¹ * k with hk₀_def
  have hk₀ : IsRowIsometry k₀ := hbiso.inv.mul hk
  have hkfac : k = b * k₀ := by rw [hk₀_def, mul_inv_cancel_left]
  have hfk : f k = ((η₁ δ : ℂˣ) : ℂ) * f k₀ := by
    rw [hkfac, hfB b hb hbiso k₀ hk₀]
    have h1 : borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup L)) = δ := borelDiagFst_diagGL δ
    have h2 : borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup L)) = 1 := borelDiagSnd_diagGL δ
    rw [h1, h2, map_one, Units.val_one, mul_one]

  set A₀ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) := e ⟨k₀, hk₀⟩ with hA₀
  have hA₀ent : ∀ i j, ((A₀ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = extensionEmbeddingOfIsReal hw ((k₀ : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => he ⟨k₀, hk₀⟩ i j
  have hA₀map : ((A₀ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
      = (extensionEmbeddingOfIsReal hw).mapMatrix (k₀ : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    rw [hA₀ent]
    rfl
  have hdetk₀ : ((k₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = 1 := det_diagGL_det_inv_mul k
  have hrow : ∀ j : Fin 2, ((k₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 j = (k : Matrix (Fin 2) (Fin 2) L) 1 j :=
    fun j => diagGL_inv_mul_apply_one δ k j
  have hA₀det : ((A₀ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [hA₀map, ← RingHom.map_det, hdetk₀, map_one]
  set θ₀ : ℝ := Complex.arg ⟨((A₀ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1,
    ((A₀ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0⟩ with hθ₀
  have hrot : rotO θ₀ = A₀ := rotO_arg_eq hA₀det
  have hcos : (Real.cos θ₀ : ℂ) = extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) L) 1 1) := by
    have h := congrArg (fun A : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hrot
    simp only [rotO_coe, rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero] at h
    rw [h, hA₀ent, hrow, extensionEmbeddingOfIsReal_apply]
  have hsin : (Real.sin θ₀ : ℂ) = extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) L) 1 0) := by
    have h := congrArg (fun A : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hrot
    simp only [rotO_coe, rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero] at h
    rw [h, hA₀ent, hrow, extensionEmbeddingOfIsReal_apply]

  have hfk₀ : f k₀ = Φ (rotO θ₀) := by
    rw [hrot]
    simp only [hΦ_def, hA₀, ContinuousMulEquiv.symm_apply_apply]
  rw [hfk, hfk₀, htfin θ₀, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, MvPolynomial.eval_C, fourier_coe_eq_exp_zpow,
    eval_fourierPoly n θ₀ _ (by simp [hsin]) (by simp [hcos])]

end Main

end R4ArchPolyR
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal.R4ArchPolyR"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal.R4ArchPolyR"

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem solution
    (F : Type) [Field F] (w : InfinitePlace F) (hw : w.IsReal)
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (f : GL (Fin 2) w.Completion → ℂ) (_hfc : Continuous f)
    (_hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (_hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ,
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
        f k = ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
          * MvPolynomial.eval
              (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (fun i => starRingEnd ℂ
                  (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P :=
  R4ArchPolyR.main hw η₁ η₂ f _hfc _hfK _hfB

end S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isReal (solution)
