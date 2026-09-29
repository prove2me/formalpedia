-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/864eb509-678e-5bd5-a0fb-f9b22cbcf60a

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace ProperUnifCore

open Matrix Topology Filter Set

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℂ

def ι : GL (Fin 2) ℝ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map Complex.ofRealHom

def cjGL : GL (Fin 2) ℂ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map (starRingEnd ℂ : ℂ →+* ℂ)

theorem ι_val (m : GL (Fin 2) ℝ) : ((ι m : GL (Fin 2) ℂ) : M2) = (m : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofRealHom := rfl

theorem cjGL_val (y : GL (Fin 2) ℂ) : ((cjGL y : GL (Fin 2) ℂ) : M2) = (y : M2).map (starRingEnd ℂ) := rfl

theorem cjGL_ι (m : GL (Fin 2) ℝ) : cjGL (ι m) = ι m := by
  refine Units.ext ?_
  rw [cjGL_val, ι_val, Matrix.map_map]
  congr 1
  funext r
  simp

theorem cjGL_cjGL (y : GL (Fin 2) ℂ) : cjGL (cjGL y) = y := by
  refine Units.ext ?_
  rw [cjGL_val, cjGL_val, Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id (y : M2)]
  congr 1
  funext z
  simp

theorem continuous_GL_map {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (f : R →+* S) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hf).congr fun _ => rfl
  · exact (Units.continuous_coe_inv.matrix_map hf).congr fun x => by
      show ((x⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f = _
      rfl

theorem continuous_ι : Continuous ι := continuous_GL_map _ Complex.continuous_ofReal

theorem continuous_cjGL : Continuous cjGL := continuous_GL_map _ Complex.continuous_conj

theorem ι_scalar_comm (d : ℝˣ) (y : GL (Fin 2) ℂ) :
    ι (Matrix.GeneralLinearGroup.scalar (Fin 2) d) * y = y * ι (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have e : (Matrix.diagonal fun _ : Fin 2 => (d : ℝ)).map Complex.ofRealHom = ((d : ℝ) : ℂ) • (1 : M2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem trace_ι (t : GL (Fin 2) ℝ) :
    Matrix.trace ((ι t : GL (Fin 2) ℂ) : M2) = ((Matrix.trace (t : Matrix (Fin 2) (Fin 2) ℝ) : ℝ) : ℂ) := by
  rw [ι_val, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp

theorem exists_ι_eq_of_map_star_eq (m : GL (Fin 2) ℂ) (hm : (m : M2).map (starRingEnd ℂ) = m) :
    ∃ m₀ : GL (Fin 2) ℝ, ι m₀ = m := by
  set mr : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ((m : M2) i j).re with hmr
  have hre : mr.map Complex.ofRealHom = (m : M2) := by
    ext i j
    have h := congrFun (congrFun hm i) j
    simp only [Matrix.map_apply, starRingEnd_apply] at h
    simp only [Matrix.map_apply, hmr, Complex.ofRealHom_eq_coe]
    exact (Complex.conj_eq_iff_re.1 h)
  have hdet : Matrix.det mr ≠ 0 := by
    intro h0
    have h1 : Matrix.det (m : M2) = 0 := by
      have hmd := RingHom.map_det Complex.ofRealHom mr
      rw [RingHom.mapMatrix_apply, hre] at hmd
      rw [← hmd, h0, map_zero]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero h1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero mr hdet, Units.ext ?_⟩
  rw [ι_val]
  exact hre

end ProperUnifCore

namespace QuatCore

open Matrix Topology Filter Set ProperUnifCore

def D0 (c : ℝ) (hc : c ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, (c : ℂ); 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp [hc])

theorem D0_val (c : ℝ) (hc : c ≠ 0) : ((D0 c hc : GL (Fin 2) ℂ) : M2) = !![0, (c : ℂ); 1, 0] := rfl

def rs (e : ℝ) (he : e ≠ 0) : GL (Fin 2) ℂ := ι (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 e he))

theorem rs_val (e : ℝ) (he : e ≠ 0) : ((rs e he : GL (Fin 2) ℂ) : M2) = ((e : ℝ) : ℂ) • (1 : M2) := by
  rw [rs, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def TwRel (D t : GL (Fin 2) ℂ) : Prop := t * D * (cjGL t)⁻¹ = D

theorem twRel_iff (D t : GL (Fin 2) ℂ) : TwRel D t ↔ t * D = D * cjGL t := by
  unfold TwRel
  rw [mul_inv_eq_iff_eq_mul]

theorem cjGL_apply (t : GL (Fin 2) ℂ) (i j : Fin 2) :
    ((cjGL t : GL (Fin 2) ℂ) : M2) i j = (starRingEnd ℂ) (((t : GL (Fin 2) ℂ) : M2) i j) := rfl

theorem entries_of_twRel_D0 (c : ℝ) (hc : c ≠ 0) (t : GL (Fin 2) ℂ) (ht : TwRel (D0 c hc) t) :
    ((t : GL (Fin 2) ℂ) : M2) 0 1 = (c : ℂ) * (starRingEnd ℂ) (((t : GL (Fin 2) ℂ) : M2) 1 0) ∧
      ((t : GL (Fin 2) ℂ) : M2) 1 1 = (starRingEnd ℂ) (((t : GL (Fin 2) ℂ) : M2) 0 0) := by
  rw [twRel_iff] at ht
  have hm := congrArg (fun u : GL (Fin 2) ℂ => (u : M2)) ht
  simp only [Units.val_mul, D0_val] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, cjGL_apply] at h00 h10
  simp [Matrix.of_apply] at h00 h10
  exact ⟨by rw [h00], by rw [h10]⟩

theorem det_of_twRel_D0 (c : ℝ) (hc : c ≠ 0) (t : GL (Fin 2) ℂ) (ht : TwRel (D0 c hc) t) :
    Matrix.det ((t : GL (Fin 2) ℂ) : M2) =
      ((‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨h01, h11⟩ := entries_of_twRel_D0 c hc t ht
  rw [Matrix.det_fin_two, h01, h11, Complex.sq_norm, Complex.sq_norm]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  ring

theorem det_pos_of_twRel_D0 (c : ℝ) (hc : c < 0) (t : GL (Fin 2) ℂ) (ht : TwRel (D0 c hc.ne) t) :
    0 < ‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 := by
  have hdet : Matrix.det ((t : GL (Fin 2) ℂ) : M2) ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 t.isUnit).ne_zero
  rw [det_of_twRel_D0 c hc.ne t ht, Complex.ofReal_ne_zero] at hdet
  have h1 : 0 ≤ ‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 := by positivity
  have h2 : 0 ≤ -c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 := by
    have : 0 ≤ -c := by linarith
    positivity
  rcases (show 0 ≤ ‖((t : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((t : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 by linarith).lt_or_eq with h | h
  · exact h
  · exact absurd h.symm hdet

def S (c : ℝ) : Set (ℂ × ℂ) := {p | ‖p.1‖ ^ 2 - c * ‖p.2‖ ^ 2 = 1}

theorem isCompact_S (c : ℝ) (hc : c < 0) : IsCompact (S c) := by
  haveI : ProperSpace (ℂ × ℂ) := inferInstance
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := max 1 (Real.sqrt (1 / -c)))).subset ?_
    intro p hp
    simp only [S, Set.mem_setOf_eq] at hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    have hc' : 0 < -c := by linarith
    have ha : ‖p.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p.2, sq_nonneg ‖p.2‖]
    have he : ‖p.2‖ ^ 2 ≤ 1 / -c := by
      rw [div_eq_mul_inv, le_mul_inv_iff₀ hc']
      nlinarith [sq_nonneg ‖p.1‖]
    constructor
    · exact le_trans (by nlinarith [norm_nonneg p.1]) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [← Real.sqrt_sq (norm_nonneg p.2)]
      exact Real.sqrt_le_sqrt he

def qM (c : ℝ) (p : ℂ × ℂ) : M2 := !![p.1, (c : ℂ) * (starRingEnd ℂ) p.2; p.2, (starRingEnd ℂ) p.1]

theorem continuous_qM (c : ℝ) : Continuous (qM c) := by
  unfold qM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem det_qM (c : ℝ) (p : ℂ × ℂ) :
    Matrix.det (qM c p) = ((‖p.1‖ ^ 2 - c * ‖p.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [qM, Matrix.det_fin_two_of, Complex.sq_norm, Complex.sq_norm]
  push_cast
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  ring

def qU (c : ℝ) (p : S c) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (qM c p.1) (by
    rw [det_qM]
    have hp : ‖(p.1).1‖ ^ 2 - c * ‖(p.1).2‖ ^ 2 = 1 := p.2
    rw [hp]; simp)

theorem qU_val (c : ℝ) (p : S c) : ((qU c p : GL (Fin 2) ℂ) : M2) = qM c p.1 := rfl

theorem det_qU (c : ℝ) (p : S c) : Matrix.det ((qU c p : GL (Fin 2) ℂ) : M2) = 1 := by
  rw [qU_val, det_qM]
  have hp : ‖(p.1).1‖ ^ 2 - c * ‖(p.1).2‖ ^ 2 = 1 := p.2
  rw [hp]; simp

theorem continuous_qU (c : ℝ) : Continuous (qU c) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_qM c).comp continuous_subtype_val).congr fun p => rfl
  · have e : (fun p : S c => (((qU c p)⁻¹ : GL (Fin 2) ℂ) : M2)) = fun p => (qM c p.1).adjugate := by
      funext p
      rw [Matrix.coe_units_inv, qU_val, Matrix.inv_def, ← qU_val, det_qU]
      simp
    rw [e]
    exact (continuous_qM c).matrix_adjugate.comp continuous_subtype_val

theorem twRel_qU (c : ℝ) (hc : c ≠ 0) (p : S c) : TwRel (D0 c hc) (qU c p) := by
  rw [twRel_iff]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, qU_val, D0_val, cjGL_val, qU_val, qM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

section NormalForm

variable (c : ℝ) (hc : c < 0) (D : GL (Fin 2) ℂ)
  (hD : ((D * cjGL D : GL (Fin 2) ℂ) : M2) = (c : ℂ) • (1 : M2))

include hD in
theorem normEq (i j : Fin 2) :
    ∑ k : Fin 2, ((D : GL (Fin 2) ℂ) : M2) i k * (starRingEnd ℂ) (((D : GL (Fin 2) ℂ) : M2) k j) =
      if i = j then (c : ℂ) else 0 := by
  have h := congrFun (congrFun hD i) j
  rw [Units.val_mul, Matrix.mul_apply, cjGL_val] at h
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  exact h

include hc hD in
theorem D10_ne : ((D : GL (Fin 2) ℂ) : M2) 1 0 ≠ 0 := by
  intro h0
  have h := normEq c D hD 0 0
  rw [Fin.sum_univ_two, h0, map_zero, mul_zero, add_zero, if_pos rfl] at h

  have hre := congrArg Complex.re h
  rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] at hre
  have : 0 ≤ Complex.normSq (((D : GL (Fin 2) ℂ) : M2) 0 0) := Complex.normSq_nonneg _
  simp at hre
  linarith

def xD : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, ((D : GL (Fin 2) ℂ) : M2) 0 0; 0, ((D : GL (Fin 2) ℂ) : M2) 1 0]
    (by rw [Matrix.det_fin_two_of]; simpa using D10_ne c hc D hD)

theorem xD_val : ((xD c hc D hD : GL (Fin 2) ℂ) : M2) =
    !![1, ((D : GL (Fin 2) ℂ) : M2) 0 0; 0, ((D : GL (Fin 2) ℂ) : M2) 1 0] := rfl

include hc hD in

theorem conj_eq : D * cjGL (xD c hc D hD) = xD c hc D hD * D0 c hc.ne := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, cjGL_val, xD_val, D0_val]
  have h00 := normEq c D hD 0 0
  have h10 := normEq c D hD 1 0
  rw [Fin.sum_univ_two] at h00 h10
  simp only [if_pos, if_neg, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true, reduceIte] at h00 h10
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  · exact h00
  · exact h10

include hc hD in
theorem twRel_iff_conj (t : GL (Fin 2) ℂ) :
    TwRel D t ↔ TwRel (D0 c hc.ne) ((xD c hc D hD)⁻¹ * t * xD c hc D hD) := by
  have key := conj_eq c hc D hD

  have hDeq : D = xD c hc D hD * D0 c hc.ne * (cjGL (xD c hc D hD))⁻¹ := by
    rw [← key]; group
  rw [twRel_iff, twRel_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h

    have := congrArg (fun u => (xD c hc D hD)⁻¹ * u * cjGL (xD c hc D hD)) h
    beta_reduce at this
    rw [show (xD c hc D hD)⁻¹ * (t * D) * cjGL (xD c hc D hD) =
        (xD c hc D hD)⁻¹ * t * xD c hc D hD * ((xD c hc D hD)⁻¹ * (D * cjGL (xD c hc D hD))) by group, key,
      show (xD c hc D hD)⁻¹ * (D * cjGL t) * cjGL (xD c hc D hD) =
        ((xD c hc D hD)⁻¹ * (D * cjGL (xD c hc D hD))) * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD)) by group,
      key] at this
    rw [show (xD c hc D hD)⁻¹ * t * xD c hc D hD * ((xD c hc D hD)⁻¹ * (xD c hc D hD * D0 c hc.ne)) =
        (xD c hc D hD)⁻¹ * t * xD c hc D hD * D0 c hc.ne by group,
      show (xD c hc D hD)⁻¹ * (xD c hc D hD * D0 c hc.ne) * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD)) =
        D0 c hc.ne * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD)) by group] at this
    exact this
  · intro h
    rw [hDeq]
    have := congrArg (fun u => xD c hc D hD * u * (cjGL (xD c hc D hD))⁻¹) h
    beta_reduce at this
    calc t * (xD c hc D hD * D0 c hc.ne * (cjGL (xD c hc D hD))⁻¹)
        = xD c hc D hD * ((xD c hc D hD)⁻¹ * t * xD c hc D hD * D0 c hc.ne) * (cjGL (xD c hc D hD))⁻¹ := by group
      _ = xD c hc D hD * (D0 c hc.ne * ((cjGL (xD c hc D hD))⁻¹ * cjGL t * cjGL (xD c hc D hD))) *
            (cjGL (xD c hc D hD))⁻¹ := by rw [h]
      _ = xD c hc D hD * D0 c hc.ne * (cjGL (xD c hc D hD))⁻¹ * cjGL t := by group

end NormalForm

theorem core (c : ℝ) (hc : c < 0) (D : GL (Fin 2) ℂ)
    (hD : ((D * cjGL D : GL (Fin 2) ℂ) : M2) = (c : ℂ) • (1 : M2)) :
    ∃ C : Set (GL (Fin 2) ℂ), IsCompact C ∧ (∀ k ∈ C, TwRel D k) ∧
      ∀ t : GL (Fin 2) ℂ, TwRel D t → ∃ (e : ℝ) (he : e ≠ 0), ∃ k ∈ C, t = rs e he * k := by
  set x := xD c hc D hD with hx
  set F : S c → GL (Fin 2) ℂ := fun p => x * qU c p * x⁻¹ with hF
  have hSc : IsCompact (S c) := isCompact_S c hc
  haveI : CompactSpace (S c) := isCompact_iff_compactSpace.1 hSc
  have hFc : Continuous F := (continuous_const.mul (continuous_qU c)).mul continuous_const
  refine ⟨Set.range F, isCompact_range hFc, ?_, ?_⟩
  · rintro k ⟨p, rfl⟩
    rw [twRel_iff_conj c hc D hD]
    have : (xD c hc D hD)⁻¹ * (x * qU c p * x⁻¹) * xD c hc D hD = qU c p := by rw [hx]; group
    rw [this]
    exact twRel_qU c hc.ne p
  · intro t ht
    set s := x⁻¹ * t * x with hs
    have hs' : TwRel (D0 c hc.ne) s := (twRel_iff_conj c hc D hD t).1 ht
    obtain ⟨h01, h11⟩ := entries_of_twRel_D0 c hc.ne s hs'
    set r : ℝ := ‖((s : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - c * ‖((s : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 with hr
    have hrpos : 0 < r := det_pos_of_twRel_D0 c hc s hs'
    set e : ℝ := Real.sqrt r with he
    have hepos : 0 < e := Real.sqrt_pos.2 hrpos
    have hesq : e ^ 2 = r := Real.sq_sqrt hrpos.le

    set a : ℂ := (e : ℂ)⁻¹ * ((s : GL (Fin 2) ℂ) : M2) 0 0 with ha
    set f : ℂ := (e : ℂ)⁻¹ * ((s : GL (Fin 2) ℂ) : M2) 1 0 with hf
    have hp : ‖a‖ ^ 2 - c * ‖f‖ ^ 2 = 1 := by
      rw [ha, hf, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hepos]
      field_simp
      rw [hesq, hr]
    refine ⟨e, hepos.ne', F ⟨(a, f), hp⟩, ⟨_, rfl⟩, ?_⟩

    have hsval : ((s : GL (Fin 2) ℂ) : M2) = (e : ℂ) • qM c (a, f) := by
      rw [Matrix.eta_fin_two ((s : GL (Fin 2) ℂ) : M2), h01, h11, qM]
      have hene : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hepos.ne'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hf, Matrix.smul_apply] <;> field_simp
    have hsu : s = rs e hepos.ne' * qU c ⟨(a, f), hp⟩ := by
      refine Units.ext ?_
      show ((s : GL (Fin 2) ℂ) : M2) = _
      rw [hsval, Units.val_mul, rs_val, qU_val, Matrix.smul_mul, Matrix.one_mul]
    have hrs : ∀ z : GL (Fin 2) ℂ, rs e hepos.ne' * z = z * rs e hepos.ne' := fun z =>
      ι_scalar_comm (Units.mk0 e hepos.ne') z
    calc t = x * s * x⁻¹ := by rw [hs]; group
      _ = x * (rs e hepos.ne' * qU c ⟨(a, f), hp⟩) * x⁻¹ := by rw [hsu]
      _ = rs e hepos.ne' * (x * qU c ⟨(a, f), hp⟩ * x⁻¹) := by rw [← mul_assoc, ← hrs x]; group

end QuatCore

namespace ProperUnifBridge

open scoped TensorProduct TensorProduct.RightActions
open ProperUnifCore

abbrev TT : Type := ℂ ⊗[ℝ] ℝ

def ρr : TT ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ρr_tmul (z : ℂ) (s : ℝ) : ρr (z ⊗ₜ s) = (s : ℂ) * z := by
  simp [ρr, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem ρr_symm_apply (z : ℂ) : ρr.symm z = z ⊗ₜ 1 := by
  simp [ρr]

def ρrLin : TT →ₗ[ℝ] ℂ where
  toFun := ρr
  map_add' := map_add ρr
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z s =>
        rw [TensorProduct.RightActions.smul_def]
        simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_symm_tmul,
          ρr_tmul, RingHom.id_apply, Complex.real_smul]
        push_cast
        ring
    | add x y hx hy =>
        rw [TensorProduct.RightActions.smul_def, map_add, smul_add, map_add, map_add,
          ← TensorProduct.RightActions.smul_def, ← TensorProduct.RightActions.smul_def, hx, hy, map_add, smul_add]

def ρrSymmLin : ℂ →ₗ[ℝ] TT where
  toFun := ρr.symm
  map_add' := map_add ρr.symm
  map_smul' := by
    intro r z
    rw [ρr_symm_apply, ρr_symm_apply, RingHom.id_apply, TensorProduct.RightActions.smul_def]
    simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.comm_symm_tmul]
    rw [TensorProduct.smul_tmul, smul_eq_mul, mul_one]

theorem continuous_ρr : Continuous ρr := by
  haveI := AutomorphicForm.t2Space_tensor ℝ ℂ ℝ
  exact LinearMap.continuous_of_finiteDimensional ρrLin

theorem continuous_ρr_symm : Continuous ρr.symm :=
  LinearMap.continuous_of_finiteDimensional ρrSymmLin

def ρ : GL (Fin 2) TT →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map ρr.toRingHom

def ρi : GL (Fin 2) ℂ →* GL (Fin 2) TT := Matrix.GeneralLinearGroup.map ρr.symm.toRingHom

theorem ρ_val (x : GL (Fin 2) TT) : ((ρ x : GL (Fin 2) ℂ) : M2) = (x : Matrix (Fin 2) (Fin 2) TT).map ρr := rfl

theorem ρi_val (y : GL (Fin 2) ℂ) :
    ((ρi y : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT) = (y : M2).map ρr.symm := rfl

theorem ρi_ρ (x : GL (Fin 2) TT) : ρi (ρ x) = x := by
  refine Units.ext ?_
  rw [ρi_val, ρ_val, Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id (x : Matrix (Fin 2) (Fin 2) TT)]
  congr 1
  funext e
  simp

theorem ρ_ρi (y : GL (Fin 2) ℂ) : ρ (ρi y) = y := by
  refine Units.ext ?_
  rw [ρ_val, ρi_val, Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id (y : M2)]
  congr 1
  funext e
  simp

theorem continuous_ρi : Continuous ρi := by
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map continuous_ρr_symm

theorem toTensorGL_apply (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL ℝ ℂ ℝ m : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT) i j =
      (1 : ℂ) ⊗ₜ (((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := rfl

theorem ρ_toTensorGL (m : GL (Fin 2) ℝ) : ρ (AutomorphicForm.toTensorGL ℝ ℂ ℝ m) = ι m := by
  refine Units.ext ?_
  ext i j
  rw [ρ_val, ι_val, Matrix.map_apply, Matrix.map_apply, toTensorGL_apply, ρr_tmul, mul_one]
  rfl

theorem toTensorGL_eq_ρi_ι (m : GL (Fin 2) ℝ) : AutomorphicForm.toTensorGL ℝ ℂ ℝ m = ρi (ι m) := by
  rw [← ρ_toTensorGL, ρi_ρ]

theorem ρr_sigma (e : TT) :
    ρr (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe e) = (starRingEnd ℂ) (ρr e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | tmul z s =>
      rw [AutomorphicForm.sigmaTensor]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        ρr_tmul]
      simp [Complex.conj_ofReal]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ρ_sigmaGL (x : GL (Fin 2) TT) : ρ (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe x) = cjGL (ρ x) := by
  refine Units.ext ?_
  rw [ρ_val, cjGL_val, ρ_val]
  show (((x : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT).map (AutomorphicForm.sigmaTensor ℝ ℂ ℝ Complex.conjAe)).map ρr = _
  rw [Matrix.map_map, Matrix.map_map]
  congr 1
  funext e
  exact ρr_sigma e

end ProperUnifBridge

end

open ProperUnifCore ProperUnifBridge QuatCore in
theorem solution
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y) :
    ∃ C : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), IsCompact C ∧
      C ⊆ (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) ∧
      ∀ t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ,
        ∃ e : ℝˣ, ∃ k ∈ C,
          t = toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) e) * k := by

  have hN : AutomorphicForm.normString ℝ ℂ ℝ Complex.conjAe δ = δ * AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
    rw [AutomorphicForm.normString, Complex.finrank_real_complex]
    simp [List.range_succ, Function.iterate_succ, Function.iterate_zero]
  have hδ' : δ * AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe δ =
      y * AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y⁻¹ := by
    rw [AutomorphicForm.IsNormConjugator, hN] at hδ
    rw [hδ]; group
  set D : GL (Fin 2) ℂ := ρ δ with hDdef
  have hcomm := ι_scalar_comm c (ρ y)
  have hD : ((D * cjGL D : GL (Fin 2) ℂ) : M2) = ((c : ℝ) : ℂ) • (1 : M2) := by
    have e1 : D * cjGL D = ι (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
      rw [hDdef, ← ρ_sigmaGL, ← map_mul, hδ', map_mul, map_mul, map_inv, ρ_toTensorGL, ← hcomm]
      group
    rw [e1, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨C, hCc, hCtw, hCall⟩ := QuatCore.core (c : ℝ) hc D hD

  have htw : ∀ t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ↔ TwRel D (ρ t) := by
    intro t
    rw [AutomorphicForm.twistedCentralizer, mem_sigmaCentralizer_iff, TwRel]
    have e : ρ (t * δ * (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe t)⁻¹) = ρ t * D * (cjGL (ρ t))⁻¹ := by
      rw [map_mul, map_mul, map_inv, ρ_sigmaGL, ← hDdef]
    constructor
    · intro h
      rw [← e, h, hDdef]
    · intro h
      have h2 : ρ (t * δ * (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe t)⁻¹) = ρ δ := by rw [e, h, hDdef]
      have h3 := congrArg ρi h2
      rwa [ρi_ρ, ρi_ρ] at h3
  refine ⟨ρi '' C, hCc.image continuous_ρi, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    show ρi k ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ
    rw [htw, ρ_ρi]
    exact hCtw k hk
  · intro t ht
    obtain ⟨e, he, k, hk, htk⟩ := hCall (ρ t) ((htw t).1 ht)
    refine ⟨Units.mk0 e he, ρi k, ⟨k, hk, rfl⟩, ?_⟩
    rw [toTensorGL_eq_ρi_ι, ← map_mul]
    have : ρ t = ι (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 e he)) * k := htk
    rw [← this, ρi_ρ]

end S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_conjAe_eq_scalar_mul_of_neg (solution)
