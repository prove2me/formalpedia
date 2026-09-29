-- Prove2me | solution 1 for AutomorphicForm.ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4e82df3d-964b-5c28-9a3e-c57772d28d67

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
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

namespace KappaEval

open ProperUnifCore QuatCore ProperUnifBridge

theorem continuous_ρ : Continuous ρ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map continuous_ρr

theorem ρr_one_tmul (s : ℝ) : ρr ((1 : ℂ) ⊗ₜ s) = (s : ℂ) := by rw [ρr_tmul, mul_one]

theorem band_iff (e : TT) :
    (∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2), e = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)) ↔
      ρr e ∈ {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    rw [ρr_one_tmul]
    exact ⟨Complex.ofReal_im d, by simpa using hd⟩
  · rintro ⟨him, hre⟩
    refine ⟨(ρr e).re, hre, ?_⟩
    apply ρr.injective
    rw [ρr_one_tmul]
    exact Complex.ext rfl (by simp [him])

theorem isClosed_bandC : IsClosed {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 : ℝ) (Real.exp 2)} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_Icc.preimage Complex.continuous_re)

theorem det_ρ (x : GL (Fin 2) TT) :
    Matrix.det ((ρ x : GL (Fin 2) ℂ) : M2) = ρr (Matrix.det ((x : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT)) := by
  rw [ρ_val]
  exact (RingHom.map_det ρr.toRingHom _).symm

theorem sigmaGL_toTensorGL (m : GL (Fin 2) ℝ) :
    AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe (AutomorphicForm.toTensorGL ℝ ℂ ℝ m) =
      AutomorphicForm.toTensorGL ℝ ℂ ℝ m := by
  have h : ρ (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe (AutomorphicForm.toTensorGL ℝ ℂ ℝ m)) =
      ρ (AutomorphicForm.toTensorGL ℝ ℂ ℝ m) := by
    rw [ρ_sigmaGL, ρ_toTensorGL, cjGL_ι]
  have := congrArg ρi h
  rwa [ρi_ρ, ρi_ρ] at this

theorem toTensorGL_scalar_comm (a : ℝˣ) (g : GL (Fin 2) TT) :
    AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) * g =
      g * AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  have h : ρ (AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) * g) =
      ρ (g * AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) := by
    rw [map_mul, map_mul, ρ_toTensorGL, ι_scalar_comm]
  have := congrArg ρi h
  rwa [ρi_ρ, ρi_ρ] at this

theorem toTensorGL_scalar_mem (a : ℝˣ) (δ' : GL (Fin 2) TT) :
    AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) ∈
      AutomorphicForm.twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ' := by
  rw [AutomorphicForm.twistedCentralizer, mem_sigmaCentralizer_iff, sigmaGL_toTensorGL, toTensorGL_scalar_comm]
  group

theorem det_toTensorGL_scalar (a : ℝˣ) :
    Matrix.det ((AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) a) : GL (Fin 2) TT) :
      Matrix (Fin 2) (Fin 2) TT) = ((1 : ℂ) ⊗ₜ[ℝ] ((a : ℝ) ^ 2) : TT) := by
  rw [Matrix.det_fin_two, toTensorGL_apply, toTensorGL_apply, toTensorGL_apply, toTensorGL_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), TensorProduct.tmul_zero, mul_zero, sub_zero,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, sq]

def Shell (c : ℝ) : Set (ℂ × ℂ) := {p | ‖p.1‖ ^ 2 - c * ‖p.2‖ ^ 2 ∈ Set.Icc (1 : ℝ) (Real.exp 2)}

theorem isCompact_Shell (c : ℝ) (hc : c < 0) : IsCompact (Shell c) := by
  haveI : ProperSpace (ℂ × ℂ) := inferInstance
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_Icc.preimage (by fun_prop)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := max (Real.exp 1) (Real.sqrt (Real.exp 2 / -c)))).subset ?_
    intro p hp
    simp only [Shell, Set.mem_setOf_eq, Set.mem_Icc] at hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    have hc' : 0 < -c := by linarith
    have ha : ‖p.1‖ ^ 2 ≤ Real.exp 2 := by nlinarith [norm_nonneg p.2, sq_nonneg ‖p.2‖, hp.2]
    have he : ‖p.2‖ ^ 2 ≤ Real.exp 2 / -c := by
      rw [div_eq_mul_inv, le_mul_inv_iff₀ hc']
      nlinarith [sq_nonneg ‖p.1‖, hp.2]
    constructor
    · refine le_trans ?_ (le_max_left _ _)
      rw [← Real.sqrt_sq (norm_nonneg p.1), show Real.exp 1 = Real.sqrt (Real.exp 2) by
        rw [show Real.exp 2 = Real.exp 1 ^ 2 by rw [← Real.exp_nat_mul]; norm_num, Real.sqrt_sq (Real.exp_pos 1).le]]
      exact Real.sqrt_le_sqrt ha
    · refine le_trans ?_ (le_max_right _ _)
      rw [← Real.sqrt_sq (norm_nonneg p.2)]
      exact Real.sqrt_le_sqrt he

def qG (c : ℝ) (hc : c < 0) (p : Shell c) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (qM c p.1) (by
    rw [det_qM]
    have hp : ‖(p.1).1‖ ^ 2 - c * ‖(p.1).2‖ ^ 2 ∈ Set.Icc (1 : ℝ) (Real.exp 2) := p.2
    exact_mod_cast (lt_of_lt_of_le one_pos hp.1).ne')

theorem qG_val (c : ℝ) (hc : c < 0) (p : Shell c) : ((qG c hc p : GL (Fin 2) ℂ) : M2) = qM c p.1 := rfl

theorem continuous_qG (c : ℝ) (hc : c < 0) : Continuous (qG c hc) := by
  have hdet : ∀ p : Shell c, Matrix.det (qM c p.1) ≠ 0 := fun p => by
    rw [det_qM]
    have hp : ‖(p.1).1‖ ^ 2 - c * ‖(p.1).2‖ ^ 2 ∈ Set.Icc (1 : ℝ) (Real.exp 2) := p.2
    exact_mod_cast (lt_of_lt_of_le one_pos hp.1).ne'
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_qM c).comp continuous_subtype_val).congr fun p => rfl
  · have e : (fun p : Shell c => (((qG c hc p)⁻¹ : GL (Fin 2) ℂ) : M2)) =
        fun p => (Matrix.det (qM c p.1))⁻¹ • (qM c p.1).adjugate := by
      funext p
      rw [Matrix.coe_units_inv, qG_val, Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    exact (((continuous_qM c).comp continuous_subtype_val).matrix_det.inv₀ hdet).smul
      (((continuous_qM c).comp continuous_subtype_val).matrix_adjugate)

end KappaEval

end

open ProperUnifCore ProperUnifBridge QuatCore KappaEval in
theorem solution
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (κ : ℝ) (hκ0 : 0 < κ)
    (hκ : ∀ w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ,
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
           twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
       (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
         ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
           ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
             w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ :
               ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1) →
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       ∫ t, w t ∂τ' = κ))
    (hpos : 0 < τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)})
    (hfin : τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} < ⊤) :
    ENNReal.ofReal κ * τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} =
      τ' {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} := by
  classical

  letI mD : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  letI mS : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
  haveI : BorelSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := ⟨rfl⟩
  haveI := AutomorphicForm.isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := AutomorphicForm.t2Space_tensorGL ℝ ℂ ℝ
  haveI : Measure.IsHaarMeasure τ' := hτ'
  haveI : Measure.IsHaarMeasure τS := hτS
  set K : Set ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} with hK
  set B : Set ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} with hB

  have hN : AutomorphicForm.normString ℝ ℂ ℝ Complex.conjAe δ = δ * AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
    rw [AutomorphicForm.normString, Complex.finrank_real_complex]
    simp [List.range_succ, Function.iterate_zero]
  have hδ' : δ * AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe δ =
      y * AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y⁻¹ := by
    rw [AutomorphicForm.IsNormConjugator, hN] at hδ
    rw [hδ]; group
  set D : GL (Fin 2) ℂ := ρ δ with hDdef
  have hD : ((D * cjGL D : GL (Fin 2) ℂ) : M2) = ((c : ℝ) : ℂ) • (1 : M2) := by
    have hcomm := ι_scalar_comm c (ρ y)
    have e1 : D * cjGL D = ι (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
      rw [hDdef, ← ρ_sigmaGL, ← map_mul, hδ', map_mul, map_mul, map_inv, ρ_toTensorGL, ← hcomm]
      group
    rw [e1, ι_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have htw : ∀ t : GL (Fin 2) TT, t ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ↔ TwRel D (ρ t) := by
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

  have hdetconj : ∀ g z : GL (Fin 2) ℂ, Matrix.det (((z⁻¹ * g * z : GL (Fin 2) ℂ)) : M2) = Matrix.det ((g : GL (Fin 2) ℂ) : M2) := by
    intro g z
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

  have hdetpos : ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ), ∃ ν : ℝ, 0 < ν ∧
      Matrix.det (((t : GL (Fin 2) TT)) : Matrix (Fin 2) (Fin 2) TT) = ((1 : ℂ) ⊗ₜ[ℝ] ν : TT) := by
    intro t
    have ht : TwRel D (ρ (t : GL (Fin 2) TT)) := (htw _).1 t.2
    set s := (xD (c : ℝ) hc D hD)⁻¹ * ρ (t : GL (Fin 2) TT) * xD (c : ℝ) hc D hD with hs
    have hs' : TwRel (D0 (c : ℝ) hc.ne) s := (twRel_iff_conj (c : ℝ) hc D hD _).1 ht
    refine ⟨_, det_pos_of_twRel_D0 (c : ℝ) hc s hs', ?_⟩
    apply ρr.injective
    rw [ρr_one_tmul, ← det_of_twRel_D0 (c : ℝ) hc.ne s hs', ← det_ρ, hs, hdetconj]

  have hσc : Continuous (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe : GL (Fin 2) TT → GL (Fin 2) TT) := by
    have e : (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe : GL (Fin 2) TT → GL (Fin 2) TT) =
        fun t => ρi (cjGL (ρ t)) := by
      funext t
      rw [← ρ_sigmaGL, ρi_ρ]
    rw [e]
    exact continuous_ρi.comp (continuous_cjGL.comp continuous_ρ)
  have hTdc : IsClosed ((twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) : Set (GL (Fin 2) TT)) := by
    have e : ((twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) : Set (GL (Fin 2) TT)) = {t | t * δ * (AutomorphicForm.sigmaGL ℝ ℂ ℝ Complex.conjAe t)⁻¹ = δ} := by
      ext t; exact mem_sigmaCentralizer_iff
    rw [e]
    exact isClosed_eq ((continuous_id.mul continuous_const).mul (hσc.inv)) continuous_const

  have hdetc : Continuous fun g : GL (Fin 2) TT => ρr (Matrix.det ((g : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT)) :=
    continuous_ρr.comp (Units.continuous_val.matrix_det)
  set E : Set (GL (Fin 2) TT) := {g | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
    Matrix.det ((g : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} with hE
  have hEeq : E = (fun g : GL (Fin 2) TT => ρr (Matrix.det ((g : GL (Fin 2) TT) : Matrix (Fin 2) (Fin 2) TT))) ⁻¹'
      {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 : ℝ) (Real.exp 2)} := by
    ext g; exact band_iff _
  have hEc : IsClosed E := by rw [hEeq]; exact isClosed_bandC.preimage hdetc
  have hKE : K = (Subtype.val : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → GL (Fin 2) TT) ⁻¹' E := by
    ext t; exact Iff.rfl
  have hBE : B = (Subtype.val : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) → GL (Fin 2) TT) ⁻¹' E := by
    ext t; exact Iff.rfl
  have hKm : MeasurableSet K := by rw [hKE]; exact (hEc.preimage continuous_subtype_val).measurableSet
  have hBm : MeasurableSet B := by rw [hBE]; exact (hEc.preimage continuous_subtype_val).measurableSet

  have hKc : IsCompact K := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, hKE, Set.image_preimage_eq_inter_range, Subtype.range_coe]
    set x := xD (c : ℝ) hc D hD with hx
    haveI : CompactSpace (Shell (c : ℝ)) := isCompact_iff_compactSpace.1 (isCompact_Shell (c : ℝ) hc)
    set F : Shell (c : ℝ) → GL (Fin 2) TT := fun p => ρi (x * qG (c : ℝ) hc p * x⁻¹) with hF
    have hFc : Continuous F := continuous_ρi.comp ((continuous_const.mul (continuous_qG (c : ℝ) hc)).mul continuous_const)
    refine (isCompact_range hFc).of_isClosed_subset (hEc.inter hTdc) ?_
    rintro g ⟨⟨d, hd, hgd⟩, hgT⟩
    have ht : TwRel D (ρ g) := (htw g).1 hgT
    set s := x⁻¹ * ρ g * x with hs
    have hs' : TwRel (D0 (c : ℝ) hc.ne) s := by rw [hs, hx]; exact (twRel_iff_conj (c : ℝ) hc D hD _).1 ht
    obtain ⟨h01, h11⟩ := entries_of_twRel_D0 (c : ℝ) hc.ne s hs'
    have hdet_s : Matrix.det ((s : GL (Fin 2) ℂ) : M2) = (d : ℂ) := by
      rw [hs, hdetconj, det_ρ, hgd, ρr_one_tmul]
    have hp : (((s : GL (Fin 2) ℂ) : M2) 0 0, ((s : GL (Fin 2) ℂ) : M2) 1 0) ∈ Shell (c : ℝ) := by
      show ‖((s : GL (Fin 2) ℂ) : M2) 0 0‖ ^ 2 - (c : ℝ) * ‖((s : GL (Fin 2) ℂ) : M2) 1 0‖ ^ 2 ∈ Set.Icc (1 : ℝ) (Real.exp 2)
      have := det_of_twRel_D0 (c : ℝ) hc.ne s hs'
      rw [hdet_s, Complex.ofReal_inj] at this
      rw [← this]; exact hd
    refine ⟨⟨_, hp⟩, ?_⟩
    have hsq : qG (c : ℝ) hc ⟨_, hp⟩ = s := by
      refine Units.ext ?_
      rw [qG_val]
      show qM (c : ℝ) (((s : GL (Fin 2) ℂ) : M2) 0 0, ((s : GL (Fin 2) ℂ) : M2) 1 0) = ((s : GL (Fin 2) ℂ) : M2)
      rw [qM]
      conv_rhs => rw [Matrix.eta_fin_two ((s : GL (Fin 2) ℂ) : M2), h01, h11]
    show ρi (x * qG (c : ℝ) hc ⟨_, hp⟩ * x⁻¹) = g
    rw [hsq, hs, show x * (x⁻¹ * ρ g * x) * x⁻¹ = ρ g by group, ρi_ρ]
  have hKfin : τ' K < ⊤ := hKc.measure_lt_top

  set b : ℝ := (τS B).toReal with hb
  have hbpos : 0 < b := ENNReal.toReal_pos hpos.ne' hfin.ne
  set w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ := K.indicator (fun _ => b⁻¹) with hw
  have hw_nonneg : ∀ t, 0 ≤ w t := fun t =>
    Set.indicator_nonneg (fun _ _ => inv_nonneg.2 hbpos.le) t
  have hw_meas : Measurable w := measurable_const.indicator hKm
  have hw_supp : HasCompactSupport w :=
    HasCompactSupport.intro hKc (fun t ht => Set.indicator_of_notMem ht _)
  have hw_fibre : ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
      ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
        w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1 := by
    intro t
    obtain ⟨ν, hν, hdt⟩ := hdetpos t
    set r : ℝ := Real.sqrt ν with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 hν
    have hr2 : r ^ 2 = ν := Real.sq_sqrt hν.le
    set R : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) :=
      ⟨AutomorphicForm.toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hrpos.ne')),
        Subgroup.mem_inf.2 ⟨toTensorGL_scalar_mem _ _, toTensorGL_scalar_mem _ _⟩⟩ with hR
    have hmem : ∀ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
        ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∈ K ↔ R * s ∈ B := by
      intro s
      rw [hKE, hBE, Set.mem_preimage, Set.mem_preimage]
      show (∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
          Matrix.det ((((s : GL (Fin 2) TT) * (t : GL (Fin 2) TT) : GL (Fin 2) TT)) : Matrix (Fin 2) (Fin 2) TT) =
            ((1 : ℂ) ⊗ₜ[ℝ] d : TT)) ↔
        (∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
          Matrix.det ((((R : GL (Fin 2) TT) * (s : GL (Fin 2) TT) : GL (Fin 2) TT)) : Matrix (Fin 2) (Fin 2) TT) =
            ((1 : ℂ) ⊗ₜ[ℝ] d : TT))
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdt, hR]
      simp only [det_toTensorGL_scalar, Units.val_mk0, hr2]
      rw [mul_comm]
    have hA : (fun s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) =>
        w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t)) =
        ((fun s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) => R * s) ⁻¹' B).indicator (fun _ => b⁻¹) := by
      funext s
      simp only [hw, Set.indicator_apply, Set.mem_preimage]
      rw [if_congr (hmem s) rfl rfl]
    have hRm : Measurable (fun s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) => R * s) := (continuous_const.mul continuous_id).measurable
    rw [hA, integral_indicator_const _ (hBm.preimage hRm)]
    have hinv : τS ((fun s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) => R * s) ⁻¹' B) = τS B := by
      rw [← Measure.map_apply hRm hBm, Measure.IsMulLeftInvariant.map_mul_left_eq_self]
    rw [measureReal_def, hinv, smul_eq_mul, ← hb, mul_inv_cancel₀ hbpos.ne']
  have hint := hκ w ⟨hw_nonneg, hw_meas, hw_supp, hw_fibre⟩
  rw [hw, integral_indicator_const _ hKm, measureReal_def, smul_eq_mul] at hint

  rw [← hint]
  calc ENNReal.ofReal ((τ' K).toReal * b⁻¹) * τS B
      = ENNReal.ofReal ((τ' K).toReal * b⁻¹) * ENNReal.ofReal b := by rw [hb, ENNReal.ofReal_toReal hfin.ne]
    _ = ENNReal.ofReal ((τ' K).toReal * b⁻¹ * b) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.2 hbpos.le))]
    _ = ENNReal.ofReal ((τ' K).toReal) := by rw [mul_assoc, inv_mul_cancel₀ hbpos.ne', mul_one]
    _ = τ' K := ENNReal.ofReal_toReal hKfin.ne

end S_AutomorphicForm_ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst
end P2MW
export P2MW.S_AutomorphicForm_ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst (solution)
