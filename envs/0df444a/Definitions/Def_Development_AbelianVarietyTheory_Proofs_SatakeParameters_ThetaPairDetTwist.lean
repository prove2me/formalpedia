-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:24.326195+00:00
-- url     : https://prove2.me/theorems/85f139ff-b340-4e4f-97ae-d3e68985c2c9
-- title:
--   Theta Pair Det Twist
-- statement:
--   Definitions and structural lemmas for Theta Pair Det Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ThetaPairDetTwist.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviEmb
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
import Theorems.Thm_GlobalTheory_SmGL_det_parab
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two
import Theorems.Thm_GlobalTheory_SmGL_val_absPow_ofReal
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_isSmoothRepresentation
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
import Theorems.Thm_GlobalTheory_T_hermitian_norm_sq_le_re_mul_re_of_posDef
import Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology
namespace GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
local notation "e₀" => stdSum (rfl : _ + _ = _ + _)
section Mat
variable {α β : Type} [Fintype α]
open MeasureTheory ValuativeRel in
open scoped TensorProduct Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] in

theorem _root_.GlobalTheory.GodementJacquet.parab_mul_eMat
    (p : _root_.GlobalTheory.SmGL.parab k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t)))) :
    (p : GL (Fin (r + t)) k).val * _root_.GlobalTheory.GodementJacquet.eMat k r t =
      _root_.GlobalTheory.GodementJacquet.eMat k r t * (_root_.GlobalTheory.SmGL.leviProj k
        (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
          GL (Fin r) k).val := by
  have hE : ∀ (i : Fin (r + t)) (j : Fin r),
      _root_.GlobalTheory.GodementJacquet.eMat k r t i j = if i = Fin.castAdd t j then 1 else 0 := by
    intro i j
    simp [_root_.GlobalTheory.GodementJacquet.eMat, Fin.ext_iff]
  have hlow : ∀ (i : Fin t) (j : Fin r),
      (p : GL (Fin (r + t)) k).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
    intro i j
    have := (_root_.GlobalTheory.SmGL.mem_parab_two k).1 p.2 i j
    simpa [_root_.GlobalTheory.SmGL.stdSum] using this
  have hL : ∀ (i j : Fin r), (_root_.GlobalTheory.SmGL.leviProj k
      (_root_.GlobalTheory.SmGL.two (_root_.GlobalTheory.SmGL.stdSum (rfl : r + t = r + t))) p false :
        GL (Fin r) k).val i j = (p : GL (Fin (r + t)) k).val (Fin.castAdd t i) (Fin.castAdd t j) := by
    intro i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply]
    rfl
  ext i j
  simp only [Matrix.mul_apply, hE, hL, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [eq_comm]
  · rw [hlow]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    rw [if_neg]
    simp only [Fin.ext_iff, Fin.coe_natAdd, Fin.coe_castAdd]
    omega
end Mat
section Coef
variable {σ : Representation ℂ (GL (Fin r) k) V} {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
theorem fix_inv {g : GL (Fin r) k} {v : V} (h : σ g v = v) : σ g⁻¹ v = v := by
  conv_lhs => rw [← h]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
theorem continuous_coef (hσ : IsSmooth σ) (v w : V) : Continuous (coef σ Bf v w) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_)
  have hc : Continuous fun g : GL (Fin r) k => g * g₀⁻¹ := continuous_mul_right _
  have h1 : {g : GL (Fin r) k | σ g v = v} ∈ 𝓝 ((fun g : GL (Fin r) k => g * g₀⁻¹) g₀) :=
    (hσ v).mem_nhds (by simp)
  filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with g hg
  have hg' : σ (g * g₀⁻¹) v = v := hg
  have h2 : g⁻¹ = g₀⁻¹ * (g * g₀⁻¹)⁻¹ := by group
  simp only [coef]
  rw [h2, map_mul, Module.End.mul_apply, fix_inv hg']
theorem norm_coef_le (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (v w : V) (g : GL (Fin r) k) :
    ‖coef σ Bf v w g‖ ≤ √((Bf v v).re * (Bf w w).re) := by
  have h := GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef V Bf hs hp (σ g⁻¹ v) w
  rw [hu] at h
  exact Real.le_sqrt_of_sq_le h
end Coef
section Law
theorem rpow_identity {a d g h : ℝ} (ha : 0 < a) (hd : 0 < d) (hg : 0 < g) (hh : 0 < h) (r t : ℝ) :
    (a * g) ^ ((r + t) / 2) * (a * d * h) ^ (-r / 2) =
      a ^ (t / 2) * d ^ (-r / 2) * (g ^ ((r + t) / 2) * h ^ (-r / 2)) := by
  rw [Real.mul_rpow ha.le hg.le, Real.mul_rpow (mul_pos ha hd).le hh.le, Real.mul_rpow ha.le hd.le]
  have : a ^ ((r + t) / 2) * a ^ (-r / 2) = a ^ (t / 2) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  rw [← this]
  ring
theorem om_parab (μ : kˣ →* ℂˣ) (p : parab k (two (stdSum (rfl : r + t = r + t))))
    (g : GL (Fin r) k) (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) :
    om μ ((leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k) * g)
        ((p : GL (Fin (r + t)) k) * h) Φ (eMat k r t) =
      (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
        ((μ (Matrix.GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : r + t = r + t))) p true : GL (Fin t) k)))⁻¹ : ℂˣ) *
        om μ g h Φ (eMat k r t) := by
  set a : GL (Fin r) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p false with ha
  set d : GL (Fin t) k := leviProj k (two (stdSum (rfl : r + t = r + t))) p true with hd
  have hl : leviProj k (two (stdSum (rfl : r + t = r + t))) p = leviTwo k (Fin r) (Fin t) (a, d) := by
    funext x
    cases x <;> rfl
  have hdet : Matrix.GeneralLinearGroup.det (p : GL (Fin (r + t)) k) =
      Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det d := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
  have hx : (((p : GL (Fin (r + t)) k) * h)⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * (a * g).val =
      (h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val := by
    have h1 := parab_mul_eMat p
    have h2 : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * a.val = eMat k r t := by
      rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h3 : ((p : GL (Fin (r + t)) k)⁻¹ : GL (Fin (r + t)) k).val * (eMat k r t * a.val * g.val) =
        eMat k r t * g.val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
    rw [mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (eMat k r t),
      h3, Matrix.mul_assoc]
  have hR := rpow_identity (nabs_pos' k (Matrix.GeneralLinearGroup.det a))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det d)) (nabs_pos' k (Matrix.GeneralLinearGroup.det g))
    (nabs_pos' k (Matrix.GeneralLinearGroup.det h)) (r : ℝ) (t : ℝ)
  have hR' := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [Complex.ofReal_mul] at hR'
  have hn : (μ (Matrix.GeneralLinearGroup.det a) : ℂ) ≠ 0 := Units.ne_zero _
  have hn2 : (μ (Matrix.GeneralLinearGroup.det d) : ℂ) ≠ 0 := Units.ne_zero _
  have hn3 : (μ (Matrix.GeneralLinearGroup.det h) : ℂ) ≠ 0 := Units.ne_zero _
  rw [hl, deltaHalf_two]
  simp only [om]
  rw [hx]
  have e1 : (absPow k ((t : ℂ) / 2) (Matrix.GeneralLinearGroup.det a) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det a) ^ ((t : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  have e2 : (absPow k (-(r : ℂ) / 2) (Matrix.GeneralLinearGroup.det d) : ℂ) =
      ((nabs k (Matrix.GeneralLinearGroup.det d) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show (-(r : ℂ) / 2) = ((-(r : ℝ) / 2 : ℝ) : ℂ) by simp]
    exact val_absPow_ofReal k _ _
  simp only [map_mul, hdet, nabs_mul', Units.val_mul, e1, e2, Fintype.card_fin, Nat.cast_add,
    Units.val_inv_eq_inv_val, mul_inv]
  have hinv := mul_inv_cancel₀ hn
  generalize (μ (Matrix.GeneralLinearGroup.det a) : ℂ) = a' at *
  generalize (μ (Matrix.GeneralLinearGroup.det d) : ℂ) = d' at *
  generalize (μ (Matrix.GeneralLinearGroup.det h) : ℂ) = h' at *
  generalize (μ (Matrix.GeneralLinearGroup.det g) : ℂ) = g' at *
  generalize Φ ((h⁻¹ : GL (Fin (r + t)) k).val * eMat k r t * g.val) = y at *
  generalize ((((nabs k (Matrix.GeneralLinearGroup.det a) * nabs k (Matrix.GeneralLinearGroup.det g)) ^ (((r : ℝ) + (t : ℝ)) / 2)) : ℝ) : ℂ) = x1 at *
  generalize ((((nabs k (Matrix.GeneralLinearGroup.det a) * nabs k (Matrix.GeneralLinearGroup.det d) *
            nabs k (Matrix.GeneralLinearGroup.det h)) ^ (-(r : ℝ) / 2)) : ℝ) : ℂ) = x2 at *
  linear_combination (g' * d'⁻¹ * h'⁻¹ * y * x1 * x2) * hinv + (g' * d'⁻¹ * h'⁻¹ * y) * hR'
end Law
section Int
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
theorem integrable_mul_coef (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    {f : GL (Fin r) k → ℂ} (hf : Integrable f m) (v w : V) :
    Integrable (fun g => f g * coef σ Bf v w g) m :=
  hf.mul_bdd (c := √((Bf v v).re * (Bf w w).re)) (continuous_coef hσ v w).aestronglyMeasurable
    (ae_of_all _ (norm_coef_le hs hp hu v w))
variable (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
include hσ hs hp hu
theorem gjInt_add_left {Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ} {h : GL (Fin (r + t)) k}
    (hf : Integrable (fun g => om μ g h Φ (eMat k r t)) m) (v v' w : V) :
    gjInt m μ σ Bf Φ h (v + v') w = gjInt m μ σ Bf Φ h v w + gjInt m μ σ Bf Φ h v' w := by
  simp only [gjInt]
  rw [← integral_add (integrable_mul_coef hσ hs hp hu hf _ _) (integrable_mul_coef hσ hs hp hu hf _ _)]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp [coef, mul_add]
omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem gjInt_smul_left (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (c : ℂ) (v w : V) :
    gjInt m μ σ Bf Φ h (c • v) w = c * gjInt m μ σ Bf Φ h v w := by
  simp only [gjInt]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [coef, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring
omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in

theorem gjInt_translate (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h h₀ : GL (Fin (r + t)) k) (v w : V) :
    gjInt m μ σ Bf (om μ 1 h₀ Φ) h v w = gjInt m μ σ Bf Φ (h * h₀) v w := by
  simp only [gjInt]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have := om_mul μ g 1 h h₀ Φ
  rw [mul_one] at this
  simp only [this]
end Int
section Family
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
theorem gjInt_law [m.IsMulLeftInvariant] (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ)
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (h : GL (Fin (r + t)) k) (v w : V) :
    gjInt m μ σ Bf Φ ((p : GL (Fin (r + t)) k) * h) v w =
      (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
        ((μ (Matrix.GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : r + t = r + t))) p true : GL (Fin t) k)))⁻¹ : ℂˣ) *
        gjInt m μ σ Bf Φ h
          (σ (leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k)⁻¹ v) w := by
  simp only [gjInt]
  rw [← integral_mul_left_eq_self (μ := m)
    (fun x => om μ x ((p : GL (Fin (r + t)) k) * h) Φ (eMat k r t) * coef σ Bf v w x)
    (leviProj k (two (stdSum (rfl : r + t = r + t))) p false : GL (Fin r) k), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have h1 := om_parab μ p g h Φ
  simp only [coef]
  rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  refine (congrArg (· * _) h1).trans ?_
  ring
omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem rid_leviRep (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V)
    (g : Levi k (Two (Fin r) (Fin t))) (x : V ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ V (leviRep t μ σ g x) =
      (μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) •
        σ (g false : GL (Fin r) k) (TensorProduct.rid ℂ V x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul v z =>
    show TensorProduct.rid ℂ V (extTensor σ (detRep (Fin t) μ) ((leviTwo k (Fin r) (Fin t)).symm g) (v ⊗ₜ z)) = _
    rw [extTensor_tmul]
    simp [leviTwo, detRep, smul_smul]
variable [m.IsMulLeftInvariant] (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
      Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
def rawF (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (h : GL (Fin (r + t)) k) (w : V) :
    Module.Dual ℂ (V ⊗[ℂ] ℂ) :=
  ({ toFun := fun v => gjInt m μ σ Bf Φ.1 h v w
     map_add' := fun v v' => gjInt_add_left hσ hs hp hu (hI h Φ.1 Φ.2) v v' w
     map_smul' := fun c v => gjInt_smul_left _ _ c v w } : V →ₗ[ℂ] ℂ) ∘ₗ
    (TensorProduct.rid ℂ V).toLinearMap
theorem rawF_apply (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (h : GL (Fin (r + t)) k) (w : V)
    (x : V ⊗[ℂ] ℂ) :
    rawF hσ hs hp hu hI Φ h w x = gjInt m μ σ Bf Φ.1 h (TensorProduct.rid ℂ V x) w := rfl
theorem rawF_law (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (h : GL (Fin (r + t)) k) (w : V) :
    rawF hσ hs hp hu hI Φ ((p : GL (Fin (r + t)) k) * h) w =
      (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) •
        (leviRep t μ σ).dual (leviProj k (two (stdSum (rfl : r + t = r + t))) p)
          (rawF hσ hs hp hu hI Φ h w) := by
  refine LinearMap.ext fun x => ?_
  show rawF hσ hs hp hu hI Φ ((p : GL (Fin (r + t)) k) * h) w x =
    (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (two (stdSum (rfl : r + t = r + t))) p) : ℂ) *
      rawF hσ hs hp hu hI Φ h w
        (leviRep t μ σ (leviProj k (two (stdSum (rfl : r + t = r + t))) p)⁻¹ x)
  rw [rawF_apply, rawF_apply, rid_leviRep, gjInt_law, gjInt_smul_left]
  simp only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val]
  ring
theorem rawF_translate (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (h h₀ : GL (Fin (r + t)) k) (w : V)
    (h₁ : om μ 1 h₀ Φ.1 = Φ.1) :
    rawF hσ hs hp hu hI Φ (h * h₀) w = rawF hσ hs hp hu hI Φ h w := by
  refine LinearMap.ext fun x => ?_
  rw [rawF_apply, rawF_apply, ← gjInt_translate, h₁]
omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)] in
theorem eventually_stab (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) :
    ∀ᶠ h₀ : GL (Fin (r + t)) k in 𝓝 1, om μ 1 h₀ Φ.1 = Φ.1 := by
  have h := (om_isSmoothRepresentation k (Fin r) (Fin (r + t)) μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun h₀ : GL (Fin (r + t)) k => ((1 : GL (Fin r) k), h₀) :=
    continuous_const.prodMk continuous_id
  exact (h.preimage hc).mem_nhds (om_one μ Φ.1)
theorem rawF_mem (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (h : GL (Fin (r + t)) k) (w : V) :
    rawF hσ hs hp hu hI Φ h w ∈ smoothPart (leviRep t μ σ).dual := by
  refine mem_smoothPart_of_nhds ?_
  have hc : Continuous fun g : Levi k (Two (Fin r) (Fin t)) =>
      h⁻¹ * leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h :=
    (continuous_const.mul (continuous_leviEmb k _)).mul continuous_const
  have h1 : ∀ᶠ g : Levi k (Two (Fin r) (Fin t)) in 𝓝 1,
      om μ 1 (h⁻¹ * leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h) Φ.1 = Φ.1 :=
    (hc.tendsto' 1 1 (by simp)).eventually (eventually_stab hμ Φ)
  have h2 : ∀ᶠ g : Levi k (Two (Fin r) (Fin t)) in 𝓝 1, deltaHalf k (Two (Fin r) (Fin t)) g = 1 :=
    (isSmoothChar_deltaHalf k).mem_nhds (one_mem _)
  filter_upwards [h1, h2] with g hg hd
  have law := rawF_law hσ hs hp hu hI Φ ⟨_, leviEmb_mem_parab k _ g⟩ h w
  rw [leviProj_leviEmb, hd, Units.val_one, one_smul] at law
  have tr := rawF_translate hσ hs hp hu hI Φ h _ w hg
  rw [show h * (h⁻¹ * leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h) =
    leviEmb k (two (stdSum (rfl : r + t = r + t))) g * h by group] at tr
  exact law.symm.trans tr
def famF (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) (w : V) :
    IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ)) :=
  ⟨⟨fun h => ⟨rawF hσ hs hp hu hI Φ h w, rawF_mem hσ hs hp hu hI hμ Φ h w⟩,
    fun p g => Subtype.ext (rawF_law hσ hs hp hu hI Φ p g w)⟩,
    mem_smoothPart_of_nhds (by
      filter_upwards [eventually_stab hμ Φ] with g hg
      refine Subtype.ext (funext fun x => Subtype.ext ?_)
      exact rawF_translate hσ hs hp hu hI Φ x g w hg)⟩
end Family
section Abstract
variable {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
end Abstract
section Pairing
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
end Pairing
section NonVanishing
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
  [m.IsMulLeftInvariant] [m.IsOpenPosMeasure] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
end NonVanishing
end GlobalTheory.GodementJacquet


