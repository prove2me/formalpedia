-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:27:27.23448+00:00
-- url     : https://prove2.me/theorems/67998acf-9c56-4adb-a061-090f18b6f973
-- title:
--   Orbit Push Q
-- statement:
--   Definitions and structural lemmas for Orbit Push Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushQ.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W
open PI.RhsWLim
@[simp] theorem wlp_fst_toLp {α β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (a : α × β) :
    (WithLp.toLp 2 a).fst = a.1 := rfl
@[simp] theorem wlp_snd_toLp {α β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] (a : α × β) :
    (WithLp.toLp 2 a).snd = a.2 := rfl
theorem wlp_ext {α β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β] {p q : WithLp 2 (α × β)}
    (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  cases p
  cases q
  congr 1
  exact Prod.ext h1 h2
def qFw (k : ℕ) (x : TrE k) : WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun a => ((x (some (a, false)) : ℂ) + (x (some (a, true)) : ℂ) * Complex.I)),
    x none)
def qBw (k : ℕ) (p : WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ)) : TrE k :=
  WithLp.toLp 2 (fun o => match o with
    | none => p.snd
    | some (a, b) => if b then (p.fst a).im else (p.fst a).re)
theorem qBw_qFw (k : ℕ) (x : TrE k) : qBw k (qFw k x) = x := by
  ext o
  rcases o with _ | ⟨a, _ | _⟩ <;> simp [qBw, qFw]
theorem qFw_qBw (k : ℕ) (p : WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ)) : qFw k (qBw k p) = p := by
  refine wlp_ext ?_ ?_
  · ext a
    apply Complex.ext <;> simp [qFw, qBw]
  · simp [qFw, qBw]
theorem qFw_norm_sq (k : ℕ) (x : TrE k) : ‖qFw k x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [qFw, wlp_fst_toLp, wlp_snd_toLp]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [PiLp.toLp_apply, Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs,
    sq_abs, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring
def qIso (k : ℕ) : TrE k ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℂ (Fin k) × ℝ) where
  toFun := qFw k
  invFun := qBw k
  map_add' x y := by
    refine wlp_ext ?_ ?_
    · ext a
      apply Complex.ext <;> simp [qFw]
    · simp [qFw]
  map_smul' c x := by
    refine wlp_ext ?_ ?_
    · ext a
      apply Complex.ext <;> simp [qFw]
    · simp [qFw]
  left_inv := qBw_qFw k
  right_inv := qFw_qBw k
  norm_map' x := by
    have h := qFw_norm_sq k x
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
end PI.RhsWLim.W


