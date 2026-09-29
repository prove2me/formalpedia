-- Prove2me | Definitions.Def_KServer_prophecy2
-- name    : KServer_prophecy2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T00:26:18.387583+00:00
-- url     : https://prove2.me/theorems/1f290897-1712-4d58-888c-631be45dbf4b
-- title:
--   Interval Doob energy bounded by variance
-- statement:
--   Interval Doob energy bounds for chunk systems. One Doob step increases the conditional second moment by exactly the increment's second moment (the cross term vanishes by the tower property), so the summed second moments of the Doob increments of any function over any depth interval telescope to a difference of conditional second moments. By conditional Jensen at the top end and Cauchy-Schwarz at the bottom end, this interval Doob energy is at most the global second-moment spread E[f^2] - (E f)^2, and hence at most the centred second moment E[(f - c)^2] for any constant c. These are the per-cell workhorses for bounding the coin-phase prophecy energy of the race: the number of partition cells meeting the coin phase is at most kappa + 1, and each cell's energy is bounded by the variance of that cell's tail mass.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- One Doob step increases the conditional second moment by exactly the
increment's second moment. -/
theorem sq_condExp_step (f : C.Ω → ℝ) (h : ℕ) :
    ∑ ω, C.P ω * (C.condExp f (h + 1) ω) ^ 2
      = ∑ ω, C.P ω * (C.condExp f h ω) ^ 2
        + ∑ ω, C.P ω * (C.dinc f h ω) ^ 2 := by
  have h0 := C.expVal_dinc_mul_condExp f h
  unfold ChunkSystemB.expVal at h0
  have h1 : ∀ ω : C.Ω, C.P ω * (C.condExp f (h + 1) ω) ^ 2
      = C.P ω * (C.condExp f h ω) ^ 2 + C.P ω * (C.dinc f h ω) ^ 2
        + 2 * (C.P ω * (C.dinc f h ω * C.condExp f h ω)) := by
    intro ω
    have h2 : C.condExp f (h + 1) ω = C.condExp f h ω + C.dinc f h ω := by
      unfold ChunkSystemB.dinc
      ring
    rw [h2]
    ring
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, h0]
  ring

/-- Jensen: the conditional second moment is at most the second moment. -/
theorem sum_sq_condExp_le (f : C.Ω → ℝ) (h : ℕ) :
    ∑ ω, C.P ω * (C.condExp f h ω) ^ 2 ≤ ∑ ω, C.P ω * f ω ^ 2 := by
  have h1 : ∀ ω : C.Ω, (C.condExp f h ω) ^ 2
      ≤ C.condExp (fun ω' => f ω' ^ 2) h ω := by
    intro ω
    unfold ChunkSystemB.condExp
    set A := C.atom h ω with hA
    have hm : 0 < C.mass A := C.mass_atom_pos h ω
    rw [div_pow, div_le_div_iff₀ (by positivity) hm]
    have hCS : (∑ ω' ∈ A, Real.sqrt (C.P ω')
          * (Real.sqrt (C.P ω') * f ω')) ^ 2
        ≤ (∑ ω' ∈ A, Real.sqrt (C.P ω') ^ 2)
          * ∑ ω' ∈ A, (Real.sqrt (C.P ω') * f ω') ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq A _ _
    have e1 : ∀ ω' ∈ A, Real.sqrt (C.P ω') * (Real.sqrt (C.P ω') * f ω')
        = C.P ω' * f ω' := by
      intro ω' _
      rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt (C.hP ω'))]
    have e2 : ∀ ω' ∈ A, Real.sqrt (C.P ω') ^ 2 = C.P ω' := by
      intro ω' _
      rw [Real.sq_sqrt (le_of_lt (C.hP ω'))]
    have e3 : ∀ ω' ∈ A, (Real.sqrt (C.P ω') * f ω') ^ 2
        = C.P ω' * f ω' ^ 2 := by
      intro ω' _
      rw [mul_pow, Real.sq_sqrt (le_of_lt (C.hP ω'))]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
      Finset.sum_congr rfl e3] at hCS
    have hnn : 0 ≤ ∑ ω' ∈ A, C.P ω' * f ω' ^ 2 :=
      Finset.sum_nonneg fun ω' _ =>
        mul_nonneg (le_of_lt (C.hP ω')) (sq_nonneg _)
    have hCS' : (∑ ω' ∈ A, C.P ω' * f ω') ^ 2
        ≤ C.mass A * ∑ ω' ∈ A, C.P ω' * f ω' ^ 2 := hCS
    nlinarith [hCS', hm, hnn]
  calc ∑ ω, C.P ω * (C.condExp f h ω) ^ 2
      ≤ ∑ ω, C.P ω * C.condExp (fun ω' => f ω' ^ 2) h ω :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (h1 ω) (le_of_lt (C.hP ω))
    _ = ∑ ω, C.P ω * f ω ^ 2 :=
        C.sum_mul_condExp (fun ω' => f ω' ^ 2) h

/-- Cauchy–Schwarz: the squared mean is at most the conditional second
moment at any depth. -/
theorem sq_sum_le_sum_sq_condExp (f : C.Ω → ℝ) (h : ℕ) :
    (∑ ω, C.P ω * f ω) ^ 2 ≤ ∑ ω, C.P ω * (C.condExp f h ω) ^ 2 := by
  have h1 : (∑ ω, C.P ω * C.condExp f h ω) ^ 2
      ≤ (∑ ω, C.P ω) * ∑ ω, C.P ω * (C.condExp f h ω) ^ 2 := by
    have hCS : (∑ ω, Real.sqrt (C.P ω)
          * (Real.sqrt (C.P ω) * C.condExp f h ω)) ^ 2
        ≤ (∑ ω, Real.sqrt (C.P ω) ^ 2)
          * ∑ ω, (Real.sqrt (C.P ω) * C.condExp f h ω) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    have e1 : ∀ ω : C.Ω, Real.sqrt (C.P ω)
        * (Real.sqrt (C.P ω) * C.condExp f h ω)
        = C.P ω * C.condExp f h ω := by
      intro ω
      rw [← mul_assoc, Real.mul_self_sqrt (le_of_lt (C.hP ω))]
    have e2 : ∀ ω : C.Ω, Real.sqrt (C.P ω) ^ 2 = C.P ω := by
      intro ω
      rw [Real.sq_sqrt (le_of_lt (C.hP ω))]
    have e3 : ∀ ω : C.Ω, (Real.sqrt (C.P ω) * C.condExp f h ω) ^ 2
        = C.P ω * (C.condExp f h ω) ^ 2 := by
      intro ω
      rw [mul_pow, Real.sq_sqrt (le_of_lt (C.hP ω))]
    rw [Finset.sum_congr rfl fun ω _ => e1 ω,
      Finset.sum_congr rfl fun ω _ => e2 ω,
      Finset.sum_congr rfl fun ω _ => e3 ω] at hCS
    exact hCS
  rw [C.sum_mul_condExp f h] at h1
  rw [C.hPsum, one_mul] at h1
  exact h1

/-- **Interval Doob energy is at most the variance**: for any function
and any depth interval, the summed second moments of the Doob
increments are bounded by the global second-moment spread. -/
theorem interval_energy_le_var (f : C.Ω → ℝ) (a b : ℕ) :
    ∑ h ∈ Finset.Ico a b, ∑ ω, C.P ω * (C.dinc f h ω) ^ 2
      ≤ (∑ ω, C.P ω * f ω ^ 2) - (∑ ω, C.P ω * f ω) ^ 2 := by
  by_cases hba : b ≤ a
  case pos =>
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have h1 := sq_sum_le_sum_sq_condExp f 0
    have h2 := sum_sq_condExp_le f 0
    linarith
  case neg =>
    have htel : ∀ d : ℕ, ∑ h ∈ Finset.Ico a (a + d),
        ∑ ω, C.P ω * (C.dinc f h ω) ^ 2
        = (∑ ω, C.P ω * (C.condExp f (a + d) ω) ^ 2)
          - ∑ ω, C.P ω * (C.condExp f a ω) ^ 2 := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [show a + (d + 1) = (a + d) + 1 from by omega,
          Finset.sum_Ico_succ_top (by omega), ih,
          sq_condExp_step f (a + d)]
        ring
    have hb : b = a + (b - a) := by omega
    rw [hb, htel (b - a)]
    have h1 := sq_sum_le_sum_sq_condExp f a
    have h2 := sum_sq_condExp_le f (a + (b - a))
    linarith

/-- Variance form: interval Doob energy against a centred second
moment. -/
theorem interval_energy_le_center (f : C.Ω → ℝ) (a b : ℕ) (c : ℝ) :
    ∑ h ∈ Finset.Ico a b, ∑ ω, C.P ω * (C.dinc f h ω) ^ 2
      ≤ ∑ ω, C.P ω * (f ω - c) ^ 2 := by
  have h1 := interval_energy_le_var (C := C) (fun ω => f ω - c) a b
  have h2 : ∀ h : ℕ, ∀ ω : C.Ω,
      C.dinc (fun ω' => f ω' - c) h ω = C.dinc f h ω := by
    intro h ω
    unfold ChunkSystemB.dinc
    rw [C.condExp_sub f (fun _ => c) (h + 1) ω,
      C.condExp_sub f (fun _ => c) h ω, C.condExp_const, C.condExp_const]
    ring
  rw [Finset.sum_congr rfl fun h _ =>
    Finset.sum_congr rfl fun ω _ => by rw [h2 h ω]] at h1
  refine le_trans h1 ?_
  have h3 : (0 : ℝ) ≤ (∑ ω, C.P ω * (f ω - c)) ^ 2 := sq_nonneg _
  linarith

end ChunkSystemB

end KServer


