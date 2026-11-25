-- Prove2me | solution 1 for Arxiv1904_10695.reference_amplitude_from_tm
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:05:26.189174+00:00
-- url     : https://prove2.me/submissions/8539b3ea-28d0-44a3-8d57-8f5af2240843

import Mathlib
import Definitions.Def_Arxiv1904_10695_Basic

open Arxiv1904_10695

lemma ampAvg_obs {M N : ℕ} (t : TransmissionMatrix M N) (Eref : Fin N → ℂ) (n : Fin N) :
    ampAvg (obsTM t Eref) n = ampAvg t n * ‖Eref n‖ := by
  simp only [ampAvg, inputAvg, obsTM, norm_mul, ← Finset.sum_mul]
  ring

lemma ampAvg_pos {M N : ℕ} (hM : 0 < M) (t : TransmissionMatrix M N) (m : Fin M) (n : Fin N)
    (h : t m n ≠ 0) : 0 < ampAvg t n := by
  unfold ampAvg inputAvg
  apply div_pos _ (by exact_mod_cast hM)
  calc (0 : ℝ) < ‖t m n‖ := norm_pos_iff.mpr h
    _ ≤ ∑ m', ‖t m' n‖ :=
        Finset.single_le_sum (f := fun m' => ‖t m' n‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ m)

theorem solution {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (t : TransmissionMatrix M N) (Eref : Fin N → ℂ) :
    (∀ n, ampAvg (obsTM t Eref) n = ampAvg t n * ‖Eref n‖) ∧
    ((∀ n n', ampAvg t n = ampAvg t n') → t ≠ 0 → Eref ≠ 0 →
      (∃ c : ℝ, 0 < c ∧ ∀ n, ampAvg (obsTM t Eref) n = c * ‖Eref n‖) ∧
      (∀ n, normalizeByMax (ampAvg (obsTM t Eref)) n =
        normalizeByMax (fun n' => ‖Eref n'‖) n)) := by
  refine ⟨ampAvg_obs t Eref, fun hconst ht _ => ?_⟩
  obtain ⟨m0, n0, h0⟩ : ∃ m n, t m n ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ht (funext fun m => funext fun n => hc m n)
  set c := ampAvg t n0
  have hc : 0 < c := ampAvg_pos hM t m0 n0 h0
  have hform : ∀ n, ampAvg (obsTM t Eref) n = c * ‖Eref n‖ := fun n => by
    rw [ampAvg_obs, hconst n n0]
  refine ⟨⟨c, hc, hform⟩, fun n => ?_⟩
  unfold normalizeByMax
  have hfun : ampAvg (obsTM t Eref) = fun n => c * ‖Eref n‖ := funext hform
  rw [hfun, ← Real.mul_iSup_of_nonneg hc.le, mul_div_mul_left _ _ hc.ne']

