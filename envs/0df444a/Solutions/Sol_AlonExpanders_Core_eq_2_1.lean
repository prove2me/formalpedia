-- Prove2me | solution 1 for AlonExpanders.Core.eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:17:37.077352+00:00
-- url     : https://prove2.me/submissions/39a0a29d-bc49-47f5-9340-54256ba38d18

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

set_option autoImplicit false

namespace AlonEq21Aux

open Finset

theorem lap_mulVec_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℝ) (v : V) :
    (G.lapMatrix ℝ).mulVec f v = ∑ w, (if G.Adj v w then (f v - f w) else 0) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  have h1 : ∑ w, (if G.Adj v w then (f v - f w) else 0)
      = ∑ w ∈ G.neighborFinset v, (f v - f w) := by
    rw [← Finset.sum_filter]
    congr 1
    ext w; simp
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul]

theorem pos_part_ineq (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (max a 0 - max b 0) * (a - b) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_right ha, max_eq_right hb]
  · rw [max_eq_right ha, max_eq_left hb]; nlinarith
  · rw [max_eq_left ha, max_eq_right hb]; nlinarith
  · rw [max_eq_left ha, max_eq_left hb]; nlinarith

theorem pairing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f g : V → ℝ) :
    ∑ v, g v * (G.lapMatrix ℝ).mulVec f v
      = (1 / 2 : ℝ) * ∑ u, ∑ v, (if G.Adj u v then (g u - g v) * (f u - f v) else 0) := by
  set S := ∑ u, ∑ v, (if G.Adj u v then g u * (f u - f v) else 0) with hS
  have hL : ∑ v, g v * (G.lapMatrix ℝ).mulVec f v = S := by
    rw [hS]
    simp_rw [lap_mulVec_eq, Finset.mul_sum, mul_ite, mul_zero]
  have hswap : S = ∑ u, ∑ v, (if G.Adj u v then -(g v * (f u - f v)) else 0) := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    by_cases h : G.Adj u v
    · rw [if_pos h.symm, if_pos h]; ring
    · rw [if_neg (fun h' => h h'.symm), if_neg h]
  have h2 : ∑ u, ∑ v, (if G.Adj u v then (g u - g v) * (f u - f v) else 0)
      = S + ∑ u, ∑ v, (if G.Adj u v then -(g v * (f u - f v)) else 0) := by
    rw [hS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs <;> ring
  rw [hL, h2, ← hswap]; ring

end AlonEq21Aux

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (f : V → ℝ) (hf0 : f ≠ 0)
    (hf : Matrix.mulVec (G.lapMatrix ℝ) f = AlonMilman.Diameter.lambda1 G • f) :
    (1 / 2 : ℝ) * ∑ u, ∑ v, (if G.Adj u v then (max (f u) 0 - max (f v) 0) ^ 2 else 0) ≤
      AlonMilman.Diameter.lambda1 G * ∑ v, (max (f v) 0) ^ 2 := by
  have hp := AlonEq21Aux.pairing G f (fun v => max (f v) 0)
  rw [hf] at hp
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  have hr : ∑ v, max (f v) 0 * (AlonMilman.Diameter.lambda1 G * f v)
      = AlonMilman.Diameter.lambda1 G * ∑ v, (max (f v) 0) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rcases le_total (f v) 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_left h]; ring
  rw [← hr, hp]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => ?_))
  split_ifs
  · exact AlonEq21Aux.pos_part_ineq _ _
  · exact le_refl _
