-- Prove2me | Definitions.Def_DetDLP_W4_M5QueryBridge
-- name    : DetDLP_W4_M5QueryBridge
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:44:14.979971+00:00
-- url     : https://prove2.me/theorems/2e60e40a-7120-4ab5-94f8-f9c55138613f
-- title:
--   Uniform entry-machine bound from a polynomial-time bitstring evaluator
-- statement:
--   Combines a bitstring evaluation specification with explicit query framing and polynomial bound composition to produce one machine and one uniform exponent for time and space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_PolyTBridge
import Definitions.Def_DetDLP_W4_M5GraphBounds

set_option autoImplicit false

namespace DetDLP.w4_M5QueryBridge
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open w4_M5GraphBounds w4_MulParams

theorem length_frame (s : List Bool) : (Encoding.frame s).length = 2*s.length+1 := by
  induction s with
  | nil => rfl
  | cons b s ih => change (Encoding.frame s).length+1+1 = 2*(s.length+1)+1; omega

theorem length_query (d v : ℕ) (a : List Bool) :
    (encodePortQuery (countWord d) v a).length = 2*((countWord d).length+(countWord v).length+a.length)+7 := by
  simp [encodePortQuery, Encoding.encodeList, length_frame]; omega

theorem length_countWord_le (n : ℕ) : (countWord n).length ≤ n+1 := by
  by_cases h : n = 0
  · simp [h,countWord]
  · simp only [countWord, if_neg h, Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

theorem vertices_le {d : ℕ} (hd : 1 ≤ d) : (graph d hd).nV ≤ 256*(d+1) := by
  have hJ := J_lt_linear hd
  have hn := n0_upper hd
  have hL := L_le_half_J hd
  have hr := L1_le_L d
  have hc := L2_le_L d
  rw [graph_nV hd]; omega

theorem length_legal_query {d : ℕ} (hd : 1 ≤ d) (v : Fin (graph d hd).nV)
    (a : Fin ((graph d hd).deg v) → Bool) :
    (encodePortQuery (countWord d) v.val (List.ofFn a)).length + 1 ≤ 4096*(d+1) := by
  have he := graph_edge_bound hd
  have hv := (v.isLt.trans_le (vertices_le hd))
  have hdeg : (graph d hd).deg v ≤ (graph d hd).nE := by
    unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
    exact (List.length_filter_le ..).trans List.length_finRange.le
  rw [length_query, List.length_ofFn]
  have := length_countWord_le d
  have := length_countWord_le v.val
  omega

theorem polyBound_monoK {a b d : ℕ} (hab : a ≤ b) : polyBound a d ≤ polyBound b d := by
  have h : (1:ℝ) ≤ (d:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  exact mul_le_mul (by exact_mod_cast hab) (pow_le_pow_right₀ h hab) (by positivity) (by positivity)

theorem absorb {d n c K : ℕ} (hn : n+1 ≤ 4096*(d+1)) (hc : c ≤ K) (hk : c*4096^c ≤ K) :
    polyBound c n ≤ polyBound K d := by
  have h : (n:ℝ)+1 ≤ 4096*((d:ℝ)+1) := by exact_mod_cast hn
  have hb : (1:ℝ) ≤ (d:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  calc
    polyBound c n ≤ (c:ℝ)*(4096*((d:ℝ)+1))^c := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h _) (by positivity)
    _ = ((c:ℝ)*4096^c)*((d:ℝ)+1)^c := by rw [mul_pow,mul_assoc]
    _ ≤ polyBound K d := mul_le_mul (by exact_mod_cast hk) (pow_le_pow_right₀ hb hc) (by positivity) (by positivity)

/-- One evaluator and one exponent suffice simultaneously for every admissible width. -/
theorem machine_of_query (f : List Bool → List Bool) (hf : Groundwork.PolyT f)
    (T : (d : ℕ) → (hd : 1 ≤ d) → (v : Fin (graph d hd).nV) → (Fin ((graph d hd).deg v) → Bool) → Bool)
    (hspec : ∀ (d : ℕ) (hd : 1 ≤ d) (v : Fin (graph d hd).nV) (a : Fin ((graph d hd).deg v) → Bool),
      f (encodePortQuery (countWord d) v.val (List.ofFn a)) = [T d hd v a]) :
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ), ∀ (d : ℕ) (hd : 1 ≤ d),
      ((graph d hd).nV : ℝ) ≤ polyBound K d ∧
      BoolBTNEntryEvaluable (countWord d) (graph d hd) (T d hd) E outE (polyBound K d) (polyBound K d) := by
  obtain ⟨E, out, c, run⟩ := PolyTBridge.polyT_listBool_runsWithin f hf
  let K := max 256 (max c (c*4096^c))
  refine ⟨E,out,K,fun d hd => ⟨(graph_vertex_bound hd).trans (polyBound_monoK (le_max_left ..)),?_⟩⟩
  intro v a
  let w := encodePortQuery (countWord d) v.val (List.ofFn a)
  have h := run w
  rw [show f w = _ from hspec d hd v a] at h
  have b : polyBound c w.length ≤ polyBound K d := absorb (length_legal_query hd v a)
    ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))
  exact PolyTBridge.runsWithin_mono_local h b b

end DetDLP.w4_M5QueryBridge


