-- Prove2me | Definitions.Def_QMCSub_Final1
-- name    : QMCSub_Final1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:22:30.754136+00:00
-- url     : https://prove2.me/theorems/2af85a9f-c9b9-4008-bd5b-06ccd98633f6
-- title:
--   The program's run on a canonical input
-- statement:
--   For an input graph with positive total weight and admissible constants, all size guards of the program are inactive, so its outer loop returns exactly the final iterate and accumulated value of the integer subgradient iteration on the Laplacian of the scaled rounded weights. The program's feasibility check is equivalent to the integer check $c_\theta(T-u^{(T)}_i)\le\eta T$ for all $i$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter
import Definitions.Def_QMCSub_Step
import Definitions.Def_QMCSub_Core
import Definitions.Def_QMCSub_Lap
import Definitions.Def_QMCSub_Edge
import Definitions.Def_QMCSub_Bridge1
import Definitions.Def_QMCSub_Bridge2
import Definitions.Def_QMCSub_Params

/-!
The program's run on a canonical input, identified with the integer iteration.
-/

namespace QMCSub
open QuantumMaxCutEnergy QMCNumericRuntime Matrix
open scoped BigOperators

theorem rep_length (k : ℕ) : (rep k).length = k := List.length_replicate

theorem pw_length (idx : List ℕ) (l : List Unit) :
    (pw idx l).length = idx.length * l.length := by
  unfold pw
  rw [List.length_flatMap]
  simp

theorem fuelT_length (c : Consts) (n : ℕ) : (fuelT c (List.range n)).length = Tn c n := by
  unfold fuelT Tn
  simp only [pw_length, rep_length, List.length_range]

theorem fuelK_length (c : Consts) (n : ℕ) : (fuelK c (List.range n)).length = Kn2 c n := by
  unfold fuelK Kn2
  simp only [pw_length, rep_length, List.length_range]

theorem padI_length (c : Consts) (n : ℕ) :
    (padI c (List.range n)).length = 1 + Kn2 c n * (c.cbI + n * 8) := by
  unfold padI
  rw [List.length_cons, List.length_flatMap]
  simp only [List.length_append, pw_length, rep_length, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul, fuelK_length]
  omega

theorem padO_length (c : Consts) (n : ℕ) :
    (padO c (List.range n)).length = c.cbO + 1 + n * 9 := by
  unfold padO
  simp only [List.length_append, pw_length, rep_length, List.length_range]

theorem nq_range (n : ℕ) : nq (List.range n) = (n : ℚ) := by
  unfold nq
  rw [List.length_range]

theorem etaQ_range (c : Consts) (n : ℕ) : etaQ c (List.range n) = ((etaZ c n : ℤ) : ℚ) := by
  unfold etaQ etaZ
  rw [nq_range]
  push_cast
  ring

theorem sigQ_range (c : Consts) (n : ℕ) : sigQ c (List.range n) = ((sigZ c n : ℤ) : ℚ) := by
  unfold sigQ sigZ
  rw [nq_range]
  push_cast
  ring

theorem omQ_range (c : Consts) (n : ℕ) : omQ c (List.range n) = ((OmN c n : ℕ) : ℚ) := by
  unfold omQ OmN
  rw [nq_range]
  push_cast
  ring

theorem TQ_range (c : Consts) (n : ℕ) : TQ c (List.range n) = ((Tn c n : ℕ) : ℚ) := by
  unfold TQ
  rw [fuelT_length]

theorem scaledN_eq (c : Consts) (G : Input) (i k : Fin G.n) :
    scaledN c (List.range G.n) (inputEdges G) i.val k.val =
      ((Nz (OmN c G.n) G i k : ℤ) : ℚ) := by
  unfold scaledN Nz
  rw [omQ_range, edgeW_inputEdges, edgeWeightSum_inputEdges]
  exact qfloor_eq_floor _
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Aq_nonneg G i k)) (Wq_nonneg G))

theorem lapList_eq (c : Consts) (G : Input) :
    lapList c (List.range G.n) (inputEdges G) = toM (Lz (OmN c G.n) G) := by
  show (List.range G.n).map (fun i => (List.range G.n).map (fun j =>
      if i = j then
        ((List.range G.n).map (fun k => scaledN c (List.range G.n) (inputEdges G) i k)).sum
      else -scaledN c (List.range G.n) (inputEdges G) i j)) =
    List.ofFn (fun i : Fin G.n => List.ofFn (fun j : Fin G.n =>
      ((Lz (OmN c G.n) G i j : ℤ) : ℚ)))
  apply map_range_congr
  intro i
  apply map_range_congr
  intro j
  unfold Lz
  rw [Matrix.of_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl,
      sum_range_congr G.n
        (fun k => scaledN c (List.range G.n) (inputEdges G) i k)
        (fun k : Fin G.n => ((Nz (OmN c G.n) G i k : ℤ) : ℚ)) (fun k => scaledN_eq c G i k)]
    push_cast
    rfl
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    rw [if_neg h', if_neg h, scaledN_eq]
    push_cast
    rfl

theorem natAbs_le_of_abs_le {x s : ℤ} (h : |x| ≤ s) : x.natAbs ≤ s.natAbs := by
  have h1 : (x.natAbs : ℤ) ≤ (s.natAbs : ℤ) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs]
    exact h.trans (le_abs_self s)
  exact_mod_cast h1

/-- On a canonical input with positive total weight, the program's outer loop computes the
integer iteration. -/
theorem runO_eq (c : Consts) (G : Input) (hGood : Good c G.n) (hW : 0 < Wq G) (hn : 1 ≤ G.n)
    (K : ℕ) (hK : Kn2 c G.n = 2 * K) :
    runO c (List.range G.n) (inputEdges G) =
      (toV (useq (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n)),
        ((Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) : ℤ) : ℚ)) := by
  have hLap := lapHyp (OmN c G.n) G hW hGood.hOm
  have hη := hGood.hη
  have hσ0 : 0 ≤ sigZ c G.n := by
    have h1 : (0 : ℤ) ≤ (Tn c G.n : ℤ) * (etaZ c G.n * G.n) :=
      mul_nonneg (Int.natCast_nonneg _) (mul_nonneg hη.le (Int.natCast_nonneg _))
    exact h1.trans hGood.hσ
  -- bound on the iterates
  have hu : ∀ k, k ≤ Tn c G.n → ∀ i,
      |useq (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k i| ≤ sigZ c G.n := by
    intro k hk i
    have h := useq_abs_le hLap.symm (etaZ c G.n) (sigZ c G.n) K hη.le hn k i
    have h0 : 0 ≤ etaZ c G.n * (G.n : ℤ) := mul_nonneg hη.le (Int.natCast_nonneg _)
    have hk' : (k : ℤ) * (etaZ c G.n * G.n) ≤ (Tn c G.n : ℤ) * (etaZ c G.n * G.n) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) h0
    exact h.trans (hk'.trans hGood.hσ)
  have hI : ∀ k, k < (fuelT c (List.range G.n)).length → ∀ m,
      m ≤ (fuelK c (List.range G.n)).length → ∀ a b,
      ((Mz (Lz (OmN c G.n) G) (sigZ c G.n)
        (useq (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k) ^ m) a b).natAbs <
        2 ^ (padI c (List.range G.n)).length := by
    intro k hk m hm a b
    rw [fuelT_length] at hk
    rw [fuelK_length] at hm
    rw [padI_length]
    apply pow_fits _ (2 * OmN c G.n + 2 * (sigZ c G.n).natAbs) (c.cbI + G.n * 8) (Kn2 c G.n)
      _ hGood.hG1 m hm
    intro a' b'
    apply Mz_entry_le
    · intro a'' b''
      have h := Lz_abs_le (OmN c G.n) G hW a'' b''
      have h2 := natAbs_le_of_abs_le h
      have h3 : (2 * (OmN c G.n : ℤ)).natAbs = 2 * OmN c G.n := by
        rw [show (2 * (OmN c G.n : ℤ)) = ((2 * OmN c G.n : ℕ) : ℤ) by push_cast; rfl]
        exact Int.natAbs_natCast _
      rw [h3] at h2
      exact h2
    · intro a''
      have h := hu k hk.le a''
      rw [abs_le] at h
      have h2 : |sigZ c G.n +
          useq (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k a''| ≤ 2 * sigZ c G.n := by
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
      have h3 := natAbs_le_of_abs_le h2
      have h4 : (2 * sigZ c G.n).natAbs = 2 * (sigZ c G.n).natAbs := by
        rw [Int.natAbs_mul]
        rfl
      rw [h4] at h3
      exact h3
  have hU : ∀ k, k ≤ (fuelT c (List.range G.n)).length → ∀ i,
      (useq (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k i).natAbs <
        2 ^ (padO c (List.range G.n)).length := by
    intro k hk i
    rw [fuelT_length] at hk
    rw [padO_length]
    exact lt_of_le_of_lt (natAbs_le_of_abs_le (hu k hk i)) hGood.hG2
  have hP : ∀ k, k ≤ (fuelT c (List.range G.n)).length →
      (Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k).natAbs <
        2 ^ (padO c (List.range G.n)).length := by
    intro k hk
    rw [fuelT_length] at hk
    rw [padO_length]
    have hb := Pz_bounds hLap (etaZ c G.n) (sigZ c G.n) K k
    have htr := hLap.trace_le
    have htr0 := hLap.trace_pos.le
    have h1 : Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k ≤
        ((Tn c G.n * (G.n * (2 * OmN c G.n)) : ℕ) : ℤ) := by
      push_cast
      have h2 : (k : ℤ) * ((G.n : ℤ) * (Lz (OmN c G.n) G).trace) ≤
          (Tn c G.n : ℤ) * ((G.n : ℤ) * (2 * (OmN c G.n : ℤ))) := by
        apply mul_le_mul (by exact_mod_cast hk)
          (mul_le_mul_of_nonneg_left htr (Int.natCast_nonneg _))
          (mul_nonneg (Int.natCast_nonneg _) htr0) (Int.natCast_nonneg _)
      exact hb.2.trans h2
    have h3 : ((Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k).natAbs : ℤ) ≤
        ((Tn c G.n * (G.n * (2 * OmN c G.n)) : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg hb.1]
      exact h1
    have h4 : (Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K k).natAbs ≤
        Tn c G.n * (G.n * (2 * OmN c G.n)) := by exact_mod_cast h3
    exact lt_of_le_of_lt h4 hGood.hG3
  have hrun := run_eq hLap (etaZ c G.n) (sigZ c G.n) K hη.le (fuelK c (List.range G.n))
    (padI c (List.range G.n)) (padO c (List.range G.n)) (fuelT c (List.range G.n))
    (by rw [fuelK_length, hK]) (by rw [padI_length]; omega) (by rw [padO_length]; omega)
    hI hU hP
  rw [fuelT_length] at hrun
  unfold runO staticO
  rw [lapList_eq, etaQ_range, sigQ_range]
  exact hrun

/-- The program's feasibility check is the integer check. -/
theorem checkOK_iff (c : Consts) (n : ℕ) (u : Fin n → ℤ) :
    checkOK c (List.range n) (toV u) = true ↔
      ∀ i : Fin n, (c.cth : ℤ) * ((Tn c n : ℤ) - u i) ≤ etaZ c n * (Tn c n : ℤ) := by
  unfold checkOK
  rw [List.isEmpty_iff, List.filter_eq_nil_iff, etaQ_range, TQ_range]
  constructor
  · intro h i
    have h1 := h i.val (List.mem_range.mpr i.isLt)
    rw [gv_toV] at h1
    simp only [decide_eq_true_eq, not_lt] at h1
    exact_mod_cast h1
  · intro h a ha
    have hi := h ⟨a, List.mem_range.mp ha⟩
    have h1 := gv_toV u ⟨a, List.mem_range.mp ha⟩
    simp only at h1
    rw [h1]
    simp only [decide_eq_true_eq, not_lt]
    exact_mod_cast hi

end QMCSub


