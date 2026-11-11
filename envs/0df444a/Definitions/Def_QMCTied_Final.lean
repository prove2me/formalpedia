-- Prove2me | Definitions.Def_QMCTied_Final
-- name    : QMCTied_Final
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:20:52.698987+00:00
-- url     : https://prove2.me/theorems/0e78d389-7fb7-4243-90a2-062c1393196e
-- title:
--   Polynomial-time lower value for the Pauli moment relaxation within $\varepsilon W$
-- statement:
--   For every fixed level $k\ge2$ and rational $\varepsilon>0$ there is a deterministic polynomial-time program returning a rational $L_G\ge0$ with $L_G\le U_k(G)$ and $U_k(G)-\varepsilon W(G)\le L_G$ for every weighted graph $G$, where $U_k$ is the value of the level-$k$ Pauli moment relaxation and $W$ the total weight.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_Lap
import Definitions.Def_QMCSub_Edge
import Definitions.Def_QMCSub_Bridge1
import Definitions.Def_QMCSub_Bridge2
import Definitions.Def_QMCSub_Final1
import Definitions.Def_QMCTied_Defs
import Definitions.Def_QMCTied_Core
import Definitions.Def_QMCTied_Prog
import Definitions.Def_QMCTied_Poly
import Definitions.Def_QMCTied_Pauli
import Definitions.Def_QMCTied_Params
import Definitions.Def_QMCTied_Bridge

/-!
A polynomial-time lower value for every fixed level of the Pauli moment relaxation, within any
fixed fraction of the total weight.
-/

namespace QMCTied
open QuantumMaxCutEnergy QMCNumericRuntime QMCSub Matrix
open OAI.MetricKMedian.Binary
open scoped BigOperators

theorem fuelT2_length (E N : ℕ) : (fuelT2 E (List.range N)).length = TOf E N := by
  unfold fuelT2 TOf
  simp only [pw_length, rep_length, List.length_range]
  ring

theorem fuelK2_length (E N : ℕ) :
    (fuelK2 E (List.range N)).length = 2 * (parOf E N).K := by
  unfold fuelK2 parOf
  rw [List.length_flatMap]
  simp only [List.length_append, pw_length, rep_length, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul]
  ring

theorem padI2_length (E N : ℕ) :
    (padI2 E (List.range N)).length =
      1 + (fuelK2 E (List.range N)).length * (8192 * E * E + N * 10) := by
  unfold padI2
  rw [List.length_cons, List.length_flatMap]
  simp only [List.length_append, pw_length, rep_length, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul]
  omega

theorem padO2_length (E N : ℕ) :
    (padO2 E (List.range N)).length = 4096 * E * E + 1 + N * 8 := by
  unfold padO2
  simp only [List.length_append, pw_length, rep_length, List.length_range]

theorem DQ_range (E N : ℕ) : DQ E (List.range N) = ((parOf E N).D : ℚ) := by
  unfold DQ NQ parOf
  rw [List.length_range]
  push_cast
  ring

theorem prmW_range (E N : ℕ) :
    prmW E (List.range N) =
      [((parOf E N).D : ℚ), (parOf E N).eta, ((parOf E N).dN : ℚ), ((parOf E N).D2 : ℚ),
        (1 / 2 : ℚ)] := by
  unfold prmW
  rw [DQ_range]
  unfold etaQ2 dNQ NQ parOf
  rw [List.length_range]
  push_cast
  ring_nf

/-- The class-sum table of the objective coefficients. -/
theorem gCTab_eq {N : ℕ} {κ : Type} [DecidableEq κ] (I : Inst N κ) (clsT csT : Mat)
    (hcls : ∀ i j i' j' : Fin N, gm clsT i j = gm clsT i' j' ↔ I.cls i j = I.cls i' j')
    (hcs : ∀ i j : Fin N, gm csT i j = I.Cs i j) (i j : Fin N) :
    gm (gCTabW (List.range N) clsT csT) i j = gC I (I.cls i j) := by
  have hrow : (gCTabW (List.range N) clsT csT) =
      List.ofFn (fun i : Fin N => List.ofFn (fun j : Fin N => gC I (I.cls i j))) := by
    unfold gCTabW
    apply map_range_congr
    intro i
    apply map_range_congr
    intro j
    unfold gC
    apply sum_range_congr
    intro i'
    apply sum_range_congr
    intro j'
    by_cases h : I.cls i' j' = I.cls i j
    · rw [if_pos ((hcls i' j' i j).mpr h), if_pos h, hcs]
    · rw [if_neg (fun e => h ((hcls i' j' i j).mp e)), if_neg h]
  rw [hrow]
  simp [gm]

/-- On a graph with positive total weight the program's loop is the integer iteration of the
Pauli instance. -/
theorem runW_iter_eq (k E : ℕ) (hk : 1 ≤ k) (hE : 1 ≤ E) (G : Input) (hW : 0 < Wq G) :
    runW k E (List.range G.n) (inputEdges G) =
      (tabOf (pauliInst k G)
          (lamSeq (pauliInst k G) (parOf E (RW k G).length) (TOf E (RW k G).length)),
        ((bestSeq (pauliInst k G) (parOf E (RW k G).length) (TOf E (RW k G).length) : ℤ) : ℚ)) := by
  have hI := pauliInst_good k G hk hW
  have hN := rows_length_ge k G hk hW
  have pg := pgood E (RW k G).length hE hN
  have hcls := clsTab_iff k G
  have hcs : ∀ i j : Fin (RW k G).length,
      gm (csTabW (List.range G.n) (RW k G) (inputEdges G)) i j = (pauliInst k G).Cs i j :=
    fun _ _ => rfl
  have hD0 : 0 ≤ (parOf E (RW k G).length).D := pg.hD.le
  have hfitI : ∀ lam : PauliSDP.Word G.n → ℤ, (∀ c, |lam c| ≤ (parOf E (RW k G).length).D) →
      ∀ m, m ≤ (fuelK2 E (List.range (RW k G).length)).length → ∀ a b,
      ((Mz (pauliInst k G) (parOf E (RW k G).length).D lam ^ m) a b).natAbs <
        2 ^ (padI2 E (List.range (RW k G).length)).length := by
    intro lam hbox m hm a b
    rw [padI2_length]
    apply pow_fits _ ((RW k G).length * (parOf E (RW k G).length).D.natAbs +
      (parOf E (RW k G).length).D.natAbs) (8192 * E * E + (RW k G).length * 10) _ _ pg.hG1 m hm
    intro a' b'
    have h := Mz_entry_abs_le (pauliInst k G) hI (parOf E (RW k G).length).D hD0 lam hbox a' b'
    have h2 := natAbs_le_of_abs_le h
    have h3 : (((RW k G).length : ℤ) * (parOf E (RW k G).length).D +
        (parOf E (RW k G).length).D).natAbs =
        (RW k G).length * (parOf E (RW k G).length).D.natAbs +
          (parOf E (RW k G).length).D.natAbs := by
      have h4 : (((RW k G).length : ℤ) * (parOf E (RW k G).length).D +
          (parOf E (RW k G).length).D) =
          (((RW k G).length * (parOf E (RW k G).length).D.natAbs +
            (parOf E (RW k G).length).D.natAbs : ℕ) : ℤ) := by
        push_cast
        rw [abs_of_nonneg hD0]
      rw [h4]
      exact Int.natAbs_natCast _
    rw [h3] at h2
    exact h2
  have h := runT_eq (pauliInst k G) hI (parOf E (RW k G).length)
    (clsTabW (List.range G.n) (RW k G)) (sgnTabW (List.range G.n) (RW k G))
    (gCTabW (List.range (RW k G).length) (clsTabW (List.range G.n) (RW k G))
      (csTabW (List.range G.n) (RW k G) (inputEdges G)))
    (csTabW (List.range G.n) (RW k G) (inputEdges G))
    (fuelK2 E (List.range (RW k G).length)) (padI2 E (List.range (RW k G).length))
    (padO2 E (List.range (RW k G).length)) (fuelT2 E (List.range (RW k G).length))
    (sgnTab_eq k G) hcls hcs (gCTab_eq (pauliInst k G) _ _ hcls hcs)
    hN pg.hD pg.hdN pg.hK (fuelK2_length E _)
    (by rw [padI2_length]; omega) (by rw [padO2_length]; omega) hfitI
    (by rw [padO2_length]; exact pg.hG2) (by rw [padO2_length]; exact pg.hG3)
  rw [fuelT2_length] at h
  unfold runW staticW
  rw [prmW_range, DQ_range]
  exact h

/-- The solver's value on every input: attained from below by a feasible moment vector, and
within `5 W / (8 E)` of every feasible value. -/
theorem solveW_spec (k E : ℕ) (hk : 1 ≤ k) (hE : 1 ≤ E) (G : Input) :
    0 ≤ solveW k E (List.range G.n) (inputEdges G) ∧
    (∃ L : PauliSDP.Word G.n → ℝ, PauliSDP.Feasible k L ∧
      ((solveW k E (List.range G.n) (inputEdges G) : ℚ) : ℝ) ≤
        PauliSDP.objective G.weights L) ∧
    (∀ L : PauliSDP.Word G.n → ℝ, PauliSDP.Feasible k L →
      PauliSDP.objective G.weights L ≤
        ((solveW k E (List.range G.n) (inputEdges G) : ℚ) : ℝ) +
          5 / (8 * (E : ℝ)) * ((Wq G : ℚ) : ℝ)) := by
  rcases (Wq_nonneg G).eq_or_lt with hW0 | hW
  · have hsolve : solveW k E (List.range G.n) (inputEdges G) = 0 := by
      unfold solveW
      rw [edgeWeightSum_inputEdges, ← hW0]
      simp
    rw [hsolve]
    refine ⟨le_rfl, ?_, ?_⟩
    · obtain ⟨L, hL, h0⟩ := exists_feasible k G
      exact ⟨L, hL, by simpa using h0⟩
    · intro L _
      rw [objective_zero G hW0.symm L, ← hW0]
      simp
  · have hI := pauliInst_good k G hk hW
    have hN := rows_length_ge k G hk hW
    have pg := pgood E (RW k G).length hE hN
    have hrun := runW_iter_eq k E hk hE G hW
    have hWne : edgeWeightSum (inputEdges G) ≠ 0 := by
      rw [edgeWeightSum_inputEdges]
      exact hW.ne'
    have hsolve : solveW k E (List.range G.n) (inputEdges G) =
        Wq G * (((bestSeq (pauliInst k G) (parOf E (RW k G).length)
          (TOf E (RW k G).length) : ℤ) : ℚ) / (8 * (E : ℚ))) := by
      unfold solveW
      rw [if_neg hWne, hrun, edgeWeightSum_inputEdges]
    have hD2 : (((parOf E (RW k G).length).D2 : ℕ) : ℝ) = 8 * (E : ℝ) := by
      unfold parOf
      push_cast
      rfl
    have hWR : (0 : ℝ) < ((Wq G : ℚ) : ℝ) := by exact_mod_cast hW
    have hER : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
    have hsolveR : ((solveW k E (List.range G.n) (inputEdges G) : ℚ) : ℝ) =
        ((Wq G : ℚ) : ℝ) * ((bestSeq (pauliInst k G) (parOf E (RW k G).length)
          (TOf E (RW k G).length) : ℝ) / (8 * (E : ℝ))) := by
      rw [hsolve]
      push_cast
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hsolve]
      have hb := bestSeq_nonneg (pauliInst k G) (parOf E (RW k G).length) (TOf E (RW k G).length)
      have hbq : (0 : ℚ) ≤ ((bestSeq (pauliInst k G) (parOf E (RW k G).length)
          (TOf E (RW k G).length) : ℤ) : ℚ) := by exact_mod_cast hb
      have hEq : (0 : ℚ) < 8 * (E : ℚ) := by
        have : (0 : ℚ) < (E : ℚ) := by exact_mod_cast hE
        linarith
      exact mul_nonneg hW.le (div_nonneg hbq hEq.le)
    · obtain ⟨ℓ, hℓ, hle⟩ := tied_sound (pauliInst k G) hI (parOf E (RW k G).length) hN pg.hD
        pg.hdN pg.hK pg.hD2 (TOf E (RW k G).length)
      refine ⟨ℓ, pauli_of_feas k G ℓ hℓ, ?_⟩
      rw [objective_eq k G hk hW ℓ, hsolveR]
      rw [hD2] at hle
      exact mul_le_mul_of_nonneg_left hle hWR.le
    · intro L hL
      have hacc := tied_accurate (pauliInst k G) hI (parOf E (RW k G).length) hN pg.hD pg.heta
        pg.hdN pg.hK pg.hD2 (TOf E (RW k G).length) pg.hT L (feas_of_pauli k G L hL)
      have herr := pg.herr
      rw [objective_eq k G hk hW L, hsolveR]
      rw [hD2] at hacc
      have h1 : obj (pauliInst k G) L ≤
          (bestSeq (pauliInst k G) (parOf E (RW k G).length) (TOf E (RW k G).length) : ℝ) /
            (8 * (E : ℝ)) + 5 / (8 * (E : ℝ)) := by
        rw [hD2] at herr
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hWR.le
      linarith

/-- For every fixed level and accuracy there is a polynomial-time program computing a lower
value of the Pauli moment relaxation within `ε W`. -/
theorem pauli_value_compiler (k : ℕ) (hk : 2 ≤ k) (ε : ℚ≥0) (hε : 0 < ε) :
    ∃ B : QuantumMaxCutEnergy.Algorithm,
      Nonempty (OAI.MetricKMedian.Binary.PolyProgram
        QuantumMaxCutEnergy.encodeRequest OAI.MetricKMedian.Binary.Ratio.encode
        (fun req : QuantumMaxCutEnergy.Input × List Bool => (B.run req.1 req.2 : ℚ))) ∧
      B.randomFactor = 0 ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        (B.run G [] : ℝ) ≤ QuantumMaxCutEnergy.PauliSDP.value k G ∧
        QuantumMaxCutEnergy.PauliSDP.value k G -
          (ε : ℝ) * (∑ e, (G.weights e : ℝ)) ≤ (B.run G [] : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨E, hE, hEε⟩ : ∃ E : ℕ, 1 ≤ E ∧ (1 : ℝ) / (E : ℝ) ≤ (ε : ℝ) := by
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨E, hE⟩ := exists_nat_gt (1 / (ε : ℝ))
    have hE0 : (0 : ℝ) < (E : ℝ) := lt_trans (by positivity) hE
    refine ⟨E, by exact_mod_cast hE0, ?_⟩
    rw [div_le_iff₀ hE0]
    rw [div_lt_iff₀ hεR] at hE
    linarith
  refine ⟨⟨0, 0, fun G _ => ⟨solveW k E (List.range G.n) (inputEdges G),
    (solveW_spec k E hk1 hE G).1⟩⟩, ?_, rfl, ?_⟩
  · have P0 : PolyProgram id Ratio.encode (solveRawW k E) :=
      (BooleanLists.packProgram.comp (solveRawW_poly k E).program).congr _ (fun _ => rfl)
    exact ⟨P0.recode encodeRequest (fun _ => rfl) (fun req => by
      obtain ⟨G, coins⟩ := req
      show Ratio.encode (solveRawW k E (encodeRequest (G, coins))) =
        Ratio.encode (solveW k E (List.range G.n) (inputEdges G))
      unfold solveRawW
      rw [parserVertices_request, parseEdges_request])⟩
  · intro G
    obtain ⟨_, ⟨L', hL', hle⟩, hacc⟩ := solveW_spec k E hk1 hE G
    have hne : {v : ℝ | ∃ L : PauliSDP.Word G.n → ℝ,
        PauliSDP.Feasible k L ∧ v = PauliSDP.objective G.weights L}.Nonempty :=
      ⟨_, L', hL', rfl⟩
    have hbdd : BddAbove {v : ℝ | ∃ L : PauliSDP.Word G.n → ℝ,
        PauliSDP.Feasible k L ∧ v = PauliSDP.objective G.weights L} :=
      ⟨2 * ((Wq G : ℚ) : ℝ), by
        rintro _ ⟨L, hL, rfl⟩
        exact objective_le_two k G hk1 L hL⟩
    have hcast : (((⟨solveW k E (List.range G.n) (inputEdges G),
        (solveW_spec k E hk1 hE G).1⟩ : ℚ≥0) : ℚ≥0) : ℝ) =
        ((solveW k E (List.range G.n) (inputEdges G) : ℚ) : ℝ) :=
      (Rat.cast_nnratCast (K := ℝ) (⟨solveW k E (List.range G.n) (inputEdges G),
        (solveW_spec k E hk1 hE G).1⟩ : ℚ≥0)).symm
    have hWcast : (∑ e, (G.weights e : ℝ)) = ((Wq G : ℚ) : ℝ) := by
      unfold Wq
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact (Rat.cast_nnratCast _).symm
    have hW0 : (0 : ℝ) ≤ ((Wq G : ℚ) : ℝ) := by exact_mod_cast Wq_nonneg G
    have hE0 : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
    constructor
    · show (((⟨solveW k E (List.range G.n) (inputEdges G),
        (solveW_spec k E hk1 hE G).1⟩ : ℚ≥0) : ℚ≥0) : ℝ) ≤ PauliSDP.value k G
      rw [hcast]
      exact hle.trans (le_csSup hbdd ⟨L', hL', rfl⟩)
    · show PauliSDP.value k G - (ε : ℝ) * (∑ e, (G.weights e : ℝ)) ≤
        (((⟨solveW k E (List.range G.n) (inputEdges G),
          (solveW_spec k E hk1 hE G).1⟩ : ℚ≥0) : ℚ≥0) : ℝ)
      rw [hcast, hWcast]
      have hsup : PauliSDP.value k G ≤
          ((solveW k E (List.range G.n) (inputEdges G) : ℚ) : ℝ) +
            5 / (8 * (E : ℝ)) * ((Wq G : ℚ) : ℝ) :=
        csSup_le hne (by
          rintro _ ⟨L, hL, rfl⟩
          exact hacc L hL)
      have h58 : 5 / (8 * (E : ℝ)) ≤ (ε : ℝ) := by
        have : 5 / (8 * (E : ℝ)) ≤ 1 / (E : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hE0]
          nlinarith
        linarith
      have := mul_le_mul_of_nonneg_right h58 hW0
      linarith

end QMCTied


