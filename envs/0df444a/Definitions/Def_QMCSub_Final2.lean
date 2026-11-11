-- Prove2me | Definitions.Def_QMCSub_Final2
-- name    : QMCSub_Final2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:24:15.100975+00:00
-- url     : https://prove2.me/theorems/834f5718-06c5-4887-89bd-22ff43bf4028
-- title:
--   A polynomial-time lower value for the Max-Cut SDP within $W/10000$
-- statement:
--   For every input graph the solver's value $L(G)\ge0$ satisfies $L(G)\le f_A(X')$ for some positive semidefinite $X'$ with unit diagonal, and $f_A(X)\le L(G)+W/10000$ for every such $X$, where $f_A(X)=\tfrac14\sum_{i,j}A_{ij}(1-X_{ij})$ and $W$ is the total weight. Hence $L(G)\le\mathrm{SDP}(A_G)\le L(G)+W/10000$, and $L$ is computed by a polynomial-time machine on the campaign's encodings.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
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
import Definitions.Def_QMCSub_Final1
import Definitions.Def_QMCSub_Poly

/-!
Correctness of the solver on canonical inputs, and the polynomial-time lower value for the
Max-Cut semidefinite relaxation.
-/

namespace QMCSub
open QuantumMaxCutEnergy QMCNumericRuntime Matrix
open OAI.MetricKMedian.Binary
open ModernConvex.Relaxations
open scoped BigOperators

theorem solveCore_nonneg (c : Consts) (idx : List ℕ) (xs : List NumericEdge) :
    0 ≤ solveCore c idx xs := by
  unfold solveCore
  split_ifs with h1 h2 h3
  · exact le_rfl
  · exact le_rfl
  · exact not_lt.mp h3
  · exact le_rfl

/-- On every input the solver's value is attained from below by a feasible point and is within
`W / 10000` of every feasible value. -/
theorem solveCore_spec (c : Consts) (hGood : ∀ n, 1 ≤ n → Good c n) (G : Input) :
    (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ, IsUnitDiagPSD X ∧
      ((solveCore c (List.range G.n) (inputEdges G) : ℚ) : ℝ) ≤
        maxcutRelaxationObjective (Ar G) X) ∧
    (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ, IsUnitDiagPSD X →
      maxcutRelaxationObjective (Ar G) X ≤
        ((solveCore c (List.range G.n) (inputEdges G) : ℚ) : ℝ) + ((Wq G : ℚ) : ℝ) / 10000) := by
  rcases (Wq_nonneg G).eq_or_lt with hW0 | hW
  · -- zero total weight
    have hsolve : solveCore c (List.range G.n) (inputEdges G) = 0 := by
      unfold solveCore
      rw [edgeWeightSum_inputEdges, ← hW0]
      simp
    rw [hsolve]
    constructor
    · exact ⟨1, one_feasible G, by simpa using obj_one_nonneg G⟩
    · intro X _
      rw [obj_zero G hW0.symm X, ← hW0]
      simp
  · -- positive total weight
    have hn : 1 ≤ G.n := by
      rcases Nat.eq_zero_or_pos G.n with h0 | hpos
      · exfalso
        have htr := (lapHyp (G.n ^ 2) G hW le_rfl).trace_pos
        have hz : (Lz (G.n ^ 2) G).trace = 0 := by
          unfold Matrix.trace
          exact Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega))
        omega
      · exact hpos
    have good := hGood G.n hn
    obtain ⟨K, hK⟩ := good.hK
    obtain ⟨δ, hδ0, hδ1, hpow, hHT, hPE⟩ := good.hδ
    rw [hK] at hpow
    have hLap := lapHyp (OmN c G.n) G hW good.hOm
    have hΩpos : 0 < OmN c G.n := lt_of_lt_of_le (Nat.pow_pos hn) good.hOm
    have hrun := runO_eq c G good hW hn K hK
    have hcheckZ : ∀ i, (c.cth : ℤ) * ((Tn c G.n : ℤ) -
        useq (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) i) ≤
        etaZ c G.n * (Tn c G.n : ℤ) :=
      fun i => check_holds hLap (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) good.hη hn good.hσ
        hδ0 hδ1 hpow c.cth good.hηθ hHT i
    have hcheck : checkOK c (List.range G.n) (runO c (List.range G.n) (inputEdges G)).1 = true := by
      rw [hrun]
      exact (checkOK_iff c G.n _).mpr hcheckZ
    have hWne : edgeWeightSum (inputEdges G) ≠ 0 := by
      rw [edgeWeightSum_inputEdges]
      exact hW.ne'
    have hraw : rawVal c (List.range G.n) (inputEdges G) =
        (Wq G / (OmN c G.n : ℚ)) *
          ((Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) : ℚ) * (c.cth : ℚ) /
            ((Tn c G.n : ℚ) * ((c.cth : ℚ) + 1))) / 4 := by
      unfold rawVal
      rw [hrun, edgeWeightSum_inputEdges, omQ_range, TQ_range]
    have hsolve : solveCore c (List.range G.n) (inputEdges G) =
        if rawVal c (List.range G.n) (inputEdges G) < 0 then 0
        else rawVal c (List.range G.n) (inputEdges G) := by
      unfold solveCore
      rw [if_neg hWne, if_pos hcheck]
    have hrawR : ((rawVal c (List.range G.n) (inputEdges G) : ℚ) : ℝ) =
        ((Wq G : ℚ) : ℝ) / (OmN c G.n : ℝ) *
          ((Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) : ℝ) * (c.cth : ℝ) /
            ((Tn c G.n : ℝ) * ((c.cth : ℝ) + 1))) / 4 := by
      rw [hraw]
      push_cast
      rfl
    have hWR : (0 : ℝ) < ((Wq G : ℚ) : ℝ) := by exact_mod_cast hW
    have hΩR : (0 : ℝ) < (OmN c G.n : ℝ) := by exact_mod_cast hΩpos
    have hcoef : (0 : ℝ) ≤ ((Wq G : ℚ) : ℝ) / (OmN c G.n : ℝ) := (div_pos hWR hΩR).le
    have hcastΩ : (((OmN c G.n : ℕ) : ℤ) : ℝ) = (OmN c G.n : ℝ) := Int.cast_natCast _
    constructor
    · -- soundness
      by_cases hneg : rawVal c (List.range G.n) (inputEdges G) < 0
      · rw [hsolve, if_pos hneg]
        exact ⟨1, one_feasible G, by simpa using obj_one_nonneg G⟩
      · rw [hsolve, if_neg hneg]
        have hdiag : ∀ i, 0 ≤ Lz (OmN c G.n) G i i := by
          intro i
          have h := hLap.psd.diag_nonneg (i := i)
          rw [castM_apply] at h
          exact_mod_cast h
        obtain ⟨X', hX', hX'1, hval⟩ := sound hLap.symm (etaZ c G.n) (sigZ c G.n) K hdiag
          good.hη (Tn c G.n) good.hT c.cth good.hcθ hcheckZ
        refine ⟨X', ⟨hX', hX'1⟩, ?_⟩
        have hlow := obj_lower (OmN c G.n) G hW hΩpos X' ⟨hX', hX'1⟩
        rw [hrawR]
        have h1 := mul_le_mul_of_nonneg_left hval hcoef
        linarith
    · -- accuracy
      intro X hX
      have hup := obj_upper (OmN c G.n) G hW hΩpos X hX
      have hacc := accurate hLap (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) good.hη hn good.hT
        good.hσ hδ0 hδ1 hpow c.cth good.hcθ good.hηθ hHT X hX.1 hX.2
      rw [hcastΩ] at hacc hPE
      have hge : ((rawVal c (List.range G.n) (inputEdges G) : ℚ) : ℝ) ≤
          ((solveCore c (List.range G.n) (inputEdges G) : ℚ) : ℝ) := by
        rw [hsolve]
        split_ifs with h
        · exact_mod_cast h.le
        · exact le_rfl
      rw [hrawR] at hge
      have h2 := mul_le_mul_of_nonneg_left
        (add_le_add_right hacc (2 * (G.n : ℝ) ^ 2)) hcoef
      have h4 := mul_le_mul_of_nonneg_left hPE hWR.le
      have h3 : ((Wq G : ℚ) : ℝ) / (OmN c G.n : ℝ) *
          ((Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) : ℝ) * (c.cth : ℝ) /
              ((Tn c G.n : ℝ) * ((c.cth : ℝ) + 1)) +
            (4 * (OmN c G.n : ℝ) / (c.cth : ℝ) + 1 +
              errE G.n (etaZ c G.n) (sigZ c G.n) (OmN c G.n : ℤ) (Tn c G.n) δ) +
            2 * (G.n : ℝ) ^ 2) / 4 =
          ((Wq G : ℚ) : ℝ) / (OmN c G.n : ℝ) *
            ((Pz (Lz (OmN c G.n) G) (etaZ c G.n) (sigZ c G.n) K (Tn c G.n) : ℝ) * (c.cth : ℝ) /
              ((Tn c G.n : ℝ) * ((c.cth : ℝ) + 1))) / 4 +
          ((Wq G : ℚ) : ℝ) *
            ((4 * (OmN c G.n : ℝ) / (c.cth : ℝ) + 1 +
              errE G.n (etaZ c G.n) (sigZ c G.n) (OmN c G.n : ℤ) (Tn c G.n) δ +
              2 * (G.n : ℝ) ^ 2) / (4 * (OmN c G.n : ℝ))) := by
        have hΩne : (OmN c G.n : ℝ) ≠ 0 := hΩR.ne'
        field_simp
        ring
      linarith

/-- A polynomial-time rational lower value for the Max-Cut semidefinite relaxation, within
`W / 10000` of the optimum. -/
theorem sdp_lower_value_tm2 :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  refine ⟨fun G => ⟨solveCore c0 (List.range G.n) (inputEdges G), solveCore_nonneg _ _ _⟩,
    ?_, ?_⟩
  · -- the machine
    have P0 : PolyProgram id Ratio.encode (solveRaw c0) :=
      (BooleanLists.packProgram.comp (solveRaw_poly c0).program).congr _ (fun _ => rfl)
    have P1 : PolyProgram encodeRequest Ratio.encode
        (fun req : Input × List Bool =>
          ((⟨solveCore c0 (List.range req.1.n) (inputEdges req.1),
            solveCore_nonneg _ _ _⟩ : ℚ≥0) : ℚ)) :=
      P0.recode encodeRequest (fun _ => rfl) (fun req => by
        obtain ⟨G, coins⟩ := req
        show Ratio.encode (solveRaw c0 (encodeRequest (G, coins))) =
          Ratio.encode (solveCore c0 (List.range G.n) (inputEdges G))
        unfold solveRaw
        rw [parserVertices_request, parseEdges_request])
    have P2 : PolyProgram encodeRequest (fun q : ℚ≥0 => Ratio.encode (q : ℚ))
        (fun req : Input × List Bool =>
          (⟨solveCore c0 (List.range req.1.n) (inputEdges req.1),
            solveCore_nonneg _ _ _⟩ : ℚ≥0)) :=
      P1.recode id (fun _ => rfl) (fun _ => rfl)
    exact ⟨(P2.comp nnratOutput).stock⟩
  · -- the value
    intro G
    obtain ⟨⟨X', hX', hle⟩, hacc⟩ := solveCore_spec c0 good_c0 G
    have hne : (maxcutRelaxationObjective (Ar G) '' {X | IsUnitDiagPSD X}).Nonempty :=
      ⟨_, ⟨1, one_feasible G, rfl⟩⟩
    have hbdd : BddAbove (maxcutRelaxationObjective (Ar G) '' {X | IsUnitDiagPSD X}) :=
      ⟨((Wq G : ℚ) : ℝ), by
        rintro _ ⟨X, hX, rfl⟩
        exact obj_le_total G X hX⟩
    have hLcast : (((⟨solveCore c0 (List.range G.n) (inputEdges G),
        solveCore_nonneg _ _ _⟩ : ℚ≥0) : ℚ≥0) : ℝ) =
        ((solveCore c0 (List.range G.n) (inputEdges G) : ℚ) : ℝ) :=
      (Rat.cast_nnratCast (K := ℝ) (⟨solveCore c0 (List.range G.n) (inputEdges G),
        solveCore_nonneg _ _ _⟩ : ℚ≥0)).symm
    have hWcast : (∑ e, (G.weights e : ℝ)) = ((Wq G : ℚ) : ℝ) := by
      unfold Wq
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact (Rat.cast_nnratCast _).symm
    refine ⟨sSup (maxcutRelaxationObjective (Ar G) '' {X | IsUnitDiagPSD X}), ?_, ?_, ?_⟩
    · exact isLUB_csSup hne hbdd
    · show (((⟨solveCore c0 (List.range G.n) (inputEdges G),
        solveCore_nonneg _ _ _⟩ : ℚ≥0) : ℚ≥0) : ℝ) ≤ _
      rw [hLcast]
      exact hle.trans (le_csSup hbdd ⟨X', hX', rfl⟩)
    · show _ - (((⟨solveCore c0 (List.range G.n) (inputEdges G),
        solveCore_nonneg _ _ _⟩ : ℚ≥0) : ℚ≥0) : ℝ) ≤ _
      rw [hLcast, hWcast]
      have h : sSup (maxcutRelaxationObjective (Ar G) '' {X | IsUnitDiagPSD X}) ≤
          ((solveCore c0 (List.range G.n) (inputEdges G) : ℚ) : ℝ) + ((Wq G : ℚ) : ℝ) / 10000 :=
        csSup_le hne (by
          rintro _ ⟨X, hX, rfl⟩
          exact hacc X hX)
      linarith

end QMCSub


