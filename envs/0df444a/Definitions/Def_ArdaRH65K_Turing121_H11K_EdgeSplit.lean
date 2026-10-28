-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
-- name    : ArdaRH65K_Turing121_H11K_EdgeSplit
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:14:47.167586+00:00
-- url     : https://prove2.me/theorems/6677e7ef-4d4f-43eb-bef5-44a1fab3eaed
-- title:
--   H11K EdgeSplit certificate definitions
-- statement:
--   This bundle defines individual horizontal-edge piece checks and the residual edge check. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{H11K.pieceJ},\;\mathtt{H11K.edgeRest}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H11K_EdgeSplit.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
/-  H11K_EdgeSplit.lean -- lane H11K: the Arb4 edge checker `Arb4.edgeOK` assembled from one
    kernel check PER OCTANT PIECE.

    `Arb4.edgeOK` is one Boolean per edge, checked by ONE `decide +kernel`; the Arb4 lane measured its
    memory at about 19 GB for an edge at height 1e4 (25 pieces, EM cut N = 0.3 T).  Here the piece
    conjunct of `edgeOK` is split off:

      * `pieceJ E j`   -- piece `j`: `Arb4.pieceOK` and both breakpoints inside its radius;
      * `edgeRest E`   -- everything else in `edgeOK` (label steps, endpoints, the two endpoint boxes
                          with their corners, the final `π` / `arctan` inequalities);
      * `edgeOK_of_split` -- `edgeRest E = true` and `pieceJ E j = true` for every `j < E.m` give
                          `edgeOK E = true`, hence `Arb4.edgeOK_sound`.

    Each `pieceJ E j` is then one small `decide +kernel` (one evaluator run of N terms).
    Trust: proved from its stated hypotheses; axioms within [propext, Classical.choice, Quot.sound]
    (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


open Complex

namespace H11K

open Arb4 Arb4.Q

/-- Piece `j` of edge `E`: the octant piece check and both of its breakpoints inside its radius. -/
noncomputable def pieceJ (E : EdgeD) (j : ℕ) : Bool :=
  pieceOK E.tn E.tq E.N E.L (E.pc j) && inRad (E.x j) (E.pc j) && inRad (E.x (j + 1)) (E.pc j)

/-- Every conjunct of `Arb4.edgeOK` except the pieces. -/
noncomputable def edgeRest (E : EdgeD) : Bool :=
  Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) && eqB (E.x E.m) (ofInt (-1)) &&
    (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
    eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1)) &&
    boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0 E.qlo0 E.qhi0 &&
    boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1
      E.qlo1 E.qhi1 &&
    finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo &&
    finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi





end H11K


def ArdaRH65K_Turing121_H11K_EdgeSplit : Nat := 0


