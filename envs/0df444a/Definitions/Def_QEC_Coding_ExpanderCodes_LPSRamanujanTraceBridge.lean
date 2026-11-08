-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
-- name    : QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:50:27.592208+00:00
-- url     : https://prove2.me/theorems/4e1ac6ea-af80-4747-87e1-768db3d2b65e
-- title:
--   LPSRamanujan Trace Bridge
-- statement:
--   Definitions and structural lemmas for LPSRamanujan Trace Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
noncomputable def lpsCenteredThetaResidual
    (a : LPSResiduePrime p) (n : ℕ) : ℝ :=
  (Fintype.card PSL(2, ZMod a.q) : ℝ) *
      ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
    2 * ((∑ i ∈ Finset.range (n + 1), (p : ℝ) ^ i) -
      (lpsHeckePolynomial ℝ (p : ℝ) n).eval 0)
def HasOptimalCenteredThetaCoefficientBound
    (a : LPSResiduePrime p) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    |lpsCenteredThetaResidual a (2 * n)| ≤
      C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n)
def HasFourSqrtCenteredThetaCoefficientBound
    (a : LPSResiduePrime p) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    |lpsCenteredThetaResidual a (2 * n)| ≤
      C * (((2 * n + 1 : ℕ) : ℝ) * (4 * (p : ℝ)) ^ n)
end QEC.Coding.TannerLiftedProduct


