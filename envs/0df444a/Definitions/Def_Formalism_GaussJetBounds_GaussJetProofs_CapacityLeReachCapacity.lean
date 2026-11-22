-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
-- name    : Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:14.487867+00:00
-- url     : https://prove2.me/theorems/7615f1a3-0d65-4fcd-b58e-d7c21767dcbd
-- title:
--   Capacity Le Reach Capacity
-- statement:
--   Definitions and structural lemmas for Capacity Le Reach Capacity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CapacityLeReachCapacity.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def asmA_f (l : ℕ) (A : ℝ) (cap : ℕ → ℝ) (D : ℕ∞) (e : ℕ) : ℝ :=
  if Odd e ∧ (e : ℕ∞) < D then max (A / (l : ℝ) ^ e - cap e) 0
  else if Odd e ∧ D < (e : ℕ∞) then A / (l : ℝ) ^ e else 0
def asmA_g (l : ℕ) (A : ℝ) (e : ℕ) : ℝ := if Odd e then A / (l : ℝ) ^ e else 0
def asmA_cost (l : ℕ) {d : ℕ} (eps : ZMod d → ℝ) : Option (ZMod d × ℤ) → ℝ
  | none => 0
  | some (s, j) =>
      if 0 < j then max (1 - (l : ℝ) ^ j.toNat * eps s) 0 else ((l : ℝ) ^ (-j).toNat)⁻¹
end Formalism.DworkPowerSeriesWeights


