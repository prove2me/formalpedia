-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalNumeric
-- name    : Sensitivity214439_Phase0_Solutions_UnaryWarmGlobalNumeric
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:43.993861+00:00
-- url     : https://prove2.me/theorems/12d61b73-3657-4609-a1ce-a3cc35233103
-- title:
--   Warm unary price validity and the six-case maximum
-- statement:
--   Warm prices consist of low, target, marked-target, external, and internal prices and a loss price for each old height. The fast total local fee sums the own fee and closed-form guard fees. Target potential permits either legal destination guards or some feasible guard replacement; hard potential requires a feasible replacement of a guard above the hard cutoff.
--
--   Local price validity bounds low-state total fees, high target and marked-target fees, each hard-guard fee by its height loss price, and internal loss prices when hard potential holds. The global scalar bound is the maximum of
--   $$
--   2659p_{\rm low},\quad
--   1329p_{\rm low}+p_{\rm target},\quad
--   664p_{\rm low}+p_{\rm markedTarget},\quad
--   664p_{\rm low}+p_{\rm external},
--   $$
--   $$
--   344p_{\rm low}+p_{\rm internal}+p_{\rm external},\qquad
--   344p_{\rm low}+3p_{\rm internal}.
--   $$
--   The checker verifies local prices for every enumerated state rejecting the weak rank, bounds every height loss price by the external price, and bounds this six-case maximum by the proposed output value.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryWarmGlobalNumeric.lean lines 8–61; SHA256 56c557b5554aa91a51c52bb8b18c58e44295e1397e246614fd43d2e6d3d4690b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainFast
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGainNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Range

namespace SensitivityUnaryGainNumeric
end SensitivityUnaryGainNumeric
namespace SensitivityUnaryWarmGlobalNumeric
end SensitivityUnaryWarmGlobalNumeric



/-! Exact local prices for the six warm-unary global population cases. -/
namespace SensitivityUnaryWarmGlobalNumeric

open SensitivityUnaryGainNumeric

structure Prices where
  low : ℕ
  target : ℕ
  markedTarget : ℕ
  external : ℕ
  internal : ℕ
  loss : ℕ → ℕ

def totalFeeFast (r : Recipe) (input : Array ℕ) (i j : Fin 12) (s : State) : ℕ :=
  ownFee r input j s + (s.guards.map (guardFeeFast r input i j s)).sum



def targetPotential (r : Recipe) (i j : Fin 12) (s : State) : Prop :=
  legal r j (count (r.soft j) s.guards) (count (r.hard j) s.guards) ∨
    (s.guards.any fun old => decide (guardPossible r i j s old)) = true

instance (r : Recipe) (i j : Fin 12) (s : State) : Decidable (targetPotential r i j s) := by
  unfold targetPotential
  infer_instance

def hardPotential (r : Recipe) (i j : Fin 12) (s : State) : Prop :=
  (s.guards.any fun old => decide (r.hard j < old ∧ guardPossible r i j s old)) = true

instance (r : Recipe) (i j : Fin 12) (s : State) : Decidable (hardPotential r i j s) := by
  unfold hardPotential
  infer_instance

def localPricesValid (r : Recipe) (input : Array ℕ) (i j : Fin 12) (p : Prices) (s : State) : Prop :=
  (s.height ≤ r.hard j → totalFeeFast r input i j s ≤ p.low) ∧
  (r.hard j < s.height → count (r.hard j) s.guards = 0 → targetPotential r i j s →
    totalFeeFast r input i j s ≤ p.target ∧
      totalFeeFast r input i j s + p.loss s.height ≤ p.markedTarget) ∧
  (s.guards.all fun old => decide (r.hard j < old →
    guardFeeFast r input i j s old ≤ p.loss old)) = true ∧
  (hardPotential r i j s → p.loss s.height ≤ p.internal)

instance (r : Recipe) (input : Array ℕ) (i j : Fin 12) (p : Prices) (s : State) :
    Decidable (localPricesValid r input i j p s) := by
  unfold localPricesValid
  infer_instance

def sixBound (p : Prices) : ℕ :=
  max (2659*p.low) (max (1329*p.low+p.target) (max (664*p.low+p.markedTarget)
    (max (664*p.low+p.external) (max (344*p.low+p.internal+p.external) (344*p.low+3*p.internal)))))

def check (r : Recipe) (input : Array ℕ) (i j : Fin 12) (p : Prices) (bound : ℕ) : Bool :=
  ((warmStates r j).all (fun s => decide (¬ acceptsState r i s → localPricesValid r input i j p s)) &&
    (List.range 13).all (fun h => decide (p.loss h ≤ p.external))) && decide (sixBound p ≤ bound)












end SensitivityUnaryWarmGlobalNumeric


