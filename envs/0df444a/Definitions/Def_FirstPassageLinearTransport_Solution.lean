-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Solution
-- name    : FirstPassageLinearTransport_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:32:18.636364+00:00
-- url     : https://prove2.me/theorems/8495d3bd-3700-5919-8b7e-aedd4aca064f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/Solution.lean

import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
namespace CollatzFirstPassage
open Filter
open scoped BigOperators Real Topology
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
def orbit (k n : ℕ) : ℕ := (shortcut^[k]) n
def parityBit (n i : ℕ) : Fin 2 :=
  ⟨orbit i n % 2, Nat.mod_lt _ (by omega)⟩
def oddCount (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (parityBit n i : ℕ)
def rawCollatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1
def rawOrbit (i n : ℕ) : ℕ := (rawCollatz^[i]) n
def rawTime (n k : ℕ) : ℕ := k + oddCount n k
noncomputable def badCount (S : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n => n ∉ S).card
def NaturalDensityOne (S : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (badCount S X : ℝ) / (X : ℝ)) atTop (nhds 0)
noncomputable def logTwoThree : ℝ := Real.log 3 / Real.log 2
noncomputable def a0 : ℝ := logTwoThree / 2
noncomputable def driftGap : ℝ := 1 - a0
noncomputable def logThreeTwo : ℝ := Real.log 2 / Real.log 3
noncomputable def binaryEntropyBaseTwo (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2
noncomputable def kappaStar : ℝ :=
  1 - binaryEntropyBaseTwo logThreeTwo
noncomputable def firstPassageCriticalExponent : ℝ :=
  1 / (2 * kappaStar)
noncomputable def fixedPolylogClockCritical : ℝ :=
  1 / (driftGap * Real.log 2)
noncomputable def fixedSharpEndpointMargin (A : ℝ) : ℝ :=
  kappaStar * A - 1 / 2
noncomputable def shortcutLogDeviation (n j : ℕ) : ℝ :=
  Real.log (orbit j n) - Real.log n +
    driftGap * (j : ℝ) * Real.log 2
noncomputable def rawLogDeviation (n i : ℕ) : ℝ :=
  Real.log (rawOrbit i n) - Real.log n +
    (2 * driftGap / 3) * (i : ℝ) * Real.log 2
noncomputable def shortcutFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {j : ℕ | (orbit j n : ℝ) ≤ z}
noncomputable def rawFirstPassageTime (n : ℕ) (z : ℝ) : ℕ :=
  sInf {i : ℕ | (rawOrbit i n : ℝ) ≤ z}
def HasVariableTargetHeightWitness
    (f u : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k : ℕ,
    (orbit k n : ℝ) ≤ f n ∧
      ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ u n * (n : ℝ)
noncomputable def variableTargetHeightFailureCount
    (f u : ℕ → ℝ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter fun n =>
    ¬HasVariableTargetHeightWitness f u n).card
noncomputable def fixedJointPolylogTarget (C A : ℝ) (n : ℕ) : ℝ :=
  C * (Real.log n) ^ A
noncomputable def fixedJointPolylogHeight (q : ℝ) (n : ℕ) : ℝ :=
  (((Nat.log 2 n : ℕ) : ℝ) + 2) ^ q
end CollatzFirstPassage


