-- Prove2me | Definitions.Def_MinimaxAltRegret_Main_LowerConstruction
-- name    : MinimaxAltRegret_Main_LowerConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:48.746745+00:00
-- url     : https://prove2.me/theorems/baeb50e1-88aa-48b2-a097-51de5c0be4ef
-- title:
--   Oblivious environments, the disk, and explicit lower constants
-- statement:
--   A finite environment assigns nonnegative weights of total mass one to complete loss sequences. Its outcome is selected before interaction, independently of the learner's seed. The unit disk is D={x in R^2: norm(x)<=1}. Define the universal constants
--
--   $$c_0=\frac1{80\log65536},\qquad c=\min\left\{\frac{c_0}{6},\frac14\right\}.$$
--
--   For dimension d and horizon T, put m=floor(d/2). The hard domain is the product of m unit disks when T>=5m, with an unused interval [-1,1] in odd dimension. When T<5m it is the cube [-1,1]^d. These sets and constants are computed from d,T before the learner is selected.
--
--   The objects support Lemma B.1 and Theorem 4.1. The finite-environment record contains only a probability distribution and sequences, with no lower-bound property. Constants are fixed independently of all instances.
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 16 / PDF p. 17, Lemma B.1 and its proof, Eqs. (26), (29), (40)--(43), printed pp. 16--20 / PDF pp. 17--21; Theorem 4.1 proof, printed pp. 20--22 / PDF pp. 21--23; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Continuous

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

/-- Explicit constants obtained in (40)--(43) and the two regimes of Theorem 4.1. -/
def diskConstant : ℝ := 1 / (80 * Real.log 65536)
def ocoConstant : ℝ := min (diskConstant/6) (1/4)
def unitDisk : Set (Point 2) := {x | ‖x‖ ≤ 1}

/-- Total coordinate access; theorem uses have 0 <= k < d. -/
def coordinate {d : ℕ} (x : Point d) (k : ℕ) : ℝ :=
  if h : k < d then x ⟨k,h⟩ else 0

/-- The two source regimes, including the unused interval in odd dimension. -/
def hardDomain (d T : ℕ) : Set (Point d) :=
  if 5*(d/2) ≤ T then
    {x | (∀ k < d/2, (coordinate x (2*k))^2 + (coordinate x (2*k+1))^2 ≤ 1) ∧
      (d % 2 = 1 → |coordinate x (d-1)| ≤ 1)}
  else {x | ∀ i, |x i| ≤ 1}

/-- A finite oblivious environment: its entire sequence is sampled before play.
This general finite-distribution interface is independent of any learning guarantee. -/
structure FiniteEnvironment (L : Type) (N : ℕ) where
  weight : Fin N → ℝ
  nonnegative : ∀ j, 0 ≤ weight j
  mass_one : ∑ j, weight j = 1
  sequence : Fin N → ℕ → L

end MinimaxAltRegret.Main


