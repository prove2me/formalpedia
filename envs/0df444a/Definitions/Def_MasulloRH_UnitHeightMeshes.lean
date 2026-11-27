-- Prove2me | Definitions.Def_MasulloRH_UnitHeightMeshes
-- name    : MasulloRH_UnitHeightMeshes
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-27T02:56:16.815167+00:00
-- url     : https://prove2.me/theorems/2efcf8cb-4bae-5c9d-859e-542c6f670ba8
-- title:
--   Rational uniform meshes for the Masullo unit-height Euler–Maclaurin balls
-- statement:
--   Subdivide both sides of each Masullo unit-height rectangle into m equal parts. Each grid node is a rational complex center. Its order-one certificate uses truncation N=m, radius 2/m, the original derivative budget, and the original explicit rational remainder. The interior tests omit nodes in a logarithmic strip at the right edge.
-- source:
--   For the existing Masullo unit-height Euler–Maclaurin ball obligation https://prove2.me/theorems/458479ec-80ed-41ca-9e08-9f4753b887b0 .

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MasulloRH.UnitHeightMeshes
open Set
noncomputable section

def margin (k : ℕ) : ℝ := 1 / ((k : ℝ) + 3)
def rect (n k : ℕ) : Set ℂ :=
  Complex.reProdIm (Icc (1/2 + margin k) 1)
    (Icc ((100000:ℝ) + n + margin k) ((100000:ℝ) + n + 1))
def derivBudget (n : ℕ) : ℚ := 16 * (100003 + n)
def rad (m : ℕ) : ℚ := 2 / (m:ℚ)
def emError (n K N : ℕ) : ℚ :=
  ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
    (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
def rationalCenter (p : ℚ × ℚ) : ℂ := ⟨(p.1:ℝ), (p.2:ℝ)⟩
def node (n k m i j : ℕ) : ℚ × ℚ :=
  let d : ℚ := 1 / ((k:ℚ)+3)
  (1/2+d+(1/2-d)*((i:ℚ)/m),100000+n+d+(1-d)*((j:ℚ)/m))
def passes (n k m i j : ℕ) : Prop :=
  ((derivBudget n * rad m + emError n 1 m : ℚ) : ℝ) <
    ‖ZetaReflection.EMHigh.emFinite 1 (rationalCenter (node n k m i j)) m‖
def cert (n k : ℕ) (p : ℚ × ℚ) (r : ℚ) : Prop :=
  rationalCenter p ∈ rect n k ∧ ∃ K N : ℕ, 1 ≤ K ∧ 1 ≤ N ∧
    ((derivBudget n * r + emError n K N : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K (rationalCenter p) N‖
def covered (n k : ℕ) (s : ℂ) : Prop :=
  ∃ p r, cert n k p r ∧ dist s (rationalCenter p) < (r:ℝ)
def cutoff (n : ℕ) (c : ℝ) : ℝ := 1 - c / Real.log ((100000:ℝ)+n+3)
def innerMeshes : Prop :=
  ∀ c : ℝ, 0 < c → ∀ n k : ℕ, ∃ m : ℕ, 0 < m ∧
    ∀ i ≤ m, ∀ j ≤ m, (rationalCenter (node n k m i j)).re < cutoff n c → passes n k m i j

end
end MasulloRH.UnitHeightMeshes


