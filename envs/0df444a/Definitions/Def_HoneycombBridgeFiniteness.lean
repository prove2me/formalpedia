-- Prove2me | Definitions.Def_HoneycombBridgeFiniteness
-- name    : HoneycombBridgeFiniteness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.495385+00:00
-- url     : https://prove2.me/theorems/678d449e-561a-43a5-b3f9-c41eedf37b39
-- statement:
--   The file sets up self-avoiding bridge paths in the hexagonal (honeycomb) lattice and defines a finiteness proposition for their weighted sums. Vertices are of two kinds, up(i,j) and down(i,j) with integer coordinates; up(i,j) sits at ((i+j/2), (j+1/3)·√3/2) and down(i,j) at (i+j/2+1/2, (j+2/3)·√3/2), and the layer of a vertex is its integer second index j. An up vertex (i,j) is adjacent to exactly the down vertices (i,j−1), (i,j) and (i−1,j), and adjacency is symmetric and never joins two vertices of the same kind. The critical activity is the constant x_c = 1/(2cos(π/8)). For a height h, a BridgePath is a list of distinct vertices, consecutive ones adjacent, starting at up(0,0), ending at some down(i,h−1), with every vertex in layers 0 through h−1. Its weight is x_c raised to the number of vertices, its first-length weight is that vertex count times the weight, and bridgeMass(h) is the unconditional sum of weights over all bridge paths of height h. A path lies in the log corridor if every vertex has horizontal coordinate of absolute value at most h(log h)²; confined paths are those satisfying this, and confinedMass(h) is the sum of their weights. FiniteBridgeSums is the defined proposition, not an established theorem, that for every h ≥ 1 six families are summable: the weights over all bridge paths, the first-length weights, the first-length weights divided by bridgeMass(h), and the weights, first-length weights, and first-length weights divided by confinedMass(h) over confined paths. Summability here uses Lean's unconditional convention, so it means absolute convergence.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HoneycombBridgeFiniteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HoneycombBridgeFiniteness.lean; bytes 16..2261
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PolynomialVacuumBridge.Corridor

inductive Vertex where
  | up (i j : ℤ)
  | down (i j : ℤ)
  deriving DecidableEq

noncomputable def position : Vertex → ℝ × ℝ
  | .up i j => ((i : ℝ) + (j : ℝ) / 2,
      ((j : ℝ) + 1 / 3) * (Real.sqrt 3 / 2))
  | .down i j => ((i : ℝ) + (j : ℝ) / 2 + 1 / 2,
      ((j : ℝ) + 2 / 3) * (Real.sqrt 3 / 2))

def adjacent : Vertex → Vertex → Prop
  | .up i j, .down k l =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | .down k l, .up i j =>
      (k = i ∧ l = j - 1) ∨ (k = i ∧ l = j) ∨ (k = i - 1 ∧ l = j)
  | _, _ => False

noncomputable def criticalActivity : ℝ := (2 * Real.cos (Real.pi / 8))⁻¹
noncomputable def layer (vertex : Vertex) : ℤ :=
  Vertex.rec (fun _ vertical => vertical) (fun _ vertical => vertical) vertex

structure BridgePath (h : ℕ) where
  vertices : List Vertex
  distinct : vertices.Nodup
  connected : vertices.IsChain adjacent
  source : vertices.head? = some (.up 0 0)
  terminal : ∃ i : ℤ, vertices.getLast? = some (.down i ((h : ℤ) - 1))
  inStrip : ∀ v ∈ vertices, 0 ≤ layer v ∧ layer v < (h : ℤ)

noncomputable def weight {h : ℕ} (p : BridgePath h) : ℝ :=
  criticalActivity ^ p.vertices.length

noncomputable def firstLengthWeight {h : ℕ} (p : BridgePath h) : ℝ :=
  (p.vertices.length : ℝ) * weight p

noncomputable def bridgeMass (h : ℕ) : ℝ := ∑' p : BridgePath h, weight p
noncomputable def InLogCorridor {h : ℕ} (p : BridgePath h) : Prop :=
  ∀ v ∈ p.vertices, |(position v).1| ≤ (h : ℝ) * (Real.log (h : ℝ)) ^ 2

def ConfinedBridgePath (h : ℕ) := {p : BridgePath h // InLogCorridor p}

noncomputable def confinedMass (h : ℕ) : ℝ :=
  ∑' p : ConfinedBridgePath h, weight p.val
def FiniteBridgeSums : Prop :=
  ∀ h : ℕ, 1 ≤ h →
    Summable (weight (h := h)) ∧ Summable (firstLengthWeight (h := h)) ∧
    Summable (fun p : BridgePath h => firstLengthWeight p / bridgeMass h) ∧
    Summable (fun p : ConfinedBridgePath h => weight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) ∧
    Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val / confinedMass h)




end PolynomialVacuumBridge.Corridor
end OAI


