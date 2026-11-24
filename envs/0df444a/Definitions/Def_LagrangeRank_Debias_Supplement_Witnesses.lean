-- Prove2me | Definitions.Def_LagrangeRank_Debias_Supplement_Witnesses
-- name    : LagrangeRank_Debias_Supplement_Witnesses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:48:16.479689+00:00
-- url     : https://prove2.me/theorems/bd43d3ca-efd4-4a65-a833-76a58f820250
-- title:
--   Explicit bounded-range witnesses for source defects in general ranking power and sparse-graph inference
-- statement:
--   For $n=t+4$ and $L=n^{10}$, define two centered score vectors by centering
--   $$\theta^+=(0,\varepsilon,-\varepsilon,-1,-2,\ldots,-2),\qquad
--   \theta^-=(0,-\varepsilon,\varepsilon,-1,-2,\ldots,-2),\quad\varepsilon=n^{-20}.$$
--   For item 0, let $R_0$ consist of every predecessor set except $\{2\}$ and $\{1,2,3\}$. This is exactly a ranking property of Definition 2.3. The first score is an alternative, the second a null; the only legal swap at the alternative is with item 3, so its legal-pair signal is 1. Yet the two full BTL data laws on the complete graph have total variation tending to zero. For the family witness every other property is empty.
--
--   A separate sparse witness has $p=n^{-3}$ and centered scores obtained from $(1,0,\ldots,0)$. Both rates printed in Theorem 3.3 vanish, although the graph is empty with probability tending to one. The top-one signal remains 1. `AsymptoticUpper` expresses $\limsup u_t\le a$ using eventual $a+\epsilon$ bounds. These definitions expose counterexamples; they assert no concentration or test-validity theorem. Their mathematical justifications and source anchors are retained in DISPROOF.md.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 10, Definition 2.3; p. 19, Definition 3.2; p. 56, first inclusion; pp. 57–58, Theorem E.1

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Ranking

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

/-- An epsilon formulation of limsup ≤ a; no real supremum over an empty family. -/
def AsymptoticUpper (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, u t ≤ a + ε

def witnessN (t : ℕ) : ℕ := t + 4
def witnessL (t : ℕ) : ℕ := (witnessN t)^10
def item0 (t : ℕ) : Fin (witnessN t) := ⟨0, by unfold witnessN; omega⟩
def item1 (t : ℕ) : Fin (witnessN t) := ⟨1, by unfold witnessN; omega⟩
noncomputable def sparseP (t : ℕ) : unitInterval :=
  ⟨1 / ((witnessN t : ℕ) : ℝ)^3, by
    have h : (1 : ℝ) ≤ witnessN t := by exact_mod_cast (show 1 ≤ witnessN t by unfold witnessN; omega)
    exact ⟨by positivity, (div_le_one (by positivity)).2 (one_le_pow₀ h)⟩⟩
noncomputable def nearScores (t : ℕ) (alt : Bool) : Vec (witnessN t) :=
  center (fun i => if i.val = 0 then 0
    else if i.val = 1 then (if alt then 1 else -1) / (witnessN t : ℝ)^20
    else if i.val = 2 then (if alt then -1 else 1) / (witnessN t : ℝ)^20
    else if i.val = 3 then -1 else -2)

/-- A legal property in Definition 2.3: all predecessor sets except {2} and {1,2,3}.
Both excluded classes are possible; the property is neither empty nor universal. -/
def witnessProperty (t : ℕ) : Set (Ranking (witnessN t)) :=
  {γ | predecessors γ (item0 t) ≠ {i | i.val = 2} ∧
       predecessors γ (item0 t) ≠ {i | i.val = 1 ∨ i.val = 2 ∨ i.val = 3}}
def witnessFamily (t : ℕ) (i : Fin (witnessN t)) : Set (Ranking (witnessN t)) :=
  if i.val = 0 then witnessProperty t else ∅
noncomputable def nearProb (t : ℕ) (alt : Bool) (A : Set (Data (witnessN t) (witnessL t))) : ℝ :=
  (dataLaw (witnessL t) 1 (nearScores t alt) A).toReal

/-- A fixed, bounded-range top-one alternative. Its gap to the second order statistic is 1. -/
noncomputable def sparseScores (t : ℕ) : Vec (witnessN t) :=
  center (fun i => if i.val = 0 then 1 else 0)
noncomputable def sparseRejectProb (t : ℕ) : ℝ :=
  (dataLaw (witnessL t) (sparseP t) (sparseScores t)
    {s | topReject (sparseP t) 1 (1/4) (item0 t) (item1 t) s}).toReal

end LagrangeRank.Debias.Supplement


