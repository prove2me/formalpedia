-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Pruning
-- name    : SparsestCutOracle_Main_Pruning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:57.583939+00:00
-- url     : https://prove2.me/theorems/4d62ed46-8692-4b1e-8a39-5e2d39d37452
-- title:
--   Edge deletions and the two-call SparsePrune trace
-- statement:
--   Deleted edges are specified by their positions in the input list, so marked parallel edges remain distinguishable. Put $W=\operatorname{cap}(F)$, $H=G\setminus F$, and let $d_F(v)$ be the incident deleted capacity at $v$.
--
--   SparsePrune makes precisely the two calls
--
--   $$\operatorname{FairCutFlow}(H,d_F,\psi/4,2),\qquad
--   \operatorname{FairCutFlow}(H,\psi|_U/24,\psi|_{V\setminus U}/24,2),$$
--
--   and returns the second cut $P$. A trace records both valid pairs. Its output predicate retains the bound $\psi(P)\le48W\le\psi(V)/2$, induced expansion $1/72$, and sparsity $1/12$. The input supplies deletion flags rather than precomputed incident volumes.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 37–38, Theorem 8 and its stated algorithm

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

/-- Deletion refers to edge-list positions, so parallel artificial edges can be deleted separately. -/
def deleteEdges {n : ℕ} (G : Graph n) (F : Finset (Fin G.length)) : Graph n :=
  ((List.finRange G.length).filter fun i => i ∉ F).map fun i => G[i.val]

def deletedCapacity {n : ℕ} (G : Graph n) (F : Finset (Fin G.length)) : ℝ :=
  ∑ i ∈ F, (G[i.val].capacity : ℝ)

def deletionDemand {n : ℕ} (G : Graph n) (F : Finset (Fin G.length)) (v : Fin n) : ℝ :=
  ∑ i ∈ F, if G[i.val].u = v ∨ G[i.val].v = v then (G[i.val].capacity : ℝ) else 0

/-- The first and second calls of SparsePrune; all choices of valid fair-flow outputs are allowed. -/
def SparsePruneTrace {n : ℕ} (G : Graph n) (ψ : Fin n → ℝ) (F : Finset (Fin G.length))
    (U : Finset (Fin n)) (f₁ : Flow n) (P : Finset (Fin n)) (f₂ : Flow n) : Prop :=
  let H := (deleteEdges G F).toWGraph
  FairPair H (deletionDemand G F) (fun v => ψ v / 4) 2 U f₁ ∧
  FairPair H (fun v => if v ∈ U then ψ v / 24 else 0)
    (fun v => if v ∉ U then ψ v / 24 else 0) 2 P f₂

def Pruned {n : ℕ} (G : Graph n) (ψ : Fin n → ℝ) (F : Finset (Fin G.length))
    (P : Finset (Fin n)) : Prop :=
  mass ψ P ≤ 48 * deletedCapacity G F ∧
  48 * deletedCapacity G F ≤ totalWeight ψ / 2 ∧
  ExpandingOn (deleteEdges G F).toWGraph ψ Pᶜ (1 / 72) ∧
  cut (deleteEdges G F).toWGraph P Pᶜ ≤ (1 / 12 : ℝ) * mass ψ P

/-- The pruning input includes the deletion flags and no precomputed incident volumes. -/
noncomputable def pruneInput {n : ℕ} (G : Graph n) (ψ : Fin n → ℝ)
    (F : Finset (Fin G.length)) : State :=
  init (graphInts G ++ ((List.finRange G.length).map fun i => if i ∈ F then 1 else 0))
    (graphReals G ψ [])

end SparsestCutOracle.Main


