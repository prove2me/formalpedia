-- Prove2me | Definitions.Def_TriFreeEst247_Main_Score
-- name    : TriFreeEst247_Main_Score
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:01:12.211207+00:00
-- url     : https://prove2.me/theorems/aa970950-3c35-46cb-a045-f93bed30782b
-- title:
--   The penalized deletion score and its minimum
-- statement:
--   Fix a graph $G$ on $n$ vertices. For an edge set $F$, let $e(F)=|F|/n^2$ and $t(F)=\operatorname{Tri}(F)/n^3$, where triangles are counted in the subgraph with edge set $F$. Every normalization uses the original order $n$. For a real weight $\lambda\ge0$ and $D\subseteq E(G)$, define
--
--   $$J_\lambda(D)=e(D)+\lambda t(E(G)\setminus D),\qquad \mathrm{OPT}_\lambda(G)=\min_{D\subseteq E(G)}J_\lambda(D).$$
--
--   This finite, nonempty minimization balances deleted edges against surviving triangles and supplies the optimization problem used in the compression statements.
--
--   **Formalization Note** The real infimum is a genuine minimum over a finite powerset. Empty edge sets have density zero, and at $n=0$ the total helpers return zero. Theorems use only the source's positive graph orders and nonnegative weights.
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.6–7, §2, definition of Jλ and OPTλ

import Mathlib
import Definitions.Def_TriFreeEst247_Main_GraphModel

noncomputable section

namespace TriFreeEst247.Main

/-- Section 2, pp.6--7: all normalizations use the original graph order n. -/
def edgeDensity {n : ℕ} (F : EdgeSet n) : ℝ := (F.card : ℝ) / (n : ℝ)^2

def edgeGraph {n : ℕ} (F : EdgeSet n) : Graph n := SimpleGraph.fromEdgeSet (F : Set _)

def triangleDensity {n : ℕ} (F : EdgeSet n) : ℝ :=
  (triangles (edgeGraph F) : ℝ) / (n : ℝ)^3

def score {n : ℕ} (G : Graph n) (lam : ℝ) (D : EdgeSet n) : ℝ :=
  edgeDensity D + lam * triangleDensity (edges G \ D)

/-- Minimum over the finite nonempty powerset of the graph's edge set. -/
def scoreOpt {n : ℕ} (G : Graph n) (lam : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ D : EdgeSet n, D ⊆ edges G ∧ r = score G lam D}

end TriFreeEst247.Main


