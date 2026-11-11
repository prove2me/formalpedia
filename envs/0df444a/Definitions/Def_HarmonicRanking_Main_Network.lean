-- Prove2me | Definitions.Def_HarmonicRanking_Main_Network
-- name    : HarmonicRanking_Main_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:09.875021+00:00
-- url     : https://prove2.me/theorems/cb0aaaa9-03a7-45ed-9c5e-ff7a789d5e09
-- title:
--   The exact finite threshold network
-- statement:
--   For an $m$-level height vector $H$, construct nodes $s,t,X_{ij},Y_{ij}$, where $X$ and $Y$ are distinct grid copies. The objective arcs and their capacities are
--
--   $$
--   s\to Y_{ij}:r_{ji}/m^2,\quad Y_{ij}\to X_{ij}:1/m^2,\quad X_{ij}\to t:r_{ij}/m^2,
--   $$
--   $$
--   X_{ij}\to Y_{ik}:q_{ij}/m^2,\qquad X_{ij}\to Y_{kj}:q_{jk}/m^2\quad(i,j,k\in[m]).
--   $$
--
--   The hard arcs $X_{ij}\to Y_{ij}$, $X_{ij}\to X_{i,j+1}$, and $Y_{i+1,j}\to Y_{ij}$, when defined, each have capacity 2. Every family has distinct records, retaining all parallel and zero-capacity arcs. There are $2m^2+2$ nodes and $2m^3+6m^2-2m$ records. The values $\operatorname{MF}_m(H)$ and $\operatorname{MC}_m(H)$ are computed using the generic arc-indexed flow and cut interface. This is the source's ordinary finite-capacity version of its implication network; no threshold-game equality is built into its definition.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 17–18, Eqs. (34)–(36) and Proposition 5.1 setup

import Definitions.Def_HarmonicRanking_Main_ArcNetwork
import Definitions.Def_HarmonicRanking_Main_StepProfile

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

/-- s,t and two distinct grid copies. -/
inductive StepNode (m : ℕ) where
  | source
  | sink
  | X (i j : Fin m)
  | Y (i j : Fin m)
  deriving DecidableEq, Fintype

/-- Each constructor is an arc record, including all parallel and zero arcs. -/
inductive StepArc (m : ℕ) where
  | sourceY (i j : Fin m)
  | YX (i j : Fin m)
  | Xsink (i j : Fin m)
  | fanRow (i j k : Fin m)
  | fanCol (i j k : Fin m)
  | hardXY (i j : Fin m)
  | hardRow (i : Fin m) (j : Fin (m-1))
  | hardCol (i : Fin (m-1)) (j : Fin m)
  deriving DecidableEq, Fintype

def previous {m : ℕ} (i : Fin (m-1)) : Fin m := ⟨i.val, by omega⟩
def next {m : ℕ} (i : Fin (m-1)) : Fin m := ⟨i.val+1, by omega⟩

def stepDigraph (m : ℕ) : CombOpt.MinCostFlow.Digraph (StepNode m) (StepArc m) where
  tail := fun e => match e with
    | .sourceY _ _ => .source
    | .YX i j => .Y i j
    | .Xsink i j => .X i j
    | .fanRow i j _ => .X i j
    | .fanCol i j _ => .X i j
    | .hardXY i j => .X i j
    | .hardRow i j => .X i (previous j)
    | .hardCol i j => .Y (next i) j
  head := fun e => match e with
    | .sourceY i j => .Y i j
    | .YX i j => .X i j
    | .Xsink _ _ => .sink
    | .fanRow i _ k => .Y i k
    | .fanCol _ j k => .Y k j
    | .hardXY i j => .Y i j
    | .hardRow i j => .X i (next j)
    | .hardCol i j => .Y (previous i) j

def stepCapacity {m : ℕ} (H : Fin m → ℝ) (e : StepArc m) : ℝ :=
  match e with
  | .sourceY i j => rCoeff H j i / (m : ℝ)^2
  | .YX _ _ => 1 / (m : ℝ)^2
  | .Xsink i j => rCoeff H i j / (m : ℝ)^2
  | .fanRow i j _ => q H i j / (m : ℝ)^2
  | .fanCol _ j k => q H j k / (m : ℝ)^2
  | .hardXY _ _ => 2
  | .hardRow _ _ => 2
  | .hardCol _ _ => 2

def stepNetwork {m : ℕ} (H : Fin m → ℝ) : ArcNetwork (StepNode m) (StepArc m) where
  graph := stepDigraph m
  source := .source
  sink := .sink
  capacity := stepCapacity H

def MF {m : ℕ} (H : Fin m → ℝ) : ℝ := maxFlow (stepNetwork H)
def MC {m : ℕ} (H : Fin m → ℝ) : ℝ := minCut (stepNetwork H)

end HarmonicRanking.Main


