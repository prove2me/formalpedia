-- Prove2me | Definitions.Def_ArcFlowBPP_IsWalk
-- name    : ArcFlowBPP_IsWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:48.792898+00:00
-- url     : https://prove2.me/theorems/eac0fbe3-99f8-451e-bfca-5f428ae95489
-- title:
--   Directed walk $u \to v$ given by a list of arcs
-- statement:
--   A list of arcs $\pi = (a_1, \dots, a_n)$ is a **directed walk** from $u$ to $v$ if the tail of $a_1$ is $u$, the head of each $a_k$ is the tail of $a_{k+1}$, and the head of $a_n$ is $v$. The empty list is the walk of length zero from $u$ to $u$.
--
--   In an acyclic graph every walk is a path, so the paper's "paths from s to t" are exactly the walks from $s$ to $t$.
--
--   **Formalization Note** Walks are lists of arcs, so two parallel arcs give two different walks.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, §3, p.7 ("paths from s to t")

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, §3, p.7 ("paths from s to t").
`IsWalk G u π v`: the list of arcs `π = [a₁, …, aₙ]` is a directed walk from `u` to `v`, i.e.
`tail a₁ = u`, `head aₖ = tail aₖ₊₁` for every `k`, and `head aₙ = v`; the empty list is the walk
of length zero from `u` to `u`.

**Formalization Note.** A walk is a list of arcs, so parallel arcs give different walks. In an
acyclic graph (`ArcFlowBPP.IsAcyclic`) every walk is a path (no repeated vertex), so the
paper's "paths from s to t" are the walks `IsWalk G G.s π G.t`. -/
def IsWalk {m : ℕ} {V A : Type*} (G : LabelledGraph m V A) : V → List A → V → Prop
  | u, [], v => u = v
  | u, a :: π, v => G.tail a = u ∧ IsWalk G (G.head a) π v

end ArcFlowBPP


