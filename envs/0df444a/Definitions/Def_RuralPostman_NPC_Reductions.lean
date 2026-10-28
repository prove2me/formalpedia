-- Prove2me | Definitions.Def_RuralPostman_NPC_Reductions
-- name    : RuralPostman_NPC_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:29.185635+00:00
-- url     : https://prove2.me/theorems/c5d870f1-b343-4c77-82fd-8d5856579862
-- title:
--   §2, pp. 5–6 — the undirected and directed constructions from HAMILTON CIRCUIT to RURAL POSTMAN
-- statement:
--   Given a graph $H=(V,E)$ with $V=\{0,\dots,v-1\}$, the proof of the Theorem builds a rural postman instance on the node set $N=V\times\{0,1\}$.
--
--   **Undirected construction** (pp. 5–6), for an undirected $H$:
--   $$
--   \begin{aligned}
--   A &= \{(\langle s,0\rangle,\langle s,1\rangle)\mid s\in V\}\cup\{(\langle s,0\rangle,\langle t,0\rangle)\mid \{s,t\}\in E\},\\
--   R &= \{(\langle s,0\rangle,\langle s,1\rangle)\mid s\in V\},\\
--   w(\langle s,0\rangle,\langle s,1\rangle) &= 0,\qquad w(\langle s,0\rangle,\langle t,0\rangle)=1,\qquad k=v .
--   \end{aligned}
--   $$
--   Each edge of $H$ contributes one arc.
--
--   **Directed construction** (p. 6), for a directed $H$:
--   $$
--   \begin{aligned}
--   A &= \{(\langle s,0\rangle,\langle s,1\rangle),(\langle s,1\rangle,\langle s,0\rangle)\mid s\in V\}\cup\{(\langle s,0\rangle,\langle t,0\rangle)\mid (s,t)\in E\},\\
--   R &= \{(\langle s,0\rangle,\langle s,1\rangle)\mid s\in V\},\\
--   w(\langle s,0\rangle,\langle s,1\rangle) &= w(\langle s,1\rangle,\langle s,0\rangle)=0,\qquad w(\langle s,0\rangle,\langle t,0\rangle)=1,\qquad k=v .
--   \end{aligned}
--   $$
--
--   The required arcs are pendant arcs of weight $0$ hanging from the copies $\langle s,0\rangle$ of the vertices of $H$; the arcs of weight $1$ copy the edges of $H$. With threshold $k=v$ these instances encode HAMILTON CIRCUIT.
--
--   **Formalization Note** $V$ is `Fin v` and $N$ is `Fin (v + v)`, with $\langle s,0\rangle$ = `Fin.castAdd v s` and $\langle s,1\rangle$ = `Fin.natAdd v s`. The graph $H$ is a Boolean adjacency matrix `adj`. The arc list is fixed: in the undirected case first the $v$ pendant arcs (in the order of $s$), then one arc $(\langle s,0\rangle,\langle t,0\rangle)$ for each pair $s<t$ with `adj s t = true`; in the directed case, for each $s$ the pendant arc and its reverse, then one arc for each pair $(s,t)$ with `adj s t = true` (loops of $H$ included).
-- source:
--   Lenstra, Rinnooy Kan, On general routing problems, Mathematisch Centrum report BW 42/74 (December 1974), pp. 5–6, §2, proof of the Theorem (the two constructions, "N = V × {0,1}, … k = v")

import Mathlib
import Definitions.Def_RuralPostman_NPC_Instances

namespace RuralPostman.NPC

/-! # The two constructions of §2 (pp. 5–6)

From a graph `H = (V, E)` on `V = Fin v`, the rural postman instance on `N = V × {0,1}`, encoded
as `Fin (v + v)`: node `⟨s,0⟩` is `Fin.castAdd v s` and node `⟨s,1⟩` is `Fin.natAdd v s`. -/

/-- The undirected construction (p. 5–6): for each `s ∈ V` the required arc `(⟨s,0⟩, ⟨s,1⟩)` of
weight `0`; for each edge `{s, t}` of `H` (listed once, as `s < t` with `adj s t = true`) the
non-required arc `(⟨s,0⟩, ⟨t,0⟩)` of weight `1`; and `k = v`. -/
def urpOfGraph {v : ℕ} (adj : Fin v → Fin v → Bool) : RPInstance where
  n := v + v
  arcs :=
    (List.finRange v).map (fun s => (Fin.castAdd v s, Fin.natAdd v s, 0, true)) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => decide (s < t) && adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))
  k := v

/-- The directed construction (p. 6): for each `s ∈ V` the required arc `(⟨s,0⟩, ⟨s,1⟩)` and the
non-required arc `(⟨s,1⟩, ⟨s,0⟩)`, both of weight `0`; for each arc `(s, t)` of `H`
(`adj s t = true`) the non-required arc `(⟨s,0⟩, ⟨t,0⟩)` of weight `1`; and `k = v`. -/
def drpOfGraph {v : ℕ} (adj : Fin v → Fin v → Bool) : RPInstance where
  n := v + v
  arcs :=
    (List.finRange v).flatMap (fun s =>
      [(Fin.castAdd v s, Fin.natAdd v s, 0, true), (Fin.natAdd v s, Fin.castAdd v s, 0, false)]) ++
    (List.finRange v).flatMap (fun s =>
      ((List.finRange v).filter (fun t => adj s t)).map
        (fun t => (Fin.castAdd v s, Fin.castAdd v t, 1, false)))
  k := v

end RuralPostman.NPC


