-- Prove2me | Definitions.Def_CutwidthCircuitLB_cutSize
-- name    : CutwidthCircuitLB_cutSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:31.04557+00:00
-- url     : https://prove2.me/theorems/b4d1ff0e-bb66-47de-8024-da8457e631fd
-- title:
--   Number of edges across a prefix cut of a vertex ordering
-- statement:
--   For a multigraph on the vertices $v_1, \dots, v_N$ with edge multiset $E$, an ordering $\pi$ of the vertices and $0 \le i \le N$, the **cut size** is the number of edges (with multiplicity) across the cut
--   $$
--   \big(\{v_{\pi(1)}, \dots, v_{\pi(i)}\},\ \{v_{\pi(i+1)}, \dots, v_{\pi(N)}\}\big),
--   $$
--   i.e. with exactly one end among the first $i$ vertices of the ordering. A loop never crosses a cut.
--
--   **Formalization Note** Positions are $0$-based: $\pi(j)$ is the vertex at position $j$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.4, p.8

import Mathlib

namespace CutwidthCircuitLB

/-- The number of edges across the cut `({v_π(1), …, v_π(i)}, {v_π(i+1), …, v_π(N)})` of the vertex
ordering `π` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.4, p.8): the edges of the multiset `E` with exactly one end among
the first `i` vertices of the ordering, counted with multiplicity.

**Formalization Note** `π j` is the vertex at (0-based) position `j`, so `v` is among the first `i`
vertices iff `π⁻¹ v < i`. A loop never crosses a cut. -/
def cutSize {N : ℕ} (E : Multiset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) (i : ℕ) : ℕ :=
  E.countP (fun e => Sym2.lift ⟨fun a b => xor (decide ((π.symm a).val < i))
    (decide ((π.symm b).val < i)), fun _ _ => Bool.xor_comm _ _⟩ e = true)

end CutwidthCircuitLB


