-- Prove2me | Definitions.Def_PathORAMCap_overflowAux
-- name    : PathORAMCap_overflowAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:05.580799+00:00
-- url     : https://prove2.me/theorems/be48cc87-b4e1-40fc-bc73-24fbcdb6f8d5
-- title:
--   Upward packing $D^{(Z)}$ of node loads with bucket capacity $Z$
-- statement:
--   For a nonnegative load vector $A=(A_v)_v$ on the nodes of a binary tree, **upward packing** with capacity $Z$ places $A_v$ blocks at each node $v$ and works up from the leaves: each bucket keeps at most $Z$ of its incoming blocks and passes the excess to its parent. The excess sent upward from $v$ is
--
--   $$D^{(Z)}_v(A)=\bigl(A_v+D^{(Z)}_{v0}(A)+D^{(Z)}_{v1}(A)-Z\bigr)^+,\qquad x^+=\max\{x,0\},$$
--
--   where missing children contribute zero, and the root overflow is $D^{(Z)}(A)=D^{(Z)}_\varepsilon(A)$.
--
--   The module defines the overflow above a node $v$ of the loads on the $h$ bucket levels starting at $v$, and the root overflow $D^{(Z)}(A)$ of integer loads on the depth-$L$ tree (its $L+1$ levels). The same function evaluates the local $H$-level trees of §5.
--
--   **Formalization Note** The recursion is on the number $h$ of bucket levels; $h=0$ is the empty tree with overflow $0$, so the last level has no children. Loads are real (integer loads enter by the cast), as in the paper, which also uses real loads.
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), (20) p.16 (PDF p.19); (40) p.37 (PDF p.40); (60) p.50 (PDF p.53)

import Mathlib
import Definitions.Def_PathORAMCap_Leaf

set_option autoImplicit false

namespace PathORAMCap

/-- Upward packing with capacity `Z` on `h` bucket levels, (40) p.37 (PDF p.40), (20) p.16
(PDF p.19), (60) p.50 (PDF p.53):
`D^(Z)_v(A) = (A_v + D^(Z)_{v0}(A) + D^(Z)_{v1}(A) − Z)⁺`, where missing children contribute zero.
`overflowAux Z h A v` is the number of blocks passed above `v` when the loads `A` on the `h` levels
`v, …` (nodes `w ⪰ v` with `|w| < |v| + h`) are packed upward, each bucket retaining at most `Z`.

**Formalization Note.** The recursion is on the number `h` of bucket levels below and including
`v`; `h = 0` is the empty tree (overflow `0`), so the nodes of the last level have no children.
Loads are nonnegative reals (the paper also uses real loads for its convexity arguments); integer
loads enter by the cast. -/
noncomputable def overflowAux (Z : ℝ) : ℕ → (List Bool → ℝ) → List Bool → ℝ
  | 0, _, _ => 0
  | h + 1, A, v =>
      max (A v + overflowAux Z h A (v ++ [false]) + overflowAux Z h A (v ++ [true]) - Z) 0

/-- Root overflow `D^(Z)(A) = D^(Z)_ε(A)` of integer node loads `A` on the depth-`L` tree (the
`L + 1` bucket levels below the root), (40) p.37 (PDF p.40). -/
noncomputable def overflowD (Z L : ℕ) (A : List Bool → ℕ) : ℝ :=
  overflowAux Z (L + 1) (fun v => (A v : ℝ)) []

end PathORAMCap


