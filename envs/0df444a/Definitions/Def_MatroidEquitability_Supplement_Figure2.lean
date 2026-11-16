-- Prove2me | Definitions.Def_MatroidEquitability_Supplement_Figure2
-- name    : MatroidEquitability_Supplement_Figure2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:25:35.039684+00:00
-- url     : https://prove2.me/theorems/be86abc8-76d8-4ea5-b08b-0520c608312f
-- title:
--   The network $N_k$ and fractional flow of Figure 2
-- statement:
--   For $k\in\mathbb N$ the network $N_k$ of Figure 2 has a source $s$, $k$ identical gadgets, a hub $h$ and $k+1$ **central terminals** $C_0,\dots,C_k$, each of demand $8k$. Gadget $i\in[k]$ has top vertices $\ell^1_i,r^1_i$, bottom vertices $\ell^2_i,r^2_i$, middle vertices $p_i$ (left) and $q_i$ (right), and three terminals $T^L_i$, $T^M_i$, $T^R_i$ of demands $8k$, $6k-2$, $8k$. The arcs and the fractional flow $x$ on them are
--
--   | arcs | $x_a$ |
--   |---|---|
--   | $s\to\ell^1_i$, $s\to r^1_i$ | $15k+3$ |
--   | $\ell^1_i\to T^L_i$, $r^1_i\to T^R_i$ | $2k+2$ |
--   | $\ell^1_i\to\ell^2_i$, $r^1_i\to r^2_i$ | $13k+1$ |
--   | $\ell^2_i\to q_i$, $r^2_i\to p_i$ (crossing) | $9k-3$ |
--   | $\ell^2_i\to h$, $r^2_i\to h$ | $4k+4$ |
--   | $p_i\to T^L_i$, $q_i\to T^R_i$ | $6k-2$ |
--   | $p_i\to T^M_i$, $q_i\to T^M_i$ | $3k-1$ |
--   | $h\to C_j$ | $8k$ |
--
--   This is the instance of Theorem 18, the counterexample to the Morell–Skutella conjecture.
--
--   **Formalization Note** The hub $h$ is not drawn in Figure 2, which draws the $2k$ arcs of flow $4k+4$ directly into the block of central terminals. Without a hub the drawn flow cannot satisfy the demands, since $8k$ is not a sum of whole arcs of flow $4k+4$. The hub is also the reading under which the first step of the proof of Theorem 18 holds (two central terminals on the same $s$-path put $16k$ on an arc of flow $4k+4$). In every unsplittable flow each arc $h\to C_j$ carries exactly $8k=x_{hC_j}$, so the hub adds no deviation.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Figure 2, p.20 (PDF p.22), and the proof of Theorem 18, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_MatroidEquitability_Supplement_UnsplittableFlow

namespace MatroidEquitability

namespace Supplement

/-- Vertices of the network `N_k` of Figure 2 (printed p.20 = PDF p.22 of Bérczi, Liu, Reis, Tarnawski,
*Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256
0675891a…)): the source `s`; for each gadget `i ∈ [k]` the top vertices `ℓ1_i, r1_i`, the bottom
vertices `ℓ2_i, r2_i`, the middle vertices `p_i` (left) and `q_i` (right), and the gadget terminals
`TL_i` (left, demand `8k`), `TM_i` (middle, demand `6k − 2`), `TR_i` (right, demand `8k`); the hub `h`;
and the `k + 1` central terminals `C_0, …, C_k` (demand `8k`).

**Formalization Note.** The hub `h` is not drawn: the figure draws the `2k` arcs of flow `4k + 4`
into the block of central terminals. Since `8k` is not a sum of whole arcs of flow `4k + 4`, the drawn
flow satisfies the demands only if these arcs enter one non-terminal vertex `h` that forwards `8k` to
each central terminal; this is also the reading under which the proof's first step holds. -/
inductive Fig2Vertex (k : ℕ) : Type
  | s
  | l1 (i : Fin k)
  | r1 (i : Fin k)
  | l2 (i : Fin k)
  | r2 (i : Fin k)
  | p (i : Fin k)
  | q (i : Fin k)
  | TL (i : Fin k)
  | TM (i : Fin k)
  | TR (i : Fin k)
  | hub
  | C (j : Fin (k + 1))
  deriving DecidableEq

/-- Arcs of `N_k` (Figure 2, p.20): `s → ℓ1_i`, `s → r1_i`, `ℓ1_i → TL_i`, `r1_i → TR_i`, `ℓ1_i → ℓ2_i`,
`r1_i → r2_i`, the crossing arcs `ℓ2_i → q_i` and `r2_i → p_i`, `ℓ2_i → h`, `r2_i → h`, `p_i → TL_i`,
`p_i → TM_i`, `q_i → TM_i`, `q_i → TR_i`, and `h → C_j`. -/
inductive Fig2Arc (k : ℕ) : Type
  | sl1 (i : Fin k)
  | sr1 (i : Fin k)
  | l1TL (i : Fin k)
  | r1TR (i : Fin k)
  | l1l2 (i : Fin k)
  | r1r2 (i : Fin k)
  | l2q (i : Fin k)
  | r2p (i : Fin k)
  | l2h (i : Fin k)
  | r2h (i : Fin k)
  | pTL (i : Fin k)
  | pTM (i : Fin k)
  | qTM (i : Fin k)
  | qTR (i : Fin k)
  | hC (j : Fin (k + 1))
  deriving DecidableEq, Fintype

/-- Terminals of `N_k`: the three terminals `TL_i, TM_i, TR_i` of each gadget and the `k + 1` central
terminals `C_j` (Figure 2, p.20). -/
inductive Fig2Terminal (k : ℕ) : Type
  | TL (i : Fin k)
  | TM (i : Fin k)
  | TR (i : Fin k)
  | C (j : Fin (k + 1))
  deriving DecidableEq, Fintype

namespace Fig2Arc

variable {k : ℕ}

/-- Tail of an arc of `N_k`. -/
def tail : Fig2Arc k → Fig2Vertex k
  | sl1 _ => .s
  | sr1 _ => .s
  | l1TL i => .l1 i
  | r1TR i => .r1 i
  | l1l2 i => .l1 i
  | r1r2 i => .r1 i
  | l2q i => .l2 i
  | r2p i => .r2 i
  | l2h i => .l2 i
  | r2h i => .r2 i
  | pTL i => .p i
  | pTM i => .p i
  | qTM i => .q i
  | qTR i => .q i
  | hC _ => .hub

/-- Head of an arc of `N_k`. -/
def head : Fig2Arc k → Fig2Vertex k
  | sl1 i => .l1 i
  | sr1 i => .r1 i
  | l1TL i => .TL i
  | r1TR i => .TR i
  | l1l2 i => .l2 i
  | r1r2 i => .r2 i
  | l2q i => .q i
  | r2p i => .p i
  | l2h _ => .hub
  | r2h _ => .hub
  | pTL i => .TL i
  | pTM i => .TM i
  | qTM i => .TM i
  | qTR i => .TR i
  | hC j => .C j

end Fig2Arc

/-- The network `N_k` of Figure 2 (p.20) with its demands: `8k` at `TL_i`, `TR_i` and every central
terminal `C_j`, and `6k − 2` at `TM_i`. -/
def figure2 (k : ℕ) : SSNetwork (Fig2Vertex k) (Fig2Arc k) (Fig2Terminal k) where
  tail := Fig2Arc.tail
  head := Fig2Arc.head
  source := .s
  terminal
    | .TL i => .TL i
    | .TM i => .TM i
    | .TR i => .TR i
    | .C j => .C j
  demand
    | .TL _ => 8 * k
    | .TM _ => 6 * k - 2
    | .TR _ => 8 * k
    | .C _ => 8 * k

/-- The fractional flow `x` of Figure 2 (arc labels, p.20): `15k + 3` on `s → ℓ1_i, s → r1_i`;
`2k + 2` on `ℓ1_i → TL_i, r1_i → TR_i`; `13k + 1` on `ℓ1_i → ℓ2_i, r1_i → r2_i`; `9k − 3` on the
crossing arcs `ℓ2_i → q_i, r2_i → p_i`; `4k + 4` on `ℓ2_i → h, r2_i → h`; `6k − 2` on
`p_i → TL_i, q_i → TR_i`; `3k − 1` on `p_i → TM_i, q_i → TM_i`; and `8k` on `h → C_j`. -/
def figure2Flow (k : ℕ) : Fig2Arc k → ℝ
  | .sl1 _ => 15 * k + 3
  | .sr1 _ => 15 * k + 3
  | .l1TL _ => 2 * k + 2
  | .r1TR _ => 2 * k + 2
  | .l1l2 _ => 13 * k + 1
  | .r1r2 _ => 13 * k + 1
  | .l2q _ => 9 * k - 3
  | .r2p _ => 9 * k - 3
  | .l2h _ => 4 * k + 4
  | .r2h _ => 4 * k + 4
  | .pTL _ => 6 * k - 2
  | .pTM _ => 3 * k - 1
  | .qTM _ => 3 * k - 1
  | .qTR _ => 6 * k - 2
  | .hC _ => 8 * k

end Supplement

end MatroidEquitability


