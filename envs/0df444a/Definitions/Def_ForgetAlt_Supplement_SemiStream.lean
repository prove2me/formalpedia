-- Prove2me | Definitions.Def_ForgetAlt_Supplement_SemiStream
-- name    : ForgetAlt_Supplement_SemiStream
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:17:05.981197+00:00
-- url     : https://prove2.me/theorems/22c56fc2-dcbf-489b-8930-fb1ed6640664
-- title:
--   Deterministic multi-pass semi-streaming machines
-- statement:
--   In the **multi-pass semi-streaming model** the vertex set $\{0,\dots,n-1\}$ of a graph $G$ is known and its edges arrive as a stream, which the algorithm may read several times; the order of the edges is arbitrary and may differ from pass to pass. The algorithm is charged for its number of passes and for its memory in bits.
--
--   A **deterministic streaming machine with $s$ bits of memory** on $n$-vertex graphs consists of
--
--   1. an initial memory state, one of the $2^s$ states;
--   2. an edge-step map (state, edge) $\mapsto$ state;
--   3. an end-of-pass map state $\mapsto$ state;
--   4. an output map from states to sets of vertex pairs.
--
--   Run for $P$ passes on streams $\sigma_0,\sigma_1,\dots$, pass $i$ feeds the edges of $\sigma_i$ in order to the edge-step map and then applies the end-of-pass map; the output is read off the final state.
--
--   This is the streaming model of the second part of Theorem 1.3.
--
--   **Formalization Note** The whole retained state lives in `Fin (2^s)`, so every stored bit (pass counters included) is charged. The pattern follows the published `LoadBalMatch_Main_StreamingMachine`, without randomness and with a separate stream for each pass.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.7, “Semi-streaming model”, printed p.34 (PDF p.35); Theorem 1.3, printed p.51 (PDF p.52)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching

namespace ForgetAlt.Supplement

/-!
# Deterministic multi-pass semi-streaming machines

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.7, "Semi-streaming model", printed p.34 (PDF p.35): "the
edge set arrives as a data stream … Our study considers its multi-pass variant, where the algorithm
can read the input stream multiple times. … the efficiency of the algorithm is measured by the
number of passes … the order of edges in the input stream can be arbitrary, and even can be
different among different passes."

**Formalization Notes.**
* A deterministic machine with `s` bits of memory on graphs with vertex set `Fin n` (the vertex
  set is known): its whole retained state is a value in `Fin (2^s)` (every stored bit counts,
  pass counters included); `step` maps the state and the current edge to the next state, `endPass`
  updates the state at the end of each pass, and `output` maps the final state to a set of
  unordered pairs. Computation is free.
* `run A P σ`: pass `i` (for `i < P`) reads its own list `σ i` (in the theorems, any edge stream
  of `G`, so the order may differ between passes), then `endPass`; after `P` passes the output is
  read off the state.
* The pattern follows the published `LoadBalMatch_Main_StreamingMachine`, without randomness and
  with one stream per pass; that definition is not imported because its run reads the same stream
  in every pass.
-/

/-- A deterministic streaming machine with `s` bits of memory on `n`-vertex graphs. -/
structure StreamMachine (n s : ℕ) where
  initial : Fin (2 ^ s)
  step : Fin (2 ^ s) → Sym2 (Fin n) → Fin (2 ^ s)
  endPass : Fin (2 ^ s) → Fin (2 ^ s)
  output : Fin (2 ^ s) → Finset (Sym2 (Fin n))

/-- The state after `P` passes, pass `i` reading the stream `σ i`. -/
def StreamMachine.state {n s : ℕ} (A : StreamMachine n s) (σ : ℕ → List (Sym2 (Fin n))) :
    ℕ → Fin (2 ^ s)
  | 0 => A.initial
  | i + 1 => A.endPass ((σ i).foldl A.step (A.state σ i))

/-- The output of `A` after `P` passes, pass `i` reading the stream `σ i`. -/
def StreamMachine.run {n s : ℕ} (A : StreamMachine n s) (P : ℕ) (σ : ℕ → List (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) :=
  A.output (A.state σ P)

end ForgetAlt.Supplement


