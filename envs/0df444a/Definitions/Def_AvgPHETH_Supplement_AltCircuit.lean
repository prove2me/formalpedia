-- Prove2me | Definitions.Def_AvgPHETH_Supplement_AltCircuit
-- name    : AvgPHETH_Supplement_AltCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:30:47.065922+00:00
-- url     : https://prove2.me/theorems/e4f6c5f0-97b0-42be-ad7e-9b11a4dcf76f
-- title:
--   Alternating AND-OR circuits
-- statement:
--   An **alternating AND-OR circuit of depth $h\ge1$** over variables $V$ is a layered directed acyclic graph with input vertices in layer $0$, AND and OR gates in layers $1,\dots,h$, and a single output gate in layer $h$. Input vertices are labelled by literals or constants, so negations occur only at the inputs. Each gate receives a nonempty set of inputs from the immediately preceding layer. All gates in a layer have the same type, and the types alternate between consecutive gate layers. The circuit is AND-rooted or OR-rooted according to its output gate. Fan-out is arbitrary, a variable may label several input vertices, and gates of fan-in one are allowed.
--
--   The **bottom layer** is gate layer $1$, the **bottom width** is the largest fan-in of a bottom-layer gate, and the gates above the bottom layer are those in layers $2,\dots,h$.
--
--   **Formalization Note** A gate's inputs are stored as a set of vertices of the previous layer. A repeated wire changes neither an AND nor an OR gate, and removing it does not increase any fan-in or gate count.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3 'Alternating AND-OR circuits', pp.16–17 (PDF 18–19)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Lit

namespace AvgPHETH.Supplement

/-- An **alternating AND-OR circuit** of depth `h = depth` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, pp.16–17 (PDF 18–19)): a
layered DAG with `size 0` input vertices in layer `0`, labelled by literals or constants, and
`size j` gates in layer `j` for `1 ≤ j ≤ h`, with a single output gate in layer `h`. The gate `g` of
layer `j + 1` takes its inputs `wires j g` from layer `j` only. All gates of a layer have the same type
and the types alternate between consecutive gate layers; the output gate is an AND gate iff
`outAnd = true` (so layer `j` is of the output's type iff `h - j` is even). Fan-out is arbitrary,
variables may label several input vertices, and gates of fan-in one are allowed.

**Formalization Note** A gate's inputs are a set of vertices of the previous layer (a repeated wire
does not change an AND or OR gate) and are nonempty (the page counts fan-in from one). The sizes of
layers above `h` are unused. -/
structure AltCircuit (V : Type) where
  depth : ℕ
  depth_pos : 1 ≤ depth
  outAnd : Bool
  size : ℕ → ℕ
  input : Fin (size 0) → Lit V
  wires : (j : ℕ) → Fin (size (j + 1)) → Finset (Fin (size j))
  wires_nonempty : ∀ j, j < depth → ∀ g, (wires j g).Nonempty
  single_output : size depth = 1

end AvgPHETH.Supplement


