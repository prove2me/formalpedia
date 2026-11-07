-- Prove2me | Definitions.Def_MonDepMW_RunsWithin
-- name    : MonDepMW_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:06.329487+00:00
-- url     : https://prove2.me/theorems/69b26691-8896-4c5d-bd2c-a1536b7d2742
-- title:
--   Word-RAM runs and input layouts
-- statement:
--   Fixes how an algorithm of the paper is a program of the published word RAM (`TrulySubcubicAPSP`, with $W$-bit words and unit-cost steps). A program **runs within** $t$ steps on input cells $ws$ if, started on memory holding $ws$ in cells $0,1,\dots$, it accepts within $t$ steps; the specification is then evaluated on the signed words in the cells after the input.
--
--   Inputs: a graph as $n$ followed by its adjacency matrix row by row (the paper represents graphs by adjacency matrices); a vertex set as $n$ bits; a vertex ordering as its $n$ vertices; a partition as $n$ labels, the least vertex of each part; a relation on parts as the $n\times n$ bit matrix indexed by vertices; a partition sequence as $m$ and then $m$ blocks of labels.
--
--   **Formalization Note** Each statement using this quantifies over every word size above a logarithmic threshold, as in "the RAM model with words of length $O(\log n)$".
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), App. C, p.43; §3, p.11

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **A run of a word-RAM program.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), App. C, p.43: "the RAM model with words of length O(log n)"; the machine is the
published `TrulySubcubicAPSP` word RAM. `P`, started at position `0` on memory holding `ws` in cells `0, 1, …`, accepts
within `t` steps, and the signed words in the cells after the input (`spec`'s argument, from index `0`) satisfy `spec`.

**Formalization Note.** Every statement quantifies over all word sizes `W` above a logarithmic threshold; `spec` only
sees the output cells, through the fixed decoders of `MonDepMW.decodeSet` and its companions, never the input object. -/
def RunsWithin (P : List Instr) (W t : ℕ) (ws : List ℤ) (spec : (ℕ → ℤ) → Prop) : Prop :=
  ∃ mem, exec P t 0 (loadWords W ws) = some (true, mem) ∧
    spec fun a => (mem ((ws.length + a : ℕ) : ℤ)).toInt

open Classical in
/-- **The input graph.** "we assume that all graphs are represented by their adjacency matrices" (p.11): `n` in cell `0`,
then the `n²` entries `0/1` row by row. -/
noncomputable def graphInput {n : ℕ} (G : SimpleGraph (Fin n)) : List ℤ :=
  (n : ℤ) :: rowByRow fun u v => if G.Adj u v then 1 else 0

open Classical in
/-- A vertex set as an input: `n` cells `0/1`. -/
noncomputable def setBits {n : ℕ} (A : Finset (Fin n)) : List ℤ :=
  List.ofFn fun v => if v ∈ A then 1 else 0

/-- A vertex ordering as an input: the `n` vertices in order. -/
def orderWords {n : ℕ} (σ : Fin n ≃ Fin n) : List ℤ :=
  List.ofFn fun i => (((σ i : Fin n) : ℕ) : ℤ)

/-- A partition as an input: `n` labels in `[0, n)`, the label of `v` being the least vertex of its part. -/
noncomputable def partLabels {n : ℕ} (P : Setoid (Fin n)) : List ℤ :=
  List.ofFn fun v => ((sInf {u : ℕ | ∃ h : u < n, P.r ⟨u, h⟩ v} : ℕ) : ℤ)

open Classical in
/-- A relation on the parts of `Q` as an input: the `n × n` `0/1` matrix whose entry `(u, v)` says whether the part of `u`
is related to the part of `v`. -/
noncomputable def relMatrix {n : ℕ} (Q : Setoid (Fin n)) (ρ : Quotient Q → Quotient Q → Prop) : List ℤ :=
  rowByRow fun u v => if ρ (Quotient.mk Q u) (Quotient.mk Q v) then 1 else 0

/-- A partition sequence as an input: `m`, then `m` blocks of labels, block `i` for `𝒫_i`. -/
noncomputable def encodePartSeq {n : ℕ} (m : ℕ) (P : ℕ → Setoid (Fin n)) : List ℤ :=
  (m : ℤ) :: (List.ofFn fun i : Fin m => partLabels (P ((i : ℕ) + 1))).flatten

end MonDepMW


