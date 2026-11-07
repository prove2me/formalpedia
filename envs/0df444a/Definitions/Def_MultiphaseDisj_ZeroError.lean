-- Prove2me | Definitions.Def_MultiphaseDisj_ZeroError
-- name    : MultiphaseDisj_ZeroError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:14.517537+00:00
-- url     : https://prove2.me/theorems/5004ddfc-0384-4829-88fe-9bbfb83f8a4b
-- title:
--   Zero error, worst-case update time and expected query time
-- statement:
--   Let $\mathcal D$ be a randomized structure for insert-only multiphase Disjointness with tape law $P$. A history is a family of query sets $\vec S$ together with a sequence of distinct insertions $x_1,\dots,x_k$, which builds $X=\{x_1,\dots,x_k\}$.
--
--   1. $\mathcal D$ has **zero error** if for every tape, every history and every index $q$, the query answers "disjoint" exactly when $S_q\cap X=\emptyset$.
--   2. $\mathcal D$ has **worst-case update time** at most $t_u$ if every insertion, on every tape and after every history, makes at most $t_u$ probes.
--   3. $\mathcal D$ has **expected query time** at most $t_q$ if for every history and every index $q$ the number $T_\omega(q)$ of cells read by the query is a measurable function of the tape with
--   $$
--   \mathbb E_{\omega\sim P}\big[T_\omega(q)\big]\le t_q .
--   $$
--
--   These are the cost and correctness conventions of the main theorem: correctness for every input and tape, update time worst case over inputs and tapes, query time expected over the tape for each fixed input history.
--
--   **Formalization Note** Histories are insertion lists without repetition, so the three properties are required only on histories in which $X$ grows by a new element at each insertion. The expectation is the lower Lebesgue integral of the probe count in $[0,\infty]$; the measurability conjunct makes it the expectation of a random variable.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Problem 1, p.5; §2.1 Cell-probe conventions, p.11

import Mathlib
import Definitions.Def_MultiphaseDisj_DisjStructure

set_option autoImplicit false

open scoped ENNReal

namespace MultiphaseDisj

namespace DisjStructure

variable {n m w : ℕ} {Ω : Type*}

/-- **Zero error** (Ko, arXiv:2610.10904, held version sha256 ba26649b…, §2.1, p.11:
"correctness holds for every input and tape"): for every tape `ω`, all query sets `S`, every
sequence `L` of distinct insertions and every query `q`, the query answers `true` exactly when
`S q ∩ X = ∅`, where `X` is the set of inserted elements.

**Formalization Note** `true` encodes "disjoint". Insertion sequences are lists without
repetition (`X` is a set into which elements are inserted one at a time, Problem 1, p.5). -/
def ZeroError (D : DisjStructure n m w Ω) : Prop :=
  ∀ (ω : Ω) (S : Fin m → Finset (Fin n)) (L : List (Fin n)) (q : Fin m), L.Nodup →
    (D.qry ω q).eval (D.memAfter ω S L) = decide (Disjoint (S q) L.toFinset)

/-- **Worst-case update time at most `tu`** (arXiv:2610.10904, Problem 1, p.5, "each insertion
probes at most tu cells", and §2.1, p.11, "update time is worst case over inputs and tapes"):
every insertion, on every tape and after every valid history, makes at most `tu` probes. -/
def UpdateCostLE (D : DisjStructure n m w Ω) (tu : ℕ) : Prop :=
  ∀ (ω : Ω) (S : Fin m → Finset (Fin n)) (L : List (Fin n)) (x : Fin n), (x :: L).Nodup →
    (D.upd ω x).probes (D.memAfter ω S L) ≤ tu

/-- **Expected query time at most `tq`** (arXiv:2610.10904, §2.1, p.11: "query time is expected
over the tape for each fixed valid input history"): for all query sets `S`, every sequence `L`
of distinct insertions and every query `q`, the number of cells read by the query is a
measurable function of the tape whose expectation under the tape law `P` is at most `tq`.

**Formalization Note** The expectation is the lower Lebesgue integral of the probe count in
`ℝ≥0∞`; the measurability conjunct makes it the expectation of a random variable. -/
def ExpQueryCostLE [MeasurableSpace Ω] (D : DisjStructure n m w Ω)
    (P : MeasureTheory.Measure Ω) (tq : ℝ) : Prop :=
  ∀ (S : Fin m → Finset (Fin n)) (L : List (Fin n)) (q : Fin m), L.Nodup →
    Measurable (fun ω => (((D.qry ω q).probes (D.memAfter ω S L) : ℕ) : ℝ≥0∞)) ∧
      ∫⁻ ω, (((D.qry ω q).probes (D.memAfter ω S L) : ℕ) : ℝ≥0∞) ∂P ≤ ENNReal.ofReal tq

end DisjStructure

end MultiphaseDisj


