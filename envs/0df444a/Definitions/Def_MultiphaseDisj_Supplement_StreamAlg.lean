-- Prove2me | Definitions.Def_MultiphaseDisj_Supplement_StreamAlg
-- name    : MultiphaseDisj_Supplement_StreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:35:09.730144+00:00
-- url     : https://prove2.me/theorems/6a2c05f1-0bc8-4cb5-9486-959b56b5b2e6
-- title:
--   Streaming cell-probe algorithms for regular-expression membership and their costs
-- statement:
--   A **streaming cell-probe algorithm** for regular-expression membership over the alphabet of the family $R_{\vec S}$, with word size $w$ and a random tape $\omega$, works in the cell-probe model ($2^w$ cells of $w$ bits, only cell reads and writes charged, computation free):
--
--   1. **Preprocessing.** Given an expression $R$, it builds an initial memory from $R$ and $\omega$, at no cost.
--   2. **Streaming.** The text then arrives one symbol at a time. On each symbol $\sigma$ the algorithm runs a probe program, depending only on $\omega$ and $\sigma$, that may read and write cells; its output is the **report** whether the text read so far belongs to $L(R)$. All information retained between symbols is in memory, and the algorithm does not know which symbol is the last.
--
--   The **cost** of a symbol is the number of probes made while processing it, including its report. With respect to the family $\{R_{\vec S}\}$:
--
--   1. the algorithm has **zero error** if every report is correct, for every tape, every $\vec S$ and every text (malformed texts included);
--   2. its **worst-case cost on data symbols** is at most $t_a$ if every $a_j$ costs at most $t_a$, for every tape, $\vec S$ and preceding text;
--   3. its **expected cost on selectors** is at most $t_c$ if, for every $\vec S$ and preceding text, the cost of $c_q$ is a measurable function of the tape with expectation at most $t_c$;
--   4. its **worst-case time on all symbols** is at most $t$ if every symbol costs at most $t$ on every tape, $\vec S$ and text;
--   5. it has **amortized cost at most $C$ per symbol** if, for every tape, $\vec S$ and text of length $L$, the total cost of processing the text is at most $CL$.
--
--   These are the cost notions of Theorem A.6.
--
--   **Formalization Note** Probe programs, words and memories are those of the published definition `MultiphaseDisj.CellProbe`. The tape is any type $\Omega$; a deterministic algorithm has $\Omega$ = `Unit`. The expectation is the lower Lebesgue integral of the probe count in $[0,\infty]$, as in `MultiphaseDisj.DisjStructure.ExpQueryCostLE`.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), §A.7, p.47 (streaming membership, cost per symbol); Theorem A.6, p.48 (t_a, t_c, worst case, amortized); §2.1 Cell-probe conventions, p.11

import Mathlib
import Definitions.Def_MultiphaseDisj_CellProbe
import Definitions.Def_MultiphaseDisj_Supplement_RegexFamily

set_option autoImplicit false

open scoped ENNReal

namespace MultiphaseDisj.Supplement

/-- A randomized **streaming cell-probe algorithm** for regular-expression membership over the
alphabet `Sym n m`, with word size `w` and random tape `ω : Ω` (Ko, *Unconditional Boolean
Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…, §A.7,
pp.47–48, with the conventions of §2.1, p.11):

* `pre ω R` is the memory built from the given expression `R` (arbitrary, uncharged
  preprocessing);
* when a symbol `σ` arrives, the algorithm runs the probe program `step ω σ` (which may read and
  write) on the current memory; its Boolean result is the report "the text read so far belongs
  to `L(R)`".

**Formalization Note** The program run on a symbol sees only the tape, the symbol and the
memory: all information retained between symbols is in memory, and the algorithm does not know
which symbol is the last. The tape is drawn once, independently of the input, and shared by all
symbols. A deterministic algorithm is one with `Ω = Unit`. Cells, words and probe programs are
those of `MultiphaseDisj.CellProbe` (2^w cells of w bits). -/
structure StreamAlg (n m w : ℕ) (Ω : Type*) where
  pre : Ω → RegularExpression (Sym n m) → Mem w
  step : Ω → Sym n m → Prog w Bool

namespace StreamAlg

variable {n m w : ℕ} {Ω : Type*}

/-- The memory after preprocessing `R` and processing the symbols of `text`, in order. -/
def memAfter (A : StreamAlg n m w Ω) (ω : Ω) (R : RegularExpression (Sym n m))
    (text : List (Sym n m)) : Mem w :=
  text.foldl (fun M σ => ((A.step ω σ).run M).2) (A.pre ω R)

/-- The report made when `σ` arrives after `text`: the algorithm's answer for the prefix
`text ++ [σ]`. -/
def report (A : StreamAlg n m w Ω) (ω : Ω) (R : RegularExpression (Sym n m))
    (text : List (Sym n m)) (σ : Sym n m) : Bool :=
  ((A.step ω σ).run (A.memAfter ω R text)).1

/-- The cost of the symbol `σ` arriving after `text`: the number of cell probes made while
processing it, including its report (§A.7, p.47). -/
def cost (A : StreamAlg n m w Ω) (ω : Ω) (R : RegularExpression (Sym n m))
    (text : List (Sym n m)) (σ : Sym n m) : ℕ :=
  (A.step ω σ).probes (A.memAfter ω R text)

/-- The total cost of processing all symbols of `text`: the sum over `k < |text|` of the cost of
the `k`-th symbol after the first `k` symbols. -/
def totalCost (A : StreamAlg n m w Ω) (ω : Ω) (R : RegularExpression (Sym n m))
    (text : List (Sym n m)) : ℕ :=
  ((List.finRange text.length).map (fun k : Fin text.length => A.cost ω R (text.take k.val) (text.get k))).sum

/-- **Zero error for the family `{R_S}`** (§A.7, p.47, and §2.1, p.11): for every tape, all sets
`S`, every text and every arriving symbol, the report is `true` exactly when the text read so far
belongs to the language of `R_S`.

**Formalization Note** Texts are arbitrary words over the alphabet, malformed ones included. -/
def ZeroError (A : StreamAlg n m w Ω) : Prop :=
  ∀ (ω : Ω) (S : Fin m → Finset (Fin n)) (text : List (Sym n m)) (σ : Sym n m),
    A.report ω (RS S) text σ = true ↔ text ++ [σ] ∈ (RS S).matches'

/-- **Worst-case cost at most `ta` on a data symbol** (Theorem A.6, p.48): over all expressions
of the family, all texts and all tapes, processing a data symbol `a_j` makes at most `ta`
probes. -/
def DataCostLE (A : StreamAlg n m w Ω) (ta : ℕ) : Prop :=
  ∀ (ω : Ω) (S : Fin m → Finset (Fin n)) (text : List (Sym n m)) (j : Fin n),
    A.cost ω (RS S) text (Sym.data j) ≤ ta

/-- **Expected cost at most `tc` on a selector** (Theorem A.6, p.48): for every expression of the
family and every text that ends with a selector `c_q`, the cost of `c_q` is a measurable function
of the tape whose expectation under the tape law `P` is at most `tc`.

**Formalization Note** As in `MultiphaseDisj.DisjStructure.ExpQueryCostLE`: the expectation is
the lower Lebesgue integral of the probe count in `ℝ≥0∞`. -/
def ExpSelCostLE [MeasurableSpace Ω] (A : StreamAlg n m w Ω) (P : MeasureTheory.Measure Ω)
    (tc : ℝ) : Prop :=
  ∀ (S : Fin m → Finset (Fin n)) (text : List (Sym n m)) (q : Fin m),
    Measurable (fun ω => ((A.cost ω (RS S) text (Sym.sel q) : ℕ) : ℝ≥0∞)) ∧
      ∫⁻ ω, ((A.cost ω (RS S) text (Sym.sel q) : ℕ) : ℝ≥0∞) ∂P ≤ ENNReal.ofReal tc

/-- **Worst-case time at most `t` on every symbol** (Theorem A.6, p.48): over all expressions of
the family, all texts, all tapes and all symbols (`#`, data symbols and selectors), processing a
symbol makes at most `t` probes. -/
def WorstCostLE (A : StreamAlg n m w Ω) (t : ℕ) : Prop :=
  ∀ (ω : Ω) (S : Fin m → Finset (Fin n)) (text : List (Sym n m)) (σ : Sym n m),
    A.cost ω (RS S) text σ ≤ t

/-- **Amortized cost at most `C` per symbol on every input stream** (Theorem A.6, p.48): for
every tape, every expression of the family and every text, the total cost of processing the
text is at most `C` times its length. Since every prefix of a text is a text, this bounds the
cost of every prefix. -/
def AmortizedCostLE (A : StreamAlg n m w Ω) (C : ℕ) : Prop :=
  ∀ (ω : Ω) (S : Fin m → Finset (Fin n)) (text : List (Sym n m)),
    A.totalCost ω (RS S) text ≤ C * text.length

end StreamAlg

end MultiphaseDisj.Supplement


