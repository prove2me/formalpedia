-- Prove2me | Definitions.Def_CNFEncComplexity_Supplement_RunsTo
-- name    : CNFEncComplexity_Supplement_RunsTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:34:53.327171+00:00
-- url     : https://prove2.me/theorems/c86cbce1-3267-4e70-a337-912574b524e0
-- title:
--   Deterministic RAM query with a preloaded memory image
-- statement:
--   This fixes the data-structure model of Theorem 15 inside the paper's random access machine of §3.1 (instructions, transitions and logarithmic cost are the published `Instr`, `Step` and `Reaches`).
--
--   1. A **memory image** is a finite list $D=(D_0,\dots,D_{L-1})$ of natural numbers: the query starts with registers $r_i=D_i$ for $i<L$ and $r_i=0$ otherwise, program counter $0$, and the input head on the first input symbol. Its size is $\sum_i \ell(D_i)$ bits, where $\ell(v)$ is the bit length of $v$ ($\ell(0)=1$).
--   2. A program is **deterministic** if it contains no nondeterministic jump `njump`.
--   3. $\mathrm{RunsTo}(P,D,w,y,k)$ says that the run of program $P$ from memory image $D$ on the input tape $w$ reaches a `halt` instruction with accumulator $r_0=y$, and that the total logarithmic cost of the run, including the halting step, is $k$.
--
--   For a deterministic program each configuration has at most one successor, so the output $y$ and the cost $k$ are uniquely determined.
--
--   **Formalization Note** The halting cost $1+\ell(r_0)$ is charged exactly as in the published `AcceptsWithin`. Packing many bits into one register is allowed and is paid for by the logarithmic cost of every access and by $\ell(D_i)$ in the memory size.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 15, p.15 (PDF 16); §3.1, pp.10–11 (PDF 11–12)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr
import Definitions.Def_CNFEncComplexity_AcceptsWithin

namespace CNFEncComplexity.Supplement

open CNFEncComplexity

/-- The configuration in which a query starts: program counter `0`, registers `r_i := D_i` for
`i < |D|` and `0` elsewhere, head on the first input symbol. -/
def preloadConfig (D : List ℕ) : Config := ⟨0, fun i => D.getD i 0, 0⟩

/-- The size in bits of a memory image: the sum of the bit lengths `ℓ(D_i) = size(D_i) + 1` of its
registers (the published `bitLen`). -/
def memBits (D : List ℕ) : ℕ := (D.map bitLen).sum

/-- A program is deterministic: it contains no `njump` instruction, so every configuration has at
most one successor under the published `Step`. -/
def NjumpFree (prog : List Instr) : Prop := ∀ l₁ l₂ : ℕ, Instr.njump l₁ l₂ ∉ prog

/-- **A RAM query run with preloaded memory.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding
Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 15, p.15
(PDF 16), in the RAM of §3.1, pp.10–11 (PDF 11–12).

`RunsTo prog D w y k`: the run of `prog` on the input tape `w`, started from the memory image `D`
(`preloadConfig D`), reaches a `halt` instruction with accumulator `r₀ = y`, and the total
logarithmic cost of the run, the halting step included (cost `1 + ℓ(r₀)`, as in the published
`AcceptsWithin`), is `k`.

**Formalization Note.** Transitions are the published `Step`/`Reaches` of the §3.1 RAM with
logarithmic cost. For an `njump`-free program (`NjumpFree`) every configuration has at most one
successor and `halt` has none, so the halting configuration and the cost `k` are unique: `RunsTo`
then describes the (unique) deterministic computation. -/
def RunsTo (prog : List Instr) (D : List ℕ) (w : List Bool) (y k : ℕ) : Prop :=
  ∃ (c : Config) (k₀ : ℕ), Reaches prog w (preloadConfig D) c k₀ ∧
    prog[c.pc]? = some Instr.halt ∧ c.reg 0 = y ∧ k = k₀ + (1 + bitLen (c.reg 0))

end CNFEncComplexity.Supplement


