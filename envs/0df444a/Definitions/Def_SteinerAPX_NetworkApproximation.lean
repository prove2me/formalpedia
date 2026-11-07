-- Prove2me | Definitions.Def_SteinerAPX_NetworkApproximation
-- name    : SteinerAPX_NetworkApproximation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:43.417528+00:00
-- url     : https://prove2.me/theorems/f49e1231-1a1b-4264-addc-83110074e7ea
-- title:
--   Polynomial-time $(1+\beta)$-approximation algorithms for Euclidean Steiner Tree in logarithmic dimension
-- statement:
--   Fix constants $C,\beta>0$. A **network $(1+\beta)$-approximation** on the class of Theorem 1 is a polynomial-time algorithm that reads the binary code of a raw terminal set and outputs a raw network such that, on every valid instance with $n\ge 2$ distinct rational terminals $P\subseteq\mathbb R^k$ and $k\le C\log n$, the output network $N$ has endpoints in $\mathbb Q^k$, spans $P$, and satisfies
--   $$
--   \operatorname{len}(N)\le(1+\beta)\,\mathrm{OPT}(P).
--   $$
--   A **value $(1+\beta)$-approximation** instead outputs a rational number $v$ with
--   $$
--   \mathrm{OPT}(P)\le v\le(1+\beta)\,\mathrm{OPT}(P)
--   $$
--   on every such instance.
--
--   These are the algorithms whose existence the main theorem shows to imply $\mathrm P=\mathrm{NP}$.
--
--   **Formalization Note** Algorithms are Mathlib `TM2ComputableInPolyTime` machines with a finite alphabet reading the input bits unchanged, as the published `AbsoluteAdditiveAlgorithm`. Output endpoints are rational, which excludes no ratio since rational points are dense. The guarantee is required only on the instance class.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Theorem 1, p.2 (PDF p.4) ("This rules out a PTAS in arbitrary dimension unless P = NP"); proof of Theorem 1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_RawTerminals

namespace SteinerAPX

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Polynomial-time `(1+β)`-approximation algorithms for Euclidean Steiner Tree on the
instances of Theorem 1.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027
submission (manuscript sha256 6f78a9ea…), Theorem 1, p.2 (PDF p.4), "This rules out a PTAS in
arbitrary dimension unless P = NP", and the proof of Theorem 1, p.22 (PDF p.24): "A
(1+β/4)-approximation … returns a network of length at most …".

A `NetworkApproximation C β` is a polynomial-time machine that reads the binary code of a raw
terminal set and outputs a raw network; on every instance of the class `InClass C` (valid, `n ≥ 2`
distinct rational points in dimension `k ≤ C · log n`) its output has `k` coordinates per endpoint,
spans the terminals, and has length at most `(1 + β) · OPT`.

**Formalization Note** The machine is a Mathlib `TM2ComputableInPolyTime` with a finite alphabet,
reading the input bits unchanged (`id`), as the published `AbsoluteAdditiveAlgorithm`; its output
is encoded by `rawNetworkBits`. Endpoints are rational; since rational points are dense this
excludes no approximation ratio. The guarantee is asked only on the instance class, so an
algorithm needs to be correct only there. -/
structure NetworkApproximation (C β : ℝ) where
  run : List Bool → RawNetwork
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) rawNetworkBits run
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  guarantee : ∀ t : RawTerminals, t.InClass C →
    (run (rawTerminalsBits t)).ValidIn t.k ∧
    Spans t.terminals ((run (rawTerminalsBits t)).toNetwork t.k) ∧
    len ((run (rawTerminalsBits t)).toNetwork t.k) ≤ (1 + β) * opt t.terminals

/-- **Polynomial-time `(1+β)`-approximation of the optimal value** on the instances of Theorem 1:
the machine outputs a rational `v` with `OPT ≤ v ≤ (1 + β) · OPT` on every instance of
`InClass C`. Same source and conventions as `NetworkApproximation`; the output is encoded by
`ratBits`. -/
structure ValueApproximation (C β : ℝ) where
  run : List Bool → ℚ
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) ratBits run
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  guarantee : ∀ t : RawTerminals, t.InClass C →
    opt t.terminals ≤ (run (rawTerminalsBits t) : ℝ) ∧
    (run (rawTerminalsBits t) : ℝ) ≤ (1 + β) * opt t.terminals

end SteinerAPX


