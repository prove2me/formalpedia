-- Prove2me | Definitions.Def_SteinerAPX_Supplement_NetworkApproximationLogLog
-- name    : SteinerAPX_Supplement_NetworkApproximationLogLog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:11:47.571127+00:00
-- url     : https://prove2.me/theorems/22845d7e-f17e-4700-857f-63c61a17e580
-- title:
--   Instances in $O(\log\log n)$ dimensions and polynomial-time $(1+\beta)$-approximations on them
-- statement:
--   For a constant $C$, a raw terminal set (a dimension $k$ and a list of rational points) is in the class **InClassLogLog$(C)$** when its points all have $k$ coordinates and are pairwise distinct, there are $n \ge 3$ of them, and
--   $$k \le C \cdot \log\log n$$
--   (natural logarithm).
--
--   A **NetworkApproximationLogLog$(C,\beta)$** is a polynomial-time Turing machine with finite alphabets that reads the binary code of a raw terminal set and outputs a list of rational segments; on every instance of InClassLogLog$(C)$ its segments lie in $\mathbb R^k$, their union is connected and contains every terminal, and their total length is at most $(1+\beta)\,\mathrm{OPT}$. A **ValueApproximationLogLog$(C,\beta)$** instead outputs a rational $v$ with $\mathrm{OPT} \le v \le (1+\beta)\,\mathrm{OPT}$ on every such instance. Here $\mathrm{OPT}$ is the published `opt`, the infimum of the lengths of spanning segment networks with free Steiner points.
--
--   These are the algorithms ruled out by Theorem 2.
--
--   **Formalization Note** The two structures copy the published `SteinerAPX.NetworkApproximation` and `SteinerAPX.ValueApproximation` field by field, with the class `InClass C` ($n\ge2$, $k \le C\log n$) replaced by InClassLogLog$(C)$. $n \ge 3$ makes $\log\log n$ positive.
-- source:
--   Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…3fcfa9), Theorem 2, p.2 (PDF p.4); proof, §5.3, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_Network
import Definitions.Def_SteinerAPX_RawTerminals

set_option autoImplicit false

namespace SteinerAPX.Supplement

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **The instances of Theorem 2: `n ≥ 3` distinct rational points in `O(log log n)`
dimensions.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission
(manuscript sha256 6f78a9ea…), Theorem 2, p.2 (PDF p.4), "in O(log log n) dimensions", and its
proof, §5.3, p.23 (PDF p.25): "The padded instance has N terminals in O(log n) = O(log log N)
dimensions".

For a constant `C`, a raw terminal set `t` is in the class when it is valid (every point has `k`
coordinates, no point repeats), has `n ≥ 3` points, and its dimension satisfies
`k ≤ C · log log n` (natural logarithm).

**Formalization Note** `n ≥ 3` makes `log log n > 0`. Points are distinct, as in the published
`RawTerminals.InClass` of Theorem 1; the class is a subset of the class with repetitions allowed,
so asking an algorithm to be correct only here excludes more algorithms. -/
def InClassLogLog (C : ℝ) (t : RawTerminals) : Prop :=
  t.Valid ∧ 3 ≤ t.n ∧ (t.k : ℝ) ≤ C * Real.log (Real.log t.n)

/-- **Polynomial-time `(1+β)`-approximation algorithms on the instances of Theorem 2.** Same
source as `InClassLogLog`; proof of Theorem 1, p.22 (PDF p.24): "A (1+β/4)-approximation …
returns a network of length at most …".

A polynomial-time machine with finite alphabets that reads the binary code of a raw terminal set
and outputs a raw network; on every instance of `InClassLogLog C` its output has `k` coordinates
per endpoint, spans the terminals and has length at most `(1 + β) · OPT`.

**Formalization Note** The fields are those of the published `SteinerAPX.NetworkApproximation`
with the class `InClass C` (`k ≤ C log n`, `n ≥ 2`) replaced by `InClassLogLog C`. -/
structure NetworkApproximationLogLog (C β : ℝ) where
  run : List Bool → RawNetwork
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) rawNetworkBits run
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  guarantee : ∀ t : RawTerminals, InClassLogLog C t →
    (run (rawTerminalsBits t)).ValidIn t.k ∧
    Spans t.terminals ((run (rawTerminalsBits t)).toNetwork t.k) ∧
    len ((run (rawTerminalsBits t)).toNetwork t.k) ≤ (1 + β) * opt t.terminals

/-- **Polynomial-time `(1+β)`-approximation of the optimal value on the instances of
Theorem 2**: the machine outputs a rational `v` with `OPT ≤ v ≤ (1 + β) · OPT` on every instance of
`InClassLogLog C`. The fields are those of the published `SteinerAPX.ValueApproximation` with the
class replaced by `InClassLogLog C`; the output is encoded by `ratBits`. -/
structure ValueApproximationLogLog (C β : ℝ) where
  run : List Bool → ℚ
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) ratBits run
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  guarantee : ∀ t : RawTerminals, InClassLogLog C t →
    opt t.terminals ≤ (run (rawTerminalsBits t) : ℝ) ∧
    (run (rawTerminalsBits t) : ℝ) ≤ (1 + β) * opt t.terminals

end SteinerAPX.Supplement


