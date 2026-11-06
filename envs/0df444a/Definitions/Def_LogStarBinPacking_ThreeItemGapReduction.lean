-- Prove2me | Definitions.Def_LogStarBinPacking_ThreeItemGapReduction
-- name    : LogStarBinPacking_ThreeItemGapReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:33.91486+00:00
-- url     : https://prove2.me/theorems/a07992d9-5aca-4fae-b344-5baaa9b0ccab
-- title:
--   Polynomial-time reductions to the three-item $\log^*$ promise problem
-- statement:
--   Fix $\alpha>0$, $\varepsilon>0$ and a language $L$ of binary words. An input of the promise problem of Theorem 1.1 is a bin packing instance $J$ of $3M$ items, $M\ge1$ an integer, with all sizes in
--   $$
--   \Big(\frac13-\varepsilon,\ \frac13+\varepsilon\Big)\cap\Big(\frac14,\ \frac12\Big).
--   $$
--   A **reduction** from $L$ maps every word $x$, in polynomial time, to such an input $(M,J)$ so that
--
--   1. if $x\in L$ then $\mathrm{OPT}(J)=M$;
--   2. if $x\notin L$ then $\mathrm{OPT}(J)>M+\alpha\log^*M$.
--
--   $L$ reduces to the promise problem when such a map exists; NP-hardness of the promise problem means every language in NP reduces to it.
--
--   **Formalization Note** The output is the pair $(M,J)$, $J$ a list of sizes $(p,q)$ meaning $p/q$, with the published binary encoding; the machine is a Mathlib `TM2ComputableInPolyTime` with a finite alphabet, as in the published `PackingGapReduction`. $\log^*$ is the published `logStar` on $\mathbb R$ (the least number of base-two logarithms that bring the argument to at most one), applied to $M\ge1$.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_PacketRouting_CongDil_Recurrences

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **A polynomial-time reduction from `L` to the promise problem of Theorem 1.1.** Doron-Arad,
*Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript
(sha256 1d88425d…), Theorem 1.1, p.2. An input of the promise problem is a bin packing instance `J`
of `3M` items for an integer `M ≥ 1`, with sizes in `(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)`; the two
cases are (i) `OPT(J) = M` and (ii) `OPT(J) > M + α log∗ M`. A reduction maps every word `x` in
polynomial time to such an input `(M, J)`, into case (i) when `x ∈ L` and into case (ii) when
`x ∉ L`.

**Formalization Note** The output is the pair `(M, J)` with `J` a raw instance (pairs `(p, q)`
for the size `p/q`), encoded as in the published `PackingGapReduction`; the machine is a Mathlib
`TM2ComputableInPolyTime` with a finite alphabet. `log∗` is the published `logStar` on `ℝ`
(`log∗ x` = least number of base-two logarithms bringing `x` to at most one), applied to `M ≥ 1`.
Sizes are rational and compared with the real `ε` in `ℝ`. -/
structure ThreeItemGapReduction (α ε : ℝ) (L : BitLanguage) where
  reduce : List Bool → RawReductionOutput
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    BinaryEncoding.rawReductionOutputBits reduce
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  valid : ∀ x, (reduce x).2.Valid
  bins_pos : ∀ x, 1 ≤ (reduce x).1
  itemCount : ∀ x, (reduce x).2.length = 3 * (reduce x).1
  sizes : ∀ x (i : ((reduce x).2.toInstance (valid x)).Item),
    1 / 3 - ε < ((((reduce x).2.toInstance (valid x)).size i : ℚ) : ℝ) ∧
    ((((reduce x).2.toInstance (valid x)).size i : ℚ) : ℝ) < 1 / 3 + ε ∧
    1 / 4 < ((((reduce x).2.toInstance (valid x)).size i : ℚ) : ℝ) ∧
    ((((reduce x).2.toInstance (valid x)).size i : ℚ) : ℝ) < 1 / 2
  completeness : ∀ x, L x → opt ((reduce x).2.toInstance (valid x)) = (reduce x).1
  soundness : ∀ x, ¬ L x →
    ((reduce x).1 : ℝ) + α * (PacketRouting.CongDil.logStar ((reduce x).1 : ℝ) : ℝ) <
      (opt ((reduce x).2.toInstance (valid x)) : ℝ)

end LogStarBinPacking


