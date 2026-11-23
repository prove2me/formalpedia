-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_Supplement_Encoding
-- name    : PLCMarkets_ExactCover_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:16:14.712863+00:00
-- url     : https://prove2.me/theorems/45ace839-7b9e-4799-b25d-4b58fb234cd4
-- title:
--   Binary codes of Arrow–Debreu and Fisher markets and of rational price vectors; the size parameters $\nu_7,\nu_8$
-- statement:
--   All input numbers of a market are rationals (§6, p. 10:10). A rational is written as its reduced numerator (a signed integer) and its positive denominator, each as a binary natural number with a self-delimiting length prefix.
--
--   1. The **code of an Arrow–Debreu market** with agents $1,\dots,a$ and goods $1,\dots,g$ lists $a$ and $g$, then the endowments $w_{ij}$ row by row, then every utility function $f^i_j$ row by row. A utility function is written as the number of its bounded segments, the slope and length of each segment in order from the origin, and the slope of its last (infinite) segment.
--   2. The **code of a Fisher market** with buyers $1,\dots,n$ and goods $1,\dots,g$ (one unit of each) lists $n$, $g$, the budgets $e(i)$, and the utility functions row by row in the same way.
--   3. The **code of a rational price vector** $q=(q_1,\dots,q_g)$ lists the $q_j$ in order.
--   4. The **input size** of an Arrow–Debreu market is the length of its code.
--
--   Finally, for $k\in\mathbb N$ let
--   $$\nu(k)=\max\Big(1,\Big\lceil\frac{k-2}{2}\Big\rceil\Big),$$
--   with the ceiling taken in the integers. The tolerance parameters are $\nu_7(g)=\nu(g)$ for a Fisher market with $g$ goods and $\nu_8(a)=\nu(a)$ for a market with $a$ agents. On the reductions of the paper, $\nu_7(2n+2)=n$ is the number of strategies of each player in §7, and $\nu_8(2n+2)=n$ is the size of the X3C instance in §8.
--
--   These codes are the inputs and outputs of the search and decision problems of Theorems 6.1, 7.1 and 8.1.
--
--   **Formalization Note** The binary number code `pack` and the rational code `ratCode` are reused from the published `CorrelatedAuctionComplexity.Main.BinaryCodec`. The parameters $\nu_7,\nu_8$ are defined on every market, small and odd dimensions included; they pin the paper's $O(n^{-13})$ and $O(n^{-5})$ tolerances to the exact values $n^{-13}$ and $n^{-5}$ used in its proofs (pp. 10:17, 10:21).
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:10 (§6: all input numbers rational with at most b bits); p. 10:16 (§7: g = 2n+2 goods); p. 10:17 (ε = n^-13); pp. 10:19–10:21 (§8: 2n+2 agents, ε = n^-5)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_ADMarket
import Definitions.Def_PLCMarkets_Rationality_FisherMarket
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover
open CorrelatedAuctionComplexity.Main (Bits pack ratCode)

/-- The number list of a piecewise-linear utility function of the §8 mission: the number of listed
segments, then the (slope, amount) of every segment as reduced rationals, then the slope of the
last (infinite) piece. -/
def plUtilityData (f : PLUtility) : List ℕ :=
  f.segs.length :: (f.segs.flatMap fun s => ratCode s.1 ++ ratCode s.2) ++ ratCode f.tail

/-- The same number list for a piecewise-linear concave utility function of the Fisher model. -/
def plConcaveData (f : PLCMarkets.Rationality.PLConcave) : List ℕ :=
  f.segs.length :: (f.segs.flatMap fun s => ratCode s.1 ++ ratCode s.2) ++ ratCode f.tail

/-- The binary code of an Arrow–Debreu market with agents `Fin a` and goods `Fin g`: the numbers
`a, g`, the endowments `w_ij` (row by row, as reduced rationals), and the utility functions
`f^i_j` (row by row), all written with the self-delimiting binary number code `pack`. -/
def encodeAD {a g : ℕ} (M : ADMarket (Fin a) (Fin g)) : Bits :=
  pack ([a, g] ++
    ((List.finRange a).flatMap fun i => (List.finRange g).flatMap fun j => ratCode (M.endow i j)) ++
    ((List.finRange a).flatMap fun i =>
      (List.finRange g).flatMap fun j => plUtilityData (M.util i j)))

/-- The binary code of a Fisher market with buyers `Fin n` and goods `Fin g` (unit supply of every
good): the numbers `n, g`, the budgets `e(i)`, and the utility functions `f^i_j` (row by row). -/
def encodeFisher {n g : ℕ} (M : PLCMarkets.Rationality.FisherMarket n g) : Bits :=
  pack ([n, g] ++ ((List.finRange n).flatMap fun i => ratCode (M.budget i)) ++
    ((List.finRange n).flatMap fun i =>
      (List.finRange g).flatMap fun j => plConcaveData (M.util i j)))

/-- The binary code of a rational price vector `q : Fin g → ℚ`, good by good. -/
def encodePrices {g : ℕ} (q : Fin g → ℚ) : Bits :=
  pack ((List.finRange g).flatMap fun j => ratCode (q j))

/-- The input size of an Arrow–Debreu market: the length of its binary code. -/
def adEncodingSize {a g : ℕ} (M : ADMarket (Fin a) (Fin g)) : ℕ := (encodeAD M).length

/-- The size parameter `ν(k) = max(1, ⌈(k − 2)/2⌉)` (ceiling taken in the integers). Applied to the
number `g` of goods it is the `n` of §7 (`g = 2n + 2` goods); applied to the number of agents it is
the `n` of §8 (`2n + 2` agents). -/
def nuParam (k : ℕ) : ℕ := (max 1 ⌈((k : ℚ) - 2) / 2⌉).toNat

/-- The tolerance parameter of THEOREM 7.1: `ν₇(g) = ν(g)` for a Fisher market with `g` goods. -/
def nu7 (g : ℕ) : ℕ := nuParam g

/-- The tolerance parameter of THEOREM 8.1: `ν₈(a) = ν(a)` for a market with `a` agents. -/
def nu8 (a : ℕ) : ℕ := nuParam a

end PLCMarkets.ExactCover.Supplement


