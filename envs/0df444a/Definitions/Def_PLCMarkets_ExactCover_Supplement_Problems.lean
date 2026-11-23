-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_Supplement_Problems
-- name    : PLCMarkets_ExactCover_Supplement_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:17:17.178726+00:00
-- url     : https://prove2.me/theorems/03d360fb-7c94-4685-97fc-a31ac7a0cebf
-- title:
--   The equilibrium search problems of Theorems 6.1 and 7.1 and the existence languages of Theorem 8.1
-- statement:
--   A **market of the model** is an Arrow–Debreu market with finitely many agents and goods, both nonempty, rational nonnegative endowments, positive total supply of every good, and rational piecewise-linear concave utilities; a **Fisher market** has finitely many buyers and goods, both nonempty, positive rational budgets, one unit of every good, and rational piecewise-linear concave utilities. Instances and answers are binary strings, through the codes of the `Encoding` item. Fix an exponent $k\in\mathbb N$.
--
--   1. **Exchange equilibrium search** (Theorem 6.1). The valid instances are the codes $s$ of markets of the model satisfying (C'). An answer to $s$ is the code $t$ of a rational price equilibrium of the market, with $|t|\le|s|^k+k$.
--   2. **Fisher equilibrium search** (Theorems 6.1, 7.1). The valid instances are the codes $s$ of Fisher markets satisfying (C2). An answer to $s$ is the code $t$ of a rational equilibrium price vector, with $|t|\le|s|^k+k$.
--   3. **Approximate Fisher equilibrium search** (Theorem 7.1). Valid instances as in 2. An answer to the code $s$ of a market with $g$ goods is the code $t$ of a rational $\varepsilon$-approximate equilibrium with
--   $$\varepsilon=\nu_7(g)^{-13},\qquad |t|\le|s|^k+k.$$
--   4. **Existence languages** (Theorem 8.1). The codes of Fisher markets that have a price equilibrium; the codes of markets of the model that have a price equilibrium; the codes of Fisher markets with $n$ buyers that have an $\nu_8(n)^{-5}$-approximate equilibrium; the codes of markets of the model with $a$ agents that have an $\nu_8(a)^{-5}$-approximate equilibrium.
--
--   Every other string is an invalid instance (with no answer) or not in the language.
--
--   **Formalization Note** Search problems are the public `TetrisHard.Rows.SearchProblem` (validity and answer relation on `List Bool`), as used by the published `CorrelatedAuctionComplexity.Main.PPAD`; languages are `CookPvsNP.Lang Bool`. The answer-length bound $|s|^k+k$ makes the relations polynomially balanced, as total search problems in PPAD must be. Fisher equilibria are those of the published `PLCMarkets.Rationality.FisherMarket` (nonnegative prices, every good exactly cleared); Arrow–Debreu equilibria use the §6 budget maximization of the `SourceEquilibrium` item.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:11 (THEOREM 6.1); p. 10:16 (THEOREM 7.1); p. 10:19 (THEOREM 8.1); p. 10:10 (§6, input numbers rational)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_Supplement_SourceEquilibrium
import Definitions.Def_PLCMarkets_ExactCover_Supplement_Conditions
import Definitions.Def_PLCMarkets_ExactCover_Supplement_Encoding
import Definitions.Def_CorrelatedAuctionComplexity_Main_PPAD

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

/-- The search problem of THEOREM 6.1 for Arrow–Debreu markets, with answer-length exponent `k`:
the valid instances are the codes of markets of the model satisfying (C'); an answer to the code
`s` of such a market `M` is the code `t` of a rational price equilibrium `q` of `M` with
`|t| ≤ |s|^k + k`. Every other string is an invalid instance, with no answers. -/
def exchangeEquilibriumSearch (k : ℕ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (a g : ℕ) (M : ADMarket (Fin a) (Fin g)),
    encodeAD M = s ∧ 0 < a ∧ 0 < g ∧ (∀ j, 0 < M.supply j) ∧ ConditionCPrime M
  answer s t := ∃ (a g : ℕ) (M : ADMarket (Fin a) (Fin g)),
    encodeAD M = s ∧ 0 < a ∧ 0 < g ∧ (∀ j, 0 < M.supply j) ∧ ConditionCPrime M ∧
      t.length ≤ s.length ^ k + k ∧
      ∃ q : Fin g → ℚ, encodePrices q = t ∧ IsSrcEquilibrium M (fun j => (q j : ℝ))

/-- The exact search problem of THEOREMS 6.1 and 7.1 for Fisher markets, with answer-length
exponent `k`: the valid instances are the codes of Fisher markets (nonempty sets of buyers and of
goods) satisfying (C2); an answer to the code `s` of such a market `M` is the code `t` of a
rational price equilibrium `q` of `M` with `|t| ≤ |s|^k + k`. -/
def fisherEquilibriumSearch (k : ℕ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n g : ℕ) (M : PLCMarkets.Rationality.FisherMarket n g),
    encodeFisher M = s ∧ 0 < n ∧ 0 < g ∧ FisherC2 M
  answer s t := ∃ (n g : ℕ) (M : PLCMarkets.Rationality.FisherMarket n g),
    encodeFisher M = s ∧ 0 < n ∧ 0 < g ∧ FisherC2 M ∧
      t.length ≤ s.length ^ k + k ∧
      ∃ q : Fin g → ℚ, encodePrices q = t ∧ M.IsEquilibrium (fun j => (q j : ℝ))

/-- The approximate search problem of THEOREM 7.1, with answer-length exponent `k`: the valid
instances are as in `fisherEquilibriumSearch`; an answer to the code `s` of a market `M` with `g`
goods is the code `t` of a rational `ε`-approximate equilibrium `q` of `M`, for
`ε = ν₇(g)^{-13}`, with `|t| ≤ |s|^k + k`. -/
def fisherApproxEquilibriumSearch (k : ℕ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n g : ℕ) (M : PLCMarkets.Rationality.FisherMarket n g),
    encodeFisher M = s ∧ 0 < n ∧ 0 < g ∧ FisherC2 M
  answer s t := ∃ (n g : ℕ) (M : PLCMarkets.Rationality.FisherMarket n g),
    encodeFisher M = s ∧ 0 < n ∧ 0 < g ∧ FisherC2 M ∧
      t.length ≤ s.length ^ k + k ∧
      ∃ q : Fin g → ℚ, encodePrices q = t ∧
        IsFisherApproxEquilibrium M (((nu7 g : ℝ) ^ 13)⁻¹) (fun j => (q j : ℝ))

/-- The language of THEOREM 8.1 for Fisher markets: codes of Fisher markets (nonempty sets of
buyers and of goods) that have a price equilibrium. -/
def fisherExistenceLang : CookPvsNP.Lang Bool :=
  { s | ∃ (n g : ℕ) (M : PLCMarkets.Rationality.FisherMarket n g),
      encodeFisher M = s ∧ 0 < n ∧ 0 < g ∧ ∃ p : Fin g → ℝ, M.IsEquilibrium p }

/-- The language of THEOREM 8.1 for Arrow–Debreu markets: codes of markets of the model that have a
price equilibrium. -/
def adExistenceLang : CookPvsNP.Lang Bool :=
  { s | ∃ (a g : ℕ) (M : ADMarket (Fin a) (Fin g)),
      encodeAD M = s ∧ 0 < a ∧ 0 < g ∧ (∀ j, 0 < M.supply j) ∧
        ∃ p : Fin g → ℝ, IsSrcEquilibrium M p }

/-- The approximate language of THEOREM 8.1 for Fisher markets: codes of Fisher markets with `n`
buyers that have an `ε`-approximate equilibrium, `ε = ν₈(n)^{-5}`. -/
def fisherApproxExistenceLang : CookPvsNP.Lang Bool :=
  { s | ∃ (n g : ℕ) (M : PLCMarkets.Rationality.FisherMarket n g),
      encodeFisher M = s ∧ 0 < n ∧ 0 < g ∧
        ∃ p : Fin g → ℝ, IsFisherApproxEquilibrium M (((nu8 n : ℝ) ^ 5)⁻¹) p }

/-- The approximate language of THEOREM 8.1 for Arrow–Debreu markets: codes of markets of the model
with `a` agents that have an `ε`-approximate equilibrium, `ε = ν₈(a)^{-5}`. -/
def adApproxExistenceLang : CookPvsNP.Lang Bool :=
  { s | ∃ (a g : ℕ) (M : ADMarket (Fin a) (Fin g)),
      encodeAD M = s ∧ 0 < a ∧ 0 < g ∧ (∀ j, 0 < M.supply j) ∧
        ∃ p : Fin g → ℝ, IsSrcApproxEquilibrium M (((nu8 a : ℝ) ^ 5)⁻¹) p }

end PLCMarkets.ExactCover.Supplement


