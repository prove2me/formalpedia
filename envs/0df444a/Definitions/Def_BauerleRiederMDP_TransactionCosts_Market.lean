-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
-- name    : BauerleRiederMDP_TransactionCosts_Market
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:20.86294+00:00
-- url     : https://prove2.me/theorems/0e50d390-28c2-4ecb-8b95-f4bd79cac052
-- title:
--   Data of the terminal wealth problem with proportional transaction costs
-- statement:
--   The terminal wealth problem with proportional transaction costs of §4.5 is a financial market with one riskless bond and one stock over $N$ periods, observed on a probability space $(\Omega,\mathcal F,\mathbb P)$. Its data are:
--
--   1. the horizon $N\in\mathbb N$;
--   2. deterministic interest rates $i_n$, so that one unit in the bond at time $n-1$ is worth $1+i_n$ at time $n$;
--   3. the relative price changes $\tilde R_n=S_n/S_{n-1}$ of the stock, random variables on $\Omega$;
--   4. a transaction cost rate $c$: an additional amount $a$ (positive or negative) invested in the stock costs $c|a|$, paid from the bond position;
--   5. the utility function $U$ of the investor, with $\operatorname{dom}U=[0,\infty)$, and a degree $\gamma$ of homogeneity.
--
--   This structure only collects the data; the standing assumptions of the section are a separate predicate.
--
--   **Formalization Note** $U$ is a function on $\mathbb R$ of which only the values on $[0,\infty)$ are used.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, pp.106–107 (PDF 120–121)

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.TransactionCosts

/-- The data of the terminal wealth problem with proportional transaction costs
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.5,
pp.106–107, PDF 120–121), with one bond and one stock:

* `P` — the probability measure `IP` on the sample space `Ω`;
* `N` — the horizon;
* `i n` — the deterministic interest rate `i_n` of the bond for the period `[n − 1, n)`
  (relative bond price change `1 + i_n`);
* `c` — the proportional transaction cost rate (an additional amount `a` invested in the stock
  costs `c|a|`, paid from the bond position);
* `R n` — the relative price change `R̃_n = S_n / S_{n−1}` of the stock, a random variable;
* `U` — the utility function of the investor (`dom U = [0, ∞)`);
* `γ` — the degree of homogeneity of `U` in Assumption (FM)(i).

**Formalization Note.** Only data; every assumption of the section is in
`Market.Assumptions`. `U` is a function on `ℝ`, of which only the values on `[0, ∞)` are used. -/
structure Market (Ω : Type*) [MeasurableSpace Ω] where
  /-- the probability measure `IP` -/
  P : Measure Ω
  /-- the horizon `N` -/
  N : ℕ
  /-- the interest rates `i_n` -/
  i : ℕ → ℝ
  /-- the transaction cost rate `c` -/
  c : ℝ
  /-- the relative price changes `R̃_n` of the stock -/
  R : ℕ → Ω → ℝ
  /-- the utility function `U` -/
  U : ℝ → ℝ
  /-- the homogeneity degree `γ` of `U` -/
  γ : ℝ

end BauerleRiederMDP.TransactionCosts


