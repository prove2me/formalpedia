-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Assumptions
-- name    : BauerleRiederMDP_TransactionCosts_Market_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:15.456442+00:00
-- url     : https://prove2.me/theorems/3bb15861-1900-4941-9b42-9b2d8f05d99a
-- title:
--   Standing assumptions of §4.5 (Assumption (FM) with transaction costs)
-- statement:
--   The standing assumptions of §4.5 for a transaction cost market $(\mathbb P,N,(i_n),c,(\tilde R_n),U,\gamma)$:
--
--   1. $\mathbb P$ is a probability measure;
--   2. $0\le c<1$;
--   3. $i_n\ge 0$ for $n=1,\dots,N$;
--   4. each $\tilde R_n$ ($n=1,\dots,N$) is measurable and $\tilde R_n>0$ almost surely;
--   5. $\tilde R_1,\dots,\tilde R_N$ are independent;
--   6. Assumption (FM)(ii): $\mathbb E\|\tilde R_n\|<\infty$ for $n=1,\dots,N$;
--   7. $U$ is a utility function on $[0,\infty)$ (Definition 3.4.1): strictly increasing, strictly concave and continuous on $[0,\infty)$;
--   8. Assumption (FM)(i): $U$ is homogeneous of degree $\gamma$, i.e.
--   $$U(\lambda x)=\lambda^\gamma U(x)\qquad\text{for all }\lambda>0,\ x\ge 0.$$
--
--   Arbitrage is allowed: no no-arbitrage condition is assumed, and compactness of the admissible sets comes from the prohibition of short sales.
--
--   **Formalization Note** Items 3–5 are the market assumptions of §3.1 (p.60) that §4.5 builds on; item 7 is "continuous on $\operatorname{dom}U$" of Definition 3.4.1, i.e. right-continuous at $0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, Assumption (FM), p.107 (PDF 121); §3.1, p.60 (PDF 74); Definition 3.4.1, p.70 (PDF 84)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.TransactionCosts

/-- The standing assumptions of §4.5 of Bäuerle & Rieder (2011), *Markov Decision Processes with
Applications to Finance*, pp.106–107 (PDF 120–121), together with those of the financial market
of §3.1 (p.60, PDF 74) and of Definition 3.4.1 (p.70, PDF 84) that §4.5 relies on:

1. `IP` is a probability measure;
2. `0 ≤ c < 1` (p.106);
3. `i_n ≥ 0` for `n = 1, …, N` (p.60: "deterministic interest rate `i_{n+1} ∈ ℝ₊`");
4. `R̃_n` is a positive random variable, i.e. measurable with `R̃_n(ω) > 0` for every `ω`,
   for `n = 1, …, N` (p.60: "The positive random variable R̃_{n+1}");
5. `R̃_1, …, R̃_N` are independent (p.106: "the independent disturbances (Z_n) are given by the
   relative price changes (R̃_n)");
6. Assumption (FM)(ii): `IE ‖R̃_n‖ < ∞` for `n = 1, …, N` (p.107);
7. `U` is a utility function with `dom U = [0, ∞)` (p.106 and Definition 3.4.1, p.70): strictly
   increasing, strictly concave and continuous on `[0, ∞)`;
8. Assumption (FM)(i): `U(λx) = λ^γ U(x)` for all `λ > 0` and `x ≥ 0` (p.107).

No no-arbitrage condition is assumed: "Note that we allow for arbitrage opportunities in the
financial market" (p.107).

**Formalization Note.** Continuity on `[0, ∞)` (`ContinuousOn` on `Set.Ici 0`) is Definition
3.4.1's "continuous on dom U" (p.71: right-continuous in `0`). Independence is `iIndepFun` of
`R̃_1, …, R̃_N` indexed by `Fin N` (`k ↦ R̃_{k+1}`). -/
def Market.Assumptions {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) : Prop :=
  IsProbabilityMeasure M.P ∧
  0 ≤ M.c ∧ M.c < 1 ∧
  (∀ n, 1 ≤ n → n ≤ M.N → 0 ≤ M.i n) ∧
  (∀ n, 1 ≤ n → n ≤ M.N → Measurable (M.R n) ∧ ∀ ω, 0 < M.R n ω) ∧
  iIndepFun (fun k : Fin M.N => M.R (k.val + 1)) M.P ∧
  (∀ n, 1 ≤ n → n ≤ M.N → Integrable (M.R n) M.P) ∧
  StrictMonoOn M.U (Set.Ici 0) ∧ StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) M.U ∧
  ContinuousOn M.U (Set.Ici 0) ∧
  ∀ lam : ℝ, 0 < lam → ∀ x : ℝ, 0 ≤ x → M.U (lam * x) = lam ^ M.γ * M.U x

end BauerleRiederMDP.TransactionCosts


