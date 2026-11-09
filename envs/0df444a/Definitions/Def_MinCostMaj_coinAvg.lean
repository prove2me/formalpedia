-- Prove2me | Definitions.Def_MinCostMaj_coinAvg
-- name    : MinCostMaj_coinAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:30:07.805856+00:00
-- url     : https://prove2.me/theorems/0e76c172-20f7-45ba-b201-45b65c731f6b
-- title:
--   Average over uniform coin strings
-- statement:
--   Let $I$ be an instance, $p$ a polynomial and $N=p(|\mathrm{enc}(I)|)$. For a function $g$ from coin strings to $[0,\infty]$,
--   $$\mathrm{coinAvg}(I,p,g)=2^{-N}\sum_{w\in\{0,1\}^N}g(w),$$
--   the expectation of $g$ when the coin string is uniform on $\{0,1\}^N$.
--
--   A randomized algorithm is modelled as a deterministic algorithm that reads the instance and a coin string of polynomial length; this average is its expected cost.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 1.1, p.4 ("randomized"); Proposition 5.3, p.11 (PDF pp.5, 12)

import Mathlib
import Definitions.Def_MinCostMaj_MCInst
import Definitions.Def_MinCostMaj_encInst

namespace MinCostMaj

open scoped ENNReal

/-- **Expectation over the coin strings** of a randomized algorithm.

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 1.1, p.4 ("randomized"), and Proposition 5.3, p.11
("a randomized constant-factor approximation in expectation").

`coinAvg I p g` is the exact uniform average of `g w` over all `2^N` coin strings `w` of length
`N = p(|enc I|)`, computed in `ℝ≥0∞`.

**Formalization Note.** Randomness is a coin string read by a deterministic machine. One
polynomial `p` is fixed before the instance; on instance `I` the coins are uniform on
`{0,1}^{p(|enc I|)}`. -/
noncomputable def coinAvg (I : MCInst) (p : Polynomial ℕ) (g : List Bool → ℝ≥0∞) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) ^ (p.eval (encInst I).length))⁻¹ *
    ∑ w : Fin (p.eval (encInst I).length) → Bool, g (List.ofFn w)

end MinCostMaj


