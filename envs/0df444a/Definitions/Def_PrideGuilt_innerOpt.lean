-- Prove2me | Definitions.Def_PrideGuilt_innerOpt
-- name    : PrideGuilt_innerOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:07.055058+00:00
-- url     : https://prove2.me/theorems/2abe392f-d8f1-44c6-bd97-67c1cf7336ae
-- title:
--   Optimal profit for a given reward $\Pi^\star(f)$
-- statement:
--   For a fixed recycling reward $f$, the manufacturer's best profit over prices is
--
--   $$
--   \Pi^\star(f)=\sup\{\Pi(p,f) : p\in\mathbb R,\ D(p,f)\ge0\}.
--   $$
--
--   Proposition 1 compares it with the benchmark profit $\Pi_0$.
--
--   **Formalization Note** The page writes $\max_p\Pi(p,f)$; the constraint $D\ge0$ is the same correction as in the optimal profit $\Pi^*$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 1, p.12

import Mathlib
import Definitions.Def_PrideGuilt_profit

namespace PrideGuilt

/-- **The optimal profit for a given reward, `Π⋆(f) ≡ max_p Π(p, f)`, over prices with
nonnegative demand.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 1, p.12 (PDF 13).

**Formalization Note.** `sSup {Π(p, f) : p ∈ ℝ, D(p, f) ≥ 0}`; the constraint `D ≥ 0` is the
correction explained at `optProfit`. -/
noncomputable def innerOpt (P : Params) (γP γG f : ℝ) : ℝ :=
  sSup {π : ℝ | ∃ p : ℝ, 0 ≤ demand P γP γG p f ∧ π = profit P γP γG p f}

end PrideGuilt


