-- Prove2me | Definitions.Def_PrideGuilt_Params
-- name    : PrideGuilt_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:03.79815+00:00
-- url     : https://prove2.me/theorems/4bcccaeb-c258-4b94-bdbe-611389857d42
-- title:
--   Parameters of the pride–guilt recycling and pricing model
-- statement:
--   The model of Huang, Nguyen, Tseng, Chen and Kirshner has a manufacturer selling one product to a community of consumers, each of whom either recycles the used product or does not. Apart from the socially influenced pride $\gamma_P$ and guilt $\gamma_G$, its parameters are:
--
--   1. the price coefficient $b_0$ and the utility coefficient $b_1$ of the demand $D=1-b_0p+b_1\bar U(f)$;
--   2. the unit costs $c_n$ of a new product and $c_u$ of a remanufactured product;
--   3. a recycler's cost of recycling $c_e$ (effort, time, privacy);
--   4. the intrinsic pride $I_P$ of recycling and the intrinsic guilt $I_G$ of not recycling (a non-recycler's intrinsic utility is $-I_G$);
--   5. the initial proportion $\tau^0$ of recyclers in the community.
--
--   This record only names the parameters; the paper's standing assumptions on them are a separate definition.
--
--   **Formalization Note** $\gamma_P$ and $\gamma_G$ are not fields: every function of the model takes them as explicit arguments, because the main theorem differentiates the optimal profit in them.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Table 1 and eqs. (1)–(2), p.7; Lemma 1, p.9; eqs. (3)–(4), p.11; p.12

import Mathlib

namespace PrideGuilt

/-- **The parameters of the recycling and pricing model, other than pride and guilt.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721,
§3, Table 1 and (1)–(2), p.7 (PDF 8); Lemma 1, p.9 (PDF 10); §4, (3)–(4), p.11 (PDF 12);
§4, p.12 (PDF 13).

* `b0`, `b1` — the price and utility coefficients of the demand (3), `D = 1 − b₀p + b₁Ū(f)`;
* `cn`, `cu` — the unit costs of a new and of a remanufactured product;
* `ce` — a recycler's cost of recycling;
* `IP`, `IG` — the intrinsic pride of recycling and the intrinsic guilt of not recycling
  (a non-recycler's intrinsic utility is `−I_G`);
* `τ0` — the initial proportion `τ⁰` of recyclers (Lemma 1).

The socially influenced pride `γ_P` and guilt `γ_G` are not fields: every function of the model
takes them as explicit arguments, because Theorem 2 differentiates in them. The structure carries
no hypotheses; the paper's standing assumptions are `Standing`. -/
structure Params where
  /-- The price coefficient `b₀` of the demand (3). -/
  b0 : ℝ
  /-- The utility coefficient `b₁` of the demand (3). -/
  b1 : ℝ
  /-- The unit cost `c_n` of a new product. -/
  cn : ℝ
  /-- The unit cost `c_u` of a remanufactured product. -/
  cu : ℝ
  /-- A recycler's cost `c_e` of recycling. -/
  ce : ℝ
  /-- The intrinsic pride `I_P` of recycling. -/
  IP : ℝ
  /-- The intrinsic guilt `I_G` of not recycling. -/
  IG : ℝ
  /-- The initial proportion `τ⁰` of recyclers. -/
  τ0 : ℝ

end PrideGuilt


