-- Prove2me | Definitions.Def_NetServicePricing_InClass
-- name    : NetServicePricing_InClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:46.739668+00:00
-- url     : https://prove2.me/theorems/57fa3be3-a6e7-4835-82bc-8697493133b0
-- title:
--   The class of networks with $n$ consumers and average degree $\mathcal D$
-- statement:
--   For a number of consumers $n$, an average degree $\mathcal D$, a habit coefficient $\mu$ and a discount factor $\delta$, the **class** of Theorem 2 consists of the $n\times n$ matrices $M$ such that
--
--   1. $M$ is a network (symmetric, nonnegative, zero diagonal);
--   2. the average degree of $M$ equals $\mathcal D$;
--   3. $M$ satisfies Assumption 1 for $\mu$ and $\delta$.
--
--   Assumption 1 is a standing assumption of the paper, so it is part of membership in the class for every network, balanced or not.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Theorem 2, p.20; §3.1, p.7; Definition 1, p.16; Assumption 1, p.11

import Mathlib
import Definitions.Def_NetServicePricing_IsNetwork
import Definitions.Def_NetServicePricing_averageDegree
import Definitions.Def_NetServicePricing_Assumption1

namespace NetServicePricing

/-- **The class of networks with `n` consumers and average degree `D`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Theorem 2, p.20 ("Consider the class of all networks with n consumers and average degree
D"), with §3.1, p.7 (networks), Definition 1, p.16 (average degree) and Assumption 1, p.11, which
the paper imposes "throughout the paper".

`M` is in the class when it is a network, its average degree is `D`, and it satisfies
Assumption 1 for the habit coefficient `μ` and the discount factor `δ`.

**Formalization Note** The number of consumers is the index type `Fin n` of `M`. -/
def InClass {n : ℕ} (D μ δ : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsNetwork M ∧ averageDegree M = D ∧ Assumption1 M μ δ

end NetServicePricing


