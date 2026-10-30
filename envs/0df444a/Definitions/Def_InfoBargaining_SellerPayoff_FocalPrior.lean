-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior
-- name    : InfoBargaining_SellerPayoff_FocalPrior
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:10:23.539988+00:00
-- url     : https://prove2.me/theorems/4130117c-793e-4568-a9cd-2fca70ae587d
-- title:
--   The four focal prior distributions
-- statement:
--   The paper obtains its sharp results for **four focal distributions** of the buyer's value $u$:
--
--   1. **uniform**: $F(u)=u$ on $[0,1]$, mean $\hat u=1/2$;
--   2. **exponential** with mean $\hat u>0$: $F(u)=1-e^{-u/\hat u}$ for $u\ge 0$;
--   3. **logistic** with location $\hat u>0$ and scale $1$: $F(u)=1/[1+e^{-(u-\hat u)}]$ on $(-\infty,+\infty)$;
--   4. **modified pareto** with parameter $\lambda>0$: $F(u)=1-(1-u)^\lambda$ on $[0,1]$, mean $\hat u=1/(1+\lambda)$.
--
--   This is the index type of these four families; the laws themselves are `FocalPrior.measure` and the admissible costs `FocalPrior.costDomain`.
--
--   **Formalization Note** The positivity of $\hat u$ for the exponential and logistic priors is the model's standing assumption "a finite mean $\hat u>0$" (p. 7); $\lambda>0$ is from p. 30.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, unnumbered, p. 13 (the four focal distributions; uniform); proof of Corollary 1, p. 30 (exponential, logistic, modified pareto)

import Mathlib

namespace InfoBargaining.SellerPayoff

/-- **The four focal prior distributions of the buyer's value.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.2, unnumbered, p. 13: "linear information-acquisition cost … and several specific
distributions for the prior (i.e., uniform, exponential, logistic, and modified pareto), which
will be referred to as the four focal distributions"; the last three are specified in the proof
of Corollary 1, p. 30.

* `uniform`: `F(u) = u` on `[0, 1]`, mean `û = 1/2` (p. 13);
* `exponential uhat`: `F(u) = 1 − e^{−u/û}` for `u ≥ 0` (p. 30);
* `logistic uhat`: `F(u) = 1/[1 + e^{−(u−û)}]` on `(−∞, +∞)` (p. 30);
* `modPareto lam`: `F(u) = 1 − (1 − u)^λ` on `[0, 1]`, `λ > 0`, mean `û = 1/(1 + λ)` (p. 30).

**Formalization Note.** The positivity of `û` for the exponential and logistic priors is the
model's standing assumption "a finite mean û > 0" (p. 7); `λ > 0` is from p. 30. The laws
themselves are `FocalPrior.measure`. -/
inductive FocalPrior : Type
  | uniform : FocalPrior
  | exponential (uhat : ℝ) (huhat : 0 < uhat) : FocalPrior
  | logistic (uhat : ℝ) (huhat : 0 < uhat) : FocalPrior
  | modPareto (lam : ℝ) (hlam : 0 < lam) : FocalPrior

end InfoBargaining.SellerPayoff


