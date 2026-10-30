-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Assumption1
-- name    : PermBlockchain_Transfers_Assumption1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:10:26.430144+00:00
-- url     : https://prove2.me/theorems/7a540a88-67cf-41f9-8de6-f7970d56ed5e
-- title:
--   Assumption 1: regularity of the vendors' costs
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   Assumption 1 of the paper: the costs $c_h(x)=\gamma x$ and $c_l$ satisfy
--
--   1. $c_l(0)=c_h(0)=0$;
--   2. $c_l$ is convex with a strictly increasing derivative $c_l'$;
--   3. $c_l'(0)<\gamma<c_l'\Bigl(G\bigl(\tfrac{H+L+h+l}{2}-\gamma\bigr)\Bigr)$,
--
--   where $G$ is the distribution function of the outside option.
--
--   **Formalization Note** Item 2 is stated as: $c_l$ has (one-sided at $0$) derivative $c_l'(x)$ on $[0,\infty)$ and $c_l'$ is strictly increasing there; convexity on $[0,\infty)$ follows. $c_h(0)=0$ is automatic. $G$ is the cumulative distribution function of the measure $\nu$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), Appendix A.1, Assumption 1, p. 28 (PDF p. 29); footnote 5, p. 11 (PDF p. 12)

import Mathlib

namespace PermBlockchain.Transfers

/-- **Assumption 1: regularity of the vendors' cost functions.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), Appendix A.1, p. 28 (PDF p. 29): "Assumption 1. We assume that the cost function
c_h(x) = γx of the high type vendor and the cost function c_l(x) of the low type vendor satisfy
the following regularity conditions: 1. c_l(0) = c_h(0) = 0. 2. c_l is convex with a strictly
increasing derivative c′_l. 3. c′_l(0) < γ < c′_l(G((H+L+h+l)/2 − γ))." (Also footnote 5, p. 11.)

Here `G = cdf ν` is the distribution function of the outside option.

**Formalization Note.** Item 2 is stated as: `cl` has derivative `cl' x` within `[0, ∞)` at every
`x ≥ 0`, and `cl'` is strictly increasing on `[0, ∞)`; convexity of `c_l` on `[0, ∞)` follows and
is not repeated. Only `[0, ∞)` matters, since costs are evaluated at total quantities `≥ 0`.
`c_h(0) = 0` holds for `c_h(x) = γx`. -/
def Assumption1 (ν : MeasureTheory.Measure ℝ) (γ H L h l : ℝ) (cl cl' : ℝ → ℝ) : Prop :=
  cl 0 = 0 ∧ (∀ x, 0 ≤ x → HasDerivWithinAt cl (cl' x) (Set.Ici 0) x) ∧
  StrictMonoOn cl' (Set.Ici 0) ∧
  cl' 0 < γ ∧ γ < cl' (ProbabilityTheory.cdf ν ((H + L + h + l) / 2 - γ))

end PermBlockchain.Transfers


