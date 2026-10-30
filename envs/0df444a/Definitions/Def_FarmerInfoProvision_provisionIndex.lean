-- Prove2me | Definitions.Def_FarmerInfoProvision_provisionIndex
-- name    : FarmerInfoProvision_provisionIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:26.298211+00:00
-- url     : https://prove2.me/theorems/de51ae76-ecea-4c2b-9d78-0bc3ca154ea4
-- title:
--   Provision index $V(n,\beta;\gamma)$ of Proposition 2
-- statement:
--   Proposition 2 decides the optimal policy by the sign of
--
--   $$
--   V(n,\beta;\gamma)=16\alpha^4+16\alpha^3(\beta+3\gamma)+4\alpha^2\gamma\bigl[(7+n)\beta+(12+2n-n^2)\gamma\bigr]+4\alpha\gamma^2\bigl[(4+n)\beta+(5+2n-n^2)\gamma\bigr]-(n^2-2n-3)\gamma^3(\beta+\gamma).
--   $$
--
--   Without private signals ($\gamma=0$) it equals $16\alpha^4+16\alpha^3\beta>0$; for large $n$ or large $\gamma$ it is negative.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14

import Mathlib

namespace FarmerInfoProvision

/-- **The provision index `V(n, β; γ)` of Proposition 2.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14:
"`V(n, β; γ) = 16α⁴ + 16α³(β + 3γ) + 4α²γ[(7 + n)β + (12 + 2n − n²)γ]
+ 4αγ²[(4 + n)β + (5 + 2n − n²)γ] − (n² − 2n − 3)γ³(β + γ)`."

Its sign decides whether informing exactly one farmer or nobody is optimal.

**Formalization Note.** `n` is a real number; the theorems apply it to the number of farmers
cast to `ℝ`. -/
noncomputable def provisionIndex (n α β γ : ℝ) : ℝ :=
  16 * α ^ 4 + 16 * α ^ 3 * (β + 3 * γ) +
    4 * α ^ 2 * γ * ((7 + n) * β + (12 + 2 * n - n ^ 2) * γ) +
    4 * α * γ ^ 2 * ((4 + n) * β + (5 + 2 * n - n ^ 2) * γ) -
    (n ^ 2 - 2 * n - 3) * γ ^ 3 * (β + γ)

end FarmerInfoProvision


