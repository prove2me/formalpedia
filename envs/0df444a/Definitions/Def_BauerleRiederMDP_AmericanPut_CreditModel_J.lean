-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel_J
-- name    : BauerleRiederMDP_AmericanPut_CreditModel_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:46.472904+00:00
-- url     : https://prove2.me/theorems/ea011a2d-be5f-498d-b69a-91251b292af7
-- title:
--   Value iteration $J_n(x)=\max\{0,c(x)+\beta\int J_{n-1}\,dQ^X(\cdot|x)\}$ of the credit problem
-- statement:
--   The maximal expected discounted rewards with $n$ periods left satisfy $J_0\equiv0$ and
--   $$J_n(x)=\max\Big\{0,\ c(x)+\beta\int J_{n-1}(y)\,Q^X(dy\mid x)\Big\},\qquad x\in E.$$
--
--   **Formalization Note** $J_n$ is defined by this recursion, which the book derives from Theorem 10.1.5. Under an upper bounding function each $J_{n-1}$ is measurable with $0\le J_{n-1}\le Cb$, so the (Bochner) integral is that of an integrable function.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.2, p.340, PDF 348

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.AmericanPut

/-- The **maximal expected discounted rewards `J_n` of the credit granting problem with `n` periods left**
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §11.2, p.340, PDF 348, by
Theorem 10.1.5): `J_0 ≡ 0` and
`J_n(x) = max{0, c(x) + β ∫ J_{n−1}(y) Q^X(dy|x)}`, `x ∈ E`.

**Formalization Note.** `J_n` is defined by this recursion, which the book obtains from Theorem 10.1.5 under
Assumption (B_N). The integral is Mathlib's Bochner integral; under an upper bounding function `b`
(`CreditModel.IsUpperBoundingFunction`) every `J_{n−1}` is measurable with `0 ≤ J_{n−1} ≤ C b`, so the
integral is that of an integrable function and no junk value arises. -/
noncomputable def CreditModel.J (M : CreditModel) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (M.c x + M.beta * ∫ y, M.J n y ∂(M.QX x))

end BauerleRiederMDP.AmericanPut


