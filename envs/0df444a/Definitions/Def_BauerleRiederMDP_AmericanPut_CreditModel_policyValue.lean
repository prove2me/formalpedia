-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel_policyValue
-- name    : BauerleRiederMDP_AmericanPut_CreditModel_policyValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:42.358285+00:00
-- url     : https://prove2.me/theorems/6c72e8f8-118b-42bd-b37a-0e620637bd01
-- title:
--   Expected discounted reward of a credit policy $(f_N,\dots,f_1)$
-- statement:
--   For a credit policy $(f_N,\dots,f_1)$ with $f_n=1_{S_n}$ (cancel on $S_n$ when $n$ periods are left), the expected discounted reward with $n$ periods left satisfies $J_{0\pi}\equiv0$ and
--   $$J_{n\pi}(x)=\begin{cases}0, & x\in S_n\ \text{(cancel)},\\ c(x)+\beta\displaystyle\int J_{n-1,\pi}(y)\,Q^X(dy\mid x), & x\notin S_n\ \text{(extend)}.\end{cases}$$
--
--   **Formalization Note** The policy value is defined by this reward iteration (the book's Theorem 2.3.4, $J_{n\pi}=\mathcal T_{f_n}J_{n-1,\pi}$), not as a path expectation.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.2, pp.340–341, PDF 348–349; §10.1, p.305, PDF 313

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_CreditModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.AmericanPut

open Classical in
/-- The **expected discounted reward of a credit policy** `(f_N, …, f_1)` with `n` periods left, where
`f_n = 1_{S_n}` cancels the contract on `S_n` (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), §11.2, pp.340–341, PDF 348–349; the stopping problem as a Markov Decision Model, §10.1,
p.305, PDF 313): `J_{0π} ≡ 0` and
`J_{nπ}(x) = 0` if `x ∈ S_n` (cancel: reward `g = 0`, the contract ends), and
`J_{nπ}(x) = c(x) + β ∫ J_{n−1,π}(y) Q^X(dy|x)` otherwise (extend).

**Formalization Note.** The value of the Markov policy is defined by this reward iteration (Theorem 2.3.4 of
the book: `J_{nπ} = 𝒯_{f_n} J_{n−1,π}`) rather than as the path expectation `𝔼_x[R_{τ_π}]`. The integral is
Mathlib's Bochner integral. -/
noncomputable def CreditModel.policyValue (M : CreditModel) (S : ℕ → Set ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x =>
      if x ∈ S (n + 1) then 0 else M.c x + M.beta * ∫ y, M.policyValue S n y ∂(M.QX x)

end BauerleRiederMDP.AmericanPut


