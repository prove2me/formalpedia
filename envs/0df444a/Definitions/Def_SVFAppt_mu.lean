-- Prove2me | Definitions.Def_SVFAppt_mu
-- name    : SVFAppt_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:04.038996+00:00
-- url     : https://prove2.me/theorems/d1ad3f69-6029-418b-8130-9e52fccf9977
-- title:
--   Mean vector $\mu$ of the service times (the mean-based schedule)
-- statement:
--   Let $B_1,\dots,B_n$ be the random service times of the $n$ patients on a probability space $(\Omega,\mathcal F,P)$. Their **mean vector** is
--
--   $$\mu_j=\mathbb E[B_j]=\int_\Omega B_j\,dP,\qquad j=1,\dots,n.$$
--
--   The **mean-based schedule** is $x=\mu$: each patient is given a slot as long as their expected service time. It is the schedule under which the approximation ratio $\varrho_\omega$ of the smallest-variance-first rule is studied.
--
--   **Formalization Note** The expectation is the Bochner integral, which is $0$ for a non-integrable variable; every statement using $\mu$ assumes each $B_j$ integrable.
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, §2, pp. 7–8

import Mathlib

open MeasureTheory

namespace SVFAppt

/-- **The mean vector `µ` of the service times, i.e. the mean-based schedule `x = µ`.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, §2, pp. 7–8: patient `i` has service time `B_i`
"which has mean µi"; "the performance of svf for mean-based schedules, which are given by x = µ".

`mu P B j = ∫ B_j dP`.

**Formalization Note** The expectation is the Bochner integral, which is `0` for a non-integrable
`B_j`; every statement of this mission that uses `mu` assumes each `B_j` integrable. -/
noncomputable def mu {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (B : Fin n → Ω → ℝ) : Fin n → ℝ :=
  fun j => ∫ s, B j s ∂P

end SVFAppt


