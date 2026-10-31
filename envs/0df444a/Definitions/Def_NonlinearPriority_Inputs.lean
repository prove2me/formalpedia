-- Prove2me | Definitions.Def_NonlinearPriority_Inputs
-- name    : NonlinearPriority_Inputs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:53.723861+00:00
-- url     : https://prove2.me/theorems/ef3bde61-81e8-4965-a8fc-8054fcf44028
-- title:
--   Primitive randomness: i.i.d. marks (interarrival, type, service times)
-- statement:
--   On a probability space $(\Omega,\Pr)$, the $n$th arriving customer ($n=0,1,2,\dots$) carries a mark $(A_n, Y_n, (S^{(i)}_n)_{i\le K})$:
--
--   1. $A_n$ is the interarrival time before arrival $n$, exponential with rate $\lambda$, so arrival $n$ happens at $T_n=A_0+\dots+A_n$ and arrivals form a Poisson process;
--   2. $Y_n$ is its type, $\Pr(Y_n=i)=p_i$;
--   3. $S^{(i)}_n$ is the service time it would have as a type-$i$ customer, with law $S_i$; its actual service time is $S^{(Y_n)}_n$.
--
--   The marks are i.i.d. in $n$, and each mark has the product law $\mathrm{Exp}(\lambda)\otimes p\otimes\bigotimes_i S_i$. Hence types are independent of the arrival process and service times are i.i.d. within each type, as in the paper's model.
--
--   **Formalization Note** Independence is one `iIndepFun` over the marks together with the product form of each mark's law; each mark is measurable.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, §3, p.3 (PDF 4)

import Mathlib
import Definitions.Def_NonlinearPriority_Params

open MeasureTheory ProbabilityTheory

namespace NonlinearPriority

/-- The law of the type of an arriving customer: `P(Y = i) = pᵢ` (§3, p. 3). -/
noncomputable def typeLaw {K : ℕ} (P : Params K) : Measure (Fin K) :=
  ∑ i, ENNReal.ofReal (P.p i) • Measure.dirac i

/-- **The primitive randomness of the queue** (§3, p. 3, PDF 4). Ouyang, Argon and Ziya,
Management Science (2021), doi:10.1287/mnsc.2020.3952.

On a probability space `(Ω, Pr)`, customer `n = 0, 1, 2, …` (in order of arrival) carries the mark
`(A n, Y n, Sv · n)`:
* `A n` is the interarrival time before arrival `n` (arrival `n` happens at
  `A 0 + ⋯ + A n`), exponential with rate λ, so arrivals form a Poisson process of rate λ;
* `Y n ∈ Fin K` is its type, `P(Y n = i) = pᵢ`;
* `Sv i n` is the service time customer `n` would have if it were of type `i`, with law `Sᵢ`.

The marks are i.i.d. in `n`, and inside one mark the interarrival time, the type and the `K`
potential service times are independent (product law). Hence the type of a customer is independent
of the arrival process, and the service time `Sv (Y n) n` of customer `n` has law `S_{Y n}` given
its type, with service times i.i.d. within each type: this is the paper's model.

**Formalization Note.** Independence is one `iIndepFun` over the marks plus the product form of
each mark's law; `Measurable` is required so that the laws are the pushforward measures. -/
structure Inputs {K : ℕ} (P : Params K) (Ω : Type*) [MeasurableSpace Ω] (Pr : Measure Ω) where
  /-- interarrival times -/
  A : ℕ → Ω → ℝ
  /-- customer types -/
  Y : ℕ → Ω → Fin K
  /-- potential service times, one per type and customer -/
  Sv : Fin K → ℕ → Ω → ℝ
  measurable_mark : ∀ n, Measurable fun ω => (A n ω, Y n ω, fun i => Sv i n ω)
  law_mark : ∀ n, Pr.map (fun ω => (A n ω, Y n ω, fun i => Sv i n ω)) =
    (expMeasure P.lam).prod ((typeLaw P).prod (Measure.pi P.S))
  indep_mark : iIndepFun (fun n ω => (A n ω, Y n ω, fun i => Sv i n ω)) Pr

end NonlinearPriority


