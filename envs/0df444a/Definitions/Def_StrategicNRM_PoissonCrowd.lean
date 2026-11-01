-- Prove2me | Definitions.Def_StrategicNRM_PoissonCrowd
-- name    : StrategicNRM_PoissonCrowd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:15.327983+00:00
-- url     : https://prove2.me/theorems/920d8808-1d73-4940-bf68-1cb564967d56
-- title:
--   Poisson crowd of marks: $k\sim\mathrm{Poi}(r)$ i.i.d. marks
-- statement:
--   A **crowd** of marks in a measurable space $X$ is a pair $(k,x)$ with $k\in\mathbb N$ and $x=(x_1,\dots,x_k)\in X^k$. For $r\ge 0$ and a probability measure $\mu$ on $X$, the **Poisson crowd** of mean size $r$ and mark law $\mu$ has $k\sim\mathrm{Poisson}(r)$ and, given $k$, marks i.i.d. with law $\mu$.
--
--   Two operations on crowds are used: $c$ minus the individual $i$, and the list of marks whose time coordinate is at most $s$, in index order.
--
--   With $r=\lambda T$ and marks whose time coordinate is uniform on $[0,T]$, this is a marked Poisson process of rate $\lambda$ on $[0,T]$. The object is general and reusable: it is the finite mixed binomial form of a Poisson process, on which the Mecke and Campbell formulas are elementary.
--
--   **Formalization Note** The crowd is unordered in law, so the index has no meaning; it only breaks ties. `Crowd.upTo` returns a list and not a multiset for that reason.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §2, p.6, and §3.2, p.12

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StrategicNRM

/-- A finite crowd of marks in `X`: a number `k` of individuals and the mark of each.

Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), §2, p.6: the customers who arrive during
the selling season. The mark of a customer is his type; the arrival time is one coordinate of it.

**Formalization Note.** The indexing carries no meaning: the law `crowdLaw` is exchangeable and the
arrival time is a mark, so customers are not sorted by arrival. -/
abbrev Crowd (X : Type*) := Σ k : ℕ, Fin k → X

/-- The law of a Poisson crowd of intensity `r • μ`: the number of individuals is Poisson of mean
`r`, and given that number the marks are i.i.d. with law `μ`.

Chen & Trichakis, SSRN 2959489, §2, p.6: "Customers arrive according to a Poisson process of rate
λ throughout the selling season".

**Formalization Note.** With `r = λT` and marks whose time coordinate is uniform on `[0,T]`, this
is the (marked) Poisson process of rate `λ` on `[0,T]`, by the order-statistics property. -/
noncomputable def crowdLaw {X : Type*} [MeasurableSpace X] (r : ℝ≥0) (μ : Measure X) :
    Measure (Crowd X) :=
  (poissonMeasure r).bind fun k => (Measure.pi fun _ : Fin k => μ).map (Sigma.mk k)

/-- The crowd with individual `i` removed: `Fin.succAbove` keeps the others in index order.

Chen & Trichakis, SSRN 2959489, §3.2.1, p.12, the "−φ" of `E₋φ`. -/
def Crowd.others {X : Type*} : (c : Crowd X) → Fin c.1 → Crowd X
  | ⟨0, _⟩, i => i.elim0
  | ⟨k + 1, x⟩, i => ⟨k, fun l => x (i.succAbove l)⟩

/-- The marks of the individuals whose time `arr` is at most `s`, in index order.

Chen & Trichakis, SSRN 2959489, §3.2.1, p.11: the information `Hₛ = {φ : t_φ ≤ s}` of the seller
at time `s`.

**Formalization Note.** A list rather than a multiset, because the index breaks a tie in the
arrival times of two customers. -/
noncomputable def Crowd.upTo {X : Type*} (arr : X → ℝ) (c : Crowd X) (s : ℝ) : List X :=
  (List.ofFn c.2).filter fun x => decide (arr x ≤ s)

end StrategicNRM


