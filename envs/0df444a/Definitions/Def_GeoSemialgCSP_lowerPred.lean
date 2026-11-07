-- Prove2me | Definitions.Def_GeoSemialgCSP_lowerPred
-- name    : GeoSemialgCSP_lowerPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:33.386373+00:00
-- url     : https://prove2.me/theorems/028f560f-9367-4233-b441-f857cfd8f9c5
-- title:
--   The lower coarse predicate $P^-$
-- statement:
--   For parts $S_0,\dots,S_{q-1}$ and a predicate $P$, the **lower coarse predicate** on labels is
--   $$P^-(a_1,\dots,a_k)=\min_{x_j\in S_{a_j}}P(x_1,\dots,x_k),$$
--   which is $1$ exactly when every tuple with $x_j\in S_{a_j}$ satisfies $P$.
--
--   **Formalization Note** Written as the indicator of that condition; for nonempty parts it is the minimum.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §5, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace GeoSemialgCSP

/-- **The lower coarse predicate `P⁻`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §5, printed p.14 (PDF p.15):
`P⁻(a₁, …, a_k) = min_{x_j ∈ S_{a_j}} P(x₁, …, x_k)` for parts `S₀, …, S_{q−1}`.

**Formalization Note.** `P⁻(a) = 1` iff every tuple with `x_j ∈ S_{a_j}` satisfies `P`; for
nonempty parts this is the minimum. -/
noncomputable def lowerPred {k d q : ℕ} (S : Set (Fin k → E d)) (part : Fin q → Set (E d)) :
    (Fin k → Fin q) → ℝ :=
  fun a => {a' : Fin k → Fin q | ∀ y : Fin k → E d, (∀ j, y j ∈ part (a' j)) → y ∈ S}.indicator 1 a

end GeoSemialgCSP


