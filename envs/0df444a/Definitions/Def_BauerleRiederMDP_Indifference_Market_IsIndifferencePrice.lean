-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_IsIndifferencePrice
-- name    : BauerleRiederMDP_Indifference_Market_IsIndifferencePrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:50.372267+00:00
-- url     : https://prove2.me/theorems/3868389d-c5d4-4c59-8ddc-f255b08da079
-- title:
--   The indifference price $v_n(H,s,\hat s)$
-- statement:
--   The indifference price of $H$ at time $n$ is the value $v_n=v_n(H,s,\hat s)$ which satisfies
--   $$
--   V^0_n(x,s,\hat s)=V^H_n(x+v_n,s,\hat s)\qquad\text{for all } x\in\mathbb R.
--   $$
--   It is the amount at which the investor is indifferent between staying out of the claim and selling it short for that amount. The module defines this equation as a predicate on a number $w$, for fixed prices $(s,\hat s)$, and defines $v_n(H,s,\hat s)$ as a solution of the equation.
--
--   **Formalization Note** The book's phrase "the value which satisfies" presupposes existence and uniqueness. The function is `Classical.epsilon` of the predicate; Theorem 4.9.4 b) proves that the predicate has exactly one solution, so nothing depends on the choice.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.138, display after (4.38); Definition 4.9.1, p.136

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_VH

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The defining equation of the indifference price (Bäuerle & Rieder, Markov Decision Processes
with Applications to Finance (2011), §4.9, p.138, PDF 152, and Definition 4.9.1, p.136, PDF 150):
at time `n` in the prices `(s, ŝ)`, the number `w` satisfies
`V⁰_n(x, s, ŝ) = V^H_n(x + w, s, ŝ)` for every `x ∈ ℝ`. -/
def IsIndifferencePrice (M : Market) (N : ℕ) (H : Claim) (n : ℕ) (s ŝ w : ℝ) : Prop :=
  ∀ x : ℝ, M.VH N Claim.zero n x s ŝ = M.VH N H n (x + w) s ŝ

/-- The indifference price `v_n(H, s, ŝ)`: "the value which satisfies" the defining equation
(p.138, PDF 152).

**Formalization Note.** The book's phrase presupposes that such a value exists and is unique.
`Classical.epsilon` picks a solution of the equation when there is one; Theorem 4.9.4 b) proves that
there is exactly one, so nothing is read off the choice. -/
noncomputable def indifferencePrice (M : Market) (N : ℕ) (H : Claim) (n : ℕ) (s ŝ : ℝ) : ℝ :=
  Classical.epsilon (M.IsIndifferencePrice N H n s ŝ)

end Market

end BauerleRiederMDP.Indifference


