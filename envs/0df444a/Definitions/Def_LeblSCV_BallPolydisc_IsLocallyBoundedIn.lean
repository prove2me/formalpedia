-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_IsLocallyBoundedIn
-- name    : LeblSCV_BallPolydisc_IsLocallyBoundedIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:18:59.802356+00:00
-- url     : https://prove2.me/theorems/2771996b-efaf-45bd-b464-ebc73d910875
-- title:
--   Locally bounded in $U$ (footnote, p. 40)
-- statement:
--   Let $U, X \subset \mathbb{C}^n$. A function $f : U \setminus X \to \mathbb{C}$ is **locally bounded in $U$** if for every $q \in U$ there is a neighbourhood $W$ of $q$ such that $f$ is bounded on
--   $$W \cap (U \setminus X).$$
--   The points $q \in X$ are included: $f$ must be bounded near the set it is not defined on.
--
--   **Formalization Note.** $f$ is an ambient function `(Fin n → ℂ) → ℂ`; only its values on `U \ X` enter. "Bounded" is `∃ C, ∀ z ∈ W ∩ (U \ X), ‖f z‖ ≤ C`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 40, footnote to §1.6

import Mathlib

namespace LeblSCV.BallPolydisc

/-- Footnote on p. 40 of Lebl: `f : U ∖ X → ℂ` is locally bounded in `U` if for every `q ∈ U`
there is a neighborhood `W` of `q` such that `f` is bounded on `W ∩ (U ∖ X)`. -/
def IsLocallyBoundedIn {n : ℕ} (f : (Fin n → ℂ) → ℂ) (U X : Set (Fin n → ℂ)) : Prop :=
  ∀ q ∈ U, ∃ W ∈ nhds q, ∃ C : ℝ, ∀ z ∈ W ∩ (U \ X), ‖f z‖ ≤ C

end LeblSCV.BallPolydisc


