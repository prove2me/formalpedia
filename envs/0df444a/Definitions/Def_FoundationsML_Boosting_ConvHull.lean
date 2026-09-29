-- Prove2me | Definitions.Def_FoundationsML_Boosting_ConvHull
-- name    : FoundationsML_Boosting_ConvHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:09:30.65405+00:00
-- url     : https://prove2.me/theorems/d350d871-c5f7-4fc5-8d25-957b1eb674dd
-- title:
--   Convex hull of a hypothesis set (Eq. 7.12)
-- statement:
--   **Eq. (7.12), p. 157, PDF p. 174.** $\mathrm{conv}(H)=\{\sum_{k=1}^p\mu_kh_k : p\ge1,
--   \mu_k\ge0, h_k\in H, \sum_{k=1}^p\mu_k\le1\}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 157, Eq. (7.12) (PDF p. 174)

import Mathlib

namespace FoundationsML.Boosting

/-- The convex hull `conv(H)` of a set `H` of real-valued functions `X → ℝ` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Eq. (7.12), p. 157, PDF p. 174): `conv(H) = {∑_{k=1}^p μ_k h_k : p ≥ 1, μ_k ≥ 0, h_k ∈ H,
∑_{k=1}^p μ_k ≤ 1}`. -/
noncomputable def ConvHull {X : Type*} (H : Set (X → ℝ)) : Set (X → ℝ) :=
  {f | ∃ (p : ℕ) (μ : Fin p → ℝ) (hs : Fin p → (X → ℝ)),
    1 ≤ p ∧ (∀ k, 0 ≤ μ k) ∧ (∀ k, hs k ∈ H) ∧ (∑ k, μ k) ≤ 1 ∧
    f = fun x => ∑ k, μ k * hs k x}

end FoundationsML.Boosting


