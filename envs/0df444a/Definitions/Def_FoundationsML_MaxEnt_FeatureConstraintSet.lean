-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_FeatureConstraintSet
-- name    : FoundationsML_MaxEnt_FeatureConstraintSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:13:38.457899+00:00
-- url     : https://prove2.me/theorems/a152c9cd-572c-4466-9703-4240508c9daa
-- title:
--   The feature-constraint set C
-- statement:
--   **p. 300, PDF p. 317.** $C = \{u : \|u - E_{x\sim\hat D}[\Phi(x)]\|_\infty \le \lambda\}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 300 (PDF p. 317)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_EmpiricalFeatureMean

namespace FoundationsML.MaxEnt

/-- The convex feature-constraint set `C` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 300, PDF p. 317): `C = {u : ‖u − E_{x∼D̂}[Φ(x)]
‖_∞ ≤ λ}`, written coordinate-wise. -/
def FeatureConstraintSet {X : Type*} {N m : ℕ}
    (Φ : X → Fin N → ℝ) (S : Fin m → X) (lam : ℝ) : Set (Fin N → ℝ) :=
  {u | ∀ j, |u j - EmpiricalFeatureMean Φ S j| ≤ lam}

end FoundationsML.MaxEnt


