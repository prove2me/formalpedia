-- Prove2me | Definitions.Def_TeschlODE_Stability_orbit
-- name    : TeschlODE_Stability_orbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:17:14.163153+00:00
-- url     : https://prove2.me/theorems/bfc315a1-ee4a-434b-9ac4-527f0583076a
-- title:
--   The orbit $\gamma(x) = \Phi(I_x \times \{x\})$ (6.15)
-- statement:
--   Let $\Phi$ be a flow with maximal intervals $I_x$. The **orbit** of $x$ is
--   $$\gamma(x) = \Phi(I_x \times \{x\}) = \{\Phi(t, x) : t \in I_x\}. \qquad (6.15)$$
--   An orbit "lies entirely in" a set $V$ when $\gamma(x) \subseteq V$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3, Eq. (6.15)

import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.3, p. 192, (6.15): the orbit `γ(x) = Φ(I_x × {x})` of `x`. -/
def orbit {n : ℕ} (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun t => Φ t x) '' I x

end TeschlODE.Stability


