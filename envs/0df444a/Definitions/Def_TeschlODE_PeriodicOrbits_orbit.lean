-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_orbit
-- name    : TeschlODE_PeriodicOrbits_orbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T04:28:20.627682+00:00
-- url     : https://prove2.me/theorems/018e9110-73f1-4359-acaf-38ef87febda1
-- title:
--   The orbit $\gamma(x) = \Phi(I_x \times \{x\})$ (6.15)
-- statement:
--   For a flow $\Phi$ with maximal intervals $I_x$, the **orbit** of $x$ is
--   $$\gamma(x) = \{\Phi(t, x) \mid t \in I_x\}.$$
--   For a periodic point this is the closed curve traced by the periodic solution.
--
--   **Formalization Note.** Defined as the image of $I_x$ under $t \mapsto \Phi(t, x)$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3, Eq. (6.15)

import Mathlib

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §6.3, p. 192, (6.15): the orbit `γ(x) = Φ(I_x × {x})` of `x` under the flow `Φ` with
maximal time intervals `I`. -/
def orbit {n : ℕ} (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun t => Φ t x) '' I x

end TeschlODE.PeriodicOrbits


