-- Prove2me | Definitions.Def_GPSAnalysis_Core_Cones
-- name    : GPSAnalysis_Core_Cones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:29:06.849825+00:00
-- url     : https://prove2.me/theorems/cc1f72a2-a8e1-4094-958b-d2e7b160414c
-- title:
--   Tangent and normal cones to $\Omega$ and conforming poll sets (Definition 3.13)
-- statement:
--   For $\Omega\subseteq\mathbb R^n$ and $x\in\mathbb R^n$, the **tangent cone** and the **normal cone** are
--
--   $$T_\Omega(x)=\operatorname{cl}\{\mu(w-x):\mu\ge 0,\ w\in\Omega\},\qquad N_\Omega(x)=\{v\in\mathbb R^n:\ v^Tw\le 0\ \text{for all } w\in T_\Omega(x)\}.$$
--
--   **Definition 3.13.** For a GPS run, the rule selecting the poll sets $D_k=D(k,x_k)\subseteq D$ **conforms to $\Omega$** for $\epsilon>0$ if, at each iteration $k$ and for each $y$ on the boundary of $\Omega$ with $\|y-x_k\|<\epsilon$, the cone $T_\Omega(y)$ equals the set of nonnegative linear combinations of the columns of some subset $D^y_k\subseteq D_k$.
--
--   Conformity is the requirement that the poll directions follow the geometry of the nearby constraints; it is what turns the directional conclusions of the main theorem into the KKT conditions for linearly constrained problems.
--
--   **Formalization Note** The norm in Definition 3.13 is the sup norm on `Fin n → ℝ`; since the theorem using it quantifies over some $\epsilon>0$, the choice of norm does not matter. The boundary is the topological frontier of $\Omega$.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 900, Section 3.5, tangent and normal cones; p. 901, Definition 3.13

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run

namespace GPSAnalysis.Core

/-- The tangent cone (p. 900): `T_Ω(x) = cl {μ (w - x) : μ ≥ 0, w ∈ Ω}`. -/
def tangentCone {n : ℕ} (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  closure {v | ∃ μ : ℝ, 0 ≤ μ ∧ ∃ w ∈ Ω, v = μ • (w - x)}

/-- The normal cone (p. 900): `N_Ω(x) = {v ∈ ℝⁿ : ∀ w ∈ T_Ω(x), vᵀ w ≤ 0}`. -/
def normalCone {n : ℕ} (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {v | ∀ w ∈ tangentCone Ω x, v ⬝ᵥ w ≤ 0}

/-- Definition 3.13 (p. 901), for the poll sets `D_k` of a run: the rule selecting
`D_k = D(k, x_k) ⊆ D` conforms to `Ω` for `ε` if, at each iteration `k` and for each `y` in the
boundary of `Ω` with `‖y - x_k‖ < ε`, `T_Ω(y)` is the set of nonnegative linear combinations of
the columns of some subset `D^y_k ⊆ D_k`. (The norm is the sup norm of `Fin n → ℝ`.) -/
def ConformsTo {n m p : ℕ} {P : GPSSetup n m p} (R : GPSRun P) (ε : ℝ) : Prop :=
  ∀ k, ∀ y ∈ frontier P.Ω, ‖y - R.x k‖ < ε →
    ∃ S ⊆ R.Dk k, tangentCone P.Ω y = nonnegSpan P.D S

end GPSAnalysis.Core


