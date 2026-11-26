-- Prove2me | Definitions.Def_GRH_DirichletGrid
-- name    : GRH_DirichletGrid
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T15:03:37.935259+00:00
-- url     : https://prove2.me/theorems/80fabc6d-62ac-58db-a888-20d9581e8aad
-- title:
--   Finite Dirichlet-polynomial samples and error allowances on a rectangular grid
-- statement:
--   For a mesh denominator $m>0$ on $[a,b]\times[-H,H]$, the samples are the finite character sums $\sum_{n=1}^{m^2}\chi(n)n^{-z}$ at its $(m+1)^2$ grid points. The tail budget numerator is $T=2q(3+2H)$ and the derivative bound is $D=16q(H+2)$. A sample passes when its norm exceeds $(T+D(1+2H))/m$, or when its entire distance allowance lies inside the proved low-height strip at level three or four. All coefficients and mesh points are specified by the inputs.
-- source:
--   Derived for the centered Möbius progression bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive nonprincipal Dirichlet input at https://prove2.me/theorems/046910d8-f152-46b2-aff5-b1c00405bcd0. Uses the published Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f and the Davenport bound at https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0.

import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace GRH.DirichletGrid

/-- The rectangular grid includes its four edges. -/
noncomputable def point (a b H : ℝ) (m i j : ℕ) : ℂ :=
  ⟨a + (b-a) * ((i:ℝ)/m), -H + (2*H) * ((j:ℝ)/m)⟩

/-- The truncation index grows quadratically in the mesh denominator. -/
noncomputable def sample {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (m^2), χ (n : ZMod q) * (n : ℂ)^(-z)

noncomputable def tailBudget (q : ℕ) (H : ℝ) : ℝ := 2*q*(3+2*H)

noncomputable def slopeBudget (q : ℕ) (H : ℝ) : ℝ := 16*q*(H+2)

noncomputable def budget (q : ℕ) (H : ℝ) : ℝ := tailBudget q H + slopeBudget q H*(1+2*H)

/-- A cell may use the proved low-height strip at levels three and four.
Every other cell needs a strict Dirichlet-polynomial margin at its grid point. -/
def Passes {q : ℕ} (χ : DirichletCharacter ℂ q) (a b H : ℝ) (m : ℕ) : Prop :=
  0 < m ∧ ∀ i ≤ m, ∀ j ≤ m,
    ((q = 3 ∨ q = 4) ∧ |(point a b H m i j).im| + (1+2*H)/m ≤ 1/(256*(q:ℝ))) ∨
    budget q H / m < ‖sample χ m (point a b H m i j)‖

end GRH.DirichletGrid


