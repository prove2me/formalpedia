-- Prove2me | Definitions.Def_TeschlODE_Planar_flow
-- name    : TeschlODE_Planar_flow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T14:29:39.084184+00:00
-- url     : https://prove2.me/theorems/3a112b85-d2f6-48e3-b68f-a03ece0799d3
-- title:
--   Flow Φ(t, x) of an autonomous equation, Eq. (6.9)
-- statement:
--   With the notation of `lifetime`, the **flow** of $\dot x = f(x)$ on $M$ is
--   $$\Phi : W \to M, \qquad \Phi(t, x) = \varphi_x(t), \quad t \in I_x,$$
--   where $\varphi_x$ is the maximal integral curve at $x$.
--
--   It is the object all of Chapters 6–7 of the book reason about: orbits, limit sets and periodic points are defined through it.
--
--   **Formalization Note.** For $t \in I_x$ the value is that at $t$ of *some* integral curve at $x$ defined at $t$, selected with `Classical.choose`; for $f \in C^1$ on open $M$ all such curves agree at $t$, so this is the book's $\Phi(t, x)$. For $t \notin I_x$ the value is the junk value $x$; no statement of the mission evaluates the flow outside $I_x$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 189, §6.2, Eq. (6.9)

import Mathlib
import Definitions.Def_TeschlODE_Planar_lifetime

namespace TeschlODE.Planar

open Classical in
/-- Teschl, §6.2, (6.9), p. 189: the flow `Φ(t, x)` of `ẋ = f(x)` on `M`, i.e. the value at time
`t` of the maximal integral curve at `x`. For `t ∈ lifetime f M x` it is the value at `t` of an
integral curve at `x` defined at `t` (chosen by `Classical.choose`; for `f ∈ C¹(M)` all of them
agree at `t` by uniqueness, so the choice is immaterial). Outside `W` (i.e. for
`t ∉ lifetime f M x`) the value is the junk value `x`; every statement of this mission only
evaluates `flow f M t x` at `t ∈ lifetime f M x`. -/
noncomputable def flow {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (t : ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  if h : t ∈ lifetime f M x then
    Classical.choose (Classical.choose_spec (h : ∃ (J : Set ℝ) (φ : ℝ → Fin n → ℝ),
      IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      φ 0 = x ∧ ∀ s ∈ J, φ s ∈ M ∧ HasDerivAt φ (f (φ s)) s)) t
  else x

end TeschlODE.Planar


