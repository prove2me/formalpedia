-- Prove2me | Definitions.Def_PSDPolyApprox_polar
-- name    : PSDPolyApprox_polar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:14.698735+00:00
-- url     : https://prove2.me/theorems/0158776b-b7ed-4536-bc53-c9f4b6193a43
-- title:
--   Polar $L^\circ=\{y:\langle y,x\rangle\le1\ \forall x\in L\}$
-- statement:
--   For $L\subseteq\mathbb R^d$, the **polar**
--   $$
--   L^\circ=\{y\in\mathbb R^d : \langle x,y\rangle\le1\ \text{for all }x\in L\}.
--   $$
--   For a closed convex $L$ containing the origin, $L=\{x:\langle y,x\rangle\le1\ \forall y\in L^\circ\}$, which is equation (1) of the paper.
--
--   **Formalization Note** The polar is one-sided (no absolute value) and uses the standard dot product on $\mathbb R^\iota$.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.2, p.4, equation (1)

import Mathlib

namespace PSDPolyApprox

open Matrix

/-- **Polar of a set** (one-sided).
Fawzi, arXiv:1811.09649v1, §2.2, p.4: "Let L◦ be the polar of L so that L has the following
inequality description: L = {x ∈ Rd : ⟨y, x⟩ ≤ 1 ∀y ∈ L◦}." (1)

`polar L = {y | ∀ x ∈ L, x ⬝ᵥ y ≤ 1}` in `ι → ℝ`.

**Formalization Note.** The polar is one-sided with the dot product; it is not Mathlib's
`NormedSpace.polar` (which bounds `‖⟨y, x⟩‖`). For a closed convex `L` containing the origin,
the bipolar theorem gives (1). -/
def polar {ι : Type*} [Fintype ι] (L : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {y | ∀ x ∈ L, x ⬝ᵥ y ≤ 1}

end PSDPolyApprox


