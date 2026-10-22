-- Prove2me | Definitions.Def_RiskFunctionals_Polyhedral_Cones
-- name    : RiskFunctionals_Polyhedral_Cones
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:23.649451+00:00
-- url     : https://prove2.me/theorems/9454a989-68df-42eb-955f-1c18c02b8ba3
-- title:
--   Polyhedral sets, polyhedral cones and polar cones in $\mathbb R^k$
-- statement:
--   Vectors of $\mathbb R^k$ are paired by the Euclidean scalar product $\langle u,v\rangle=\sum_{i=1}^k u_iv_i$.
--
--   1. A set $V\subseteq\mathbb R^k$ is **polyhedral** if it is a finite intersection of closed half-spaces: there are $m\in\mathbb N$, $a_1,\dots,a_m\in\mathbb R^k$ and $b_1,\dots,b_m\in\mathbb R$ with
--   $$V=\{v\in\mathbb R^k:\ \langle a_j,v\rangle\le b_j,\ j=1,\dots,m\}.$$
--   ($m=0$ gives $V=\mathbb R^k$.)
--   2. A set $V\subseteq\mathbb R^k$ is a **polyhedral cone** if it is a finite intersection of closed half-spaces through the origin, $V=\{v:\langle a_j,v\rangle\le0,\ j=1,\dots,m\}$.
--   3. The **polar cone** of $V\subseteq\mathbb R^k$ is
--   $$V^*=\{v^*\in\mathbb R^k:\ \langle v^*,v\rangle\le0\ \text{for all } v\in V\}.$$
--
--   These are the finite-dimensional objects of the polyhedral probability functionals of Pflug and Römisch: the decision sets $V_t$ are polyhedral, and the dual feasibility conditions are membership in polar cones.
--
--   **Formalization Note** Vectors of $\mathbb R^k$ are `Fin k → ℝ` and the scalar product is Mathlib's `⬝ᵥ`. The polar cone uses the book's sign convention ($\le0$); it is the negative of Mathlib's dual cone.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 91, Definition 2.66 and the polar cone before Proposition 2.68; p. 159, conditions (i)–(ii) after Definition 3.37

import Mathlib

namespace RiskFunctionals.Polyhedral

/-- A polyhedral set in `ℝᵏ` (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World
Scientific 2007, p. 91, Definition 2.66 and p. 159, Definition 3.37): a finite intersection of
closed half-spaces, `V = {v ∈ ℝᵏ : ⟨a_j, v⟩ ≤ b_j, j = 1, …, m}`. Vectors of `ℝᵏ` are
`Fin k → ℝ` and `⟨·, ·⟩` is the Euclidean scalar product `⬝ᵥ`. `m = 0` gives `V = ℝᵏ`. -/
def IsPolyhedralSet {k : ℕ} (V : Set (Fin k → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin k → ℝ) (b : Fin m → ℝ), V = {v | ∀ j, a j ⬝ᵥ v ≤ b j}

/-- A polyhedral cone in `ℝᵏ` (p. 91, before Proposition 2.68; p. 159, condition (i)): a
polyhedral set that is a cone, equivalently a finite intersection of closed half-spaces through
the origin, `V = {v ∈ ℝᵏ : ⟨a_j, v⟩ ≤ 0, j = 1, …, m}`. -/
def IsPolyhedralCone {k : ℕ} (V : Set (Fin k → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → Fin k → ℝ), V = {v | ∀ j, a j ⬝ᵥ v ≤ 0}

/-- The polar cone `V* = {y* ∈ ℝᵏ : ⟨y, y*⟩ ≤ 0 for all y ∈ V}` (p. 91, before
Proposition 2.68; p. 159, condition (ii)). This is the **negative** of Mathlib's dual cone. -/
def polarCone {k : ℕ} (V : Set (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  {y | ∀ v ∈ V, y ⬝ᵥ v ≤ 0}

end RiskFunctionals.Polyhedral


