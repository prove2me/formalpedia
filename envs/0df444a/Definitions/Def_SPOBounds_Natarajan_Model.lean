-- Prove2me | Definitions.Def_SPOBounds_Natarajan_Model
-- name    : SPOBounds_Natarajan_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:26:13.721729+00:00
-- url     : https://prove2.me/theorems/18a53d9d-d84d-495a-a649-466e4c84e2d8
-- title:
--   Predict-then-optimize model: optimization oracle, polyhedron, SPO loss, linear optimization gap $\omega_S$
-- statement:
--   This file fixes the optimization model of the predict-then-optimize framework. Decisions and cost vectors both live in $\mathbb R^d$ with the standard inner product, and $c^\top w$ is written $\langle c, w\rangle$.
--
--   1. **Optimization oracle.** For a feasible region $S\subseteq\mathbb R^d$, a map $w^*:\mathbb R^d\to\mathbb R^d$ is an *oracle* for $S$ if, for every cost vector $c$,
--   $$w^*(c)\in S \quad\text{and}\quad \langle c, w^*(c)\rangle\le\langle c, v\rangle\ \text{ for all } v\in S,$$
--   i.e. $w^*(c)\in\arg\min_{w\in S} c^\top w$. No rule for breaking ties is imposed.
--   2. **Polyhedron.** $S$ is a *polyhedron* if $S=\{v : \langle a_k, v\rangle\le b_k,\ k=1,\dots,m\}$ for some finite $m$, vectors $a_k\in\mathbb R^d$ and scalars $b_k$.
--   3. **SPO loss.** For a predicted cost $\hat c$ and a realized cost $c$,
--   $$\ell_{\rm SPO}(\hat c, c) := c^\top w^*(\hat c) - c^\top w^*(c).$$
--   4. **Linear optimization gap.** $\omega_S(c) := \max_{w\in S} c^\top w - \min_{w\in S} c^\top w$, and for a set $\mathcal C$ of cost vectors $\omega_S(\mathcal C) := \sup_{c\in\mathcal C}\omega_S(c)$.
--
--   For an oracle, $0\le\ell_{\rm SPO}(\hat c,c)\le\omega_S(c)$, so $\omega_S(\mathcal C)$ is the range of the SPO loss on costs in $\mathcal C$; it is the scale of every bound in this mission.
--
--   **Formalization Note** The maximum and minimum in $\omega_S(c)$ are written as `sSup` and `sInf` of the image of $S$; they are attained whenever $S$ is nonempty and compact, which every theorem of the mission assumes. $\omega_S(\mathcal C)$ is `sSup` of the image of $\mathcal C$ and is used only for nonempty bounded $\mathcal C$.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 5 (§2, oracle, eq. (2)), p. 6 (SPO loss), p. 8 (§2.1, linear optimization gap), p. 10 (§3, polyhedron)

import Mathlib

open scoped InnerProductSpace

namespace SPOBounds.Natarajan

/-- `w` is an optimization oracle for the feasible region `S` (arXiv:1905.11488v3, p. 5):
for every cost vector `c`, `w c` is a minimizer of `v ↦ ⟪c, v⟫` over `S`. No tie-breaking rule
is imposed. -/
def IsOracle {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin d), w c ∈ S ∧ ∀ v ∈ S, ⟪c, w c⟫_ℝ ≤ ⟪c, v⟫_ℝ

/-- `S` is a polyhedron: the solution set of finitely many linear inequalities
`⟪a k, v⟫ ≤ b k`, `k = 0, …, m - 1` (p. 10, §3). -/
def IsPolyhedron {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ),
    S = {v | ∀ k, ⟪a k, v⟫_ℝ ≤ b k}

/-- The SPO loss `ℓ_SPO(ĉ, c) = cᵀ w*(ĉ) − cᵀ w*(c)` of the oracle `w` (p. 6). -/
noncomputable def spoLoss {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (chat c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪c, w chat⟫_ℝ - ⟪c, w c⟫_ℝ

/-- The linear optimization gap `ω_S(c) = max_{w ∈ S} cᵀw − min_{w ∈ S} cᵀw` (p. 8). -/
noncomputable def linGap {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun v => ⟪c, v⟫_ℝ) '' S) - sInf ((fun v => ⟪c, v⟫_ℝ) '' S)

/-- `ω_S(𝒞) = sup_{c ∈ 𝒞} ω_S(c)` (p. 8). Used only for nonempty bounded `C`. -/
noncomputable def linGapSet {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (C : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup (linGap S '' C)

end SPOBounds.Natarajan


