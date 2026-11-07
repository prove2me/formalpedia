-- Prove2me | Definitions.Def_HDXConc_linkWeight
-- name    : HDXConc_linkWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:30.205656+00:00
-- url     : https://prove2.me/theorems/c4f175ef-bffa-460b-b20e-85e1016eb40a
-- title:
--   Vertices and edge weights of the underlying graph of a link
-- statement:
--   Let $X$ be a pure $d$-dimensional complex with top density $\pi_d$, and let $s\in X$. The **link** of $s$ is $X_s=\{t\setminus s: t\in X,\ t\supseteq s\}$. Its underlying graph has vertex set $X_s(1)=\{v\notin s: s\cup\{v\}\in X\}$. For distinct $u,v\notin s$, the weight of $\{u,v\}$ is
--
--   $$w_s(u,v)=\sum_{t\in X(d),\ t\supseteq s\cup\{u,v\}}\pi_d(t),$$
--
--   and the weight is $0$ otherwise. In particular $s=\emptyset$ gives the underlying graph of $X$ itself, on the vertex set $X(1)$.
--
--   **Formalization Note.** The paper's link edge measure $\pi^s_2$ is $w_s$ divided by $\binom{d-|s|}{2}\sum_{t'\supseteq s}\pi_d(t')$, a constant for each link. The random walk is unchanged by a constant factor, so the walk on the link is exactly the paper's.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), §2.2 "Links, Underlying Graphs and Skeletons" and "Probability density over a simplicial complex", p.12

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace HDXConc

/-!
# Vertices and edge weights of the underlying graph of a link

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), §2.2 "Links, Underlying Graphs and Skeletons", p.12.

**Formalization Note.** The paper's link `X_s = {t \ s | t ∈ X, t ⊇ s}` carries the induced measure
`π^s_{d'}(t) = π_d(t ⊔ s) / ∑_{t' ⊇ s} π_d(t')` and hence edge weights `π^s_2`. The weight `linkWeight` below is
`π^s_2` times a constant depending only on `s`: it omits the normalization by `∑_{t' ⊇ s} π_d(t')` and by the
binomial coefficient. A random walk does not see a constant factor, so the walk on the link is the paper's.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `X(1)` as a set of vertices: those `v` with `{v} ∈ X`. -/
def vertices (X : Finset (Finset V)) : Finset V :=
  Finset.univ.filter (fun v => ({v} : Finset V) ∈ X)

/-- The vertices `X_s(1)` of the link of `s`: those `v ∉ s` with `s ∪ {v} ∈ X`. -/
def linkVerts (X : Finset (Finset V)) (s : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ s ∧ insert v s ∈ X)

omit [Fintype V] in
/-- The edge weight of `{u, v}` in the underlying graph of the link of `s`:
`∑_{t ∈ X(d), t ⊇ s ∪ {u, v}} π_d(t)` for distinct `u, v ∉ s`, and `0` otherwise (no loops). -/
noncomputable def linkWeight (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) (s : Finset V)
    (u v : V) : ℝ :=
  if u ≠ v ∧ u ∉ s ∧ v ∉ s then
    ∑ t ∈ (SteurerHDX.faces X d).filter (fun t => s ∪ {u, v} ⊆ t), π t
  else 0

end HDXConc


