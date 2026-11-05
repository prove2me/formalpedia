-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_GridScheme
-- name    : BauerleRiederMDP_LPDuality_GridScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:03.4683+00:00
-- url     : https://prove2.me/theorems/ca36ea1c-3e29-4e2b-9f8d-86cd35bd9cad
-- title:
--   Grid $G\subset E$ with a linear interpolation scheme and mesh size $h$
-- statement:
--   Let the state space $E$ be a subset of a real normed space $V$. A **grid with interpolation scheme** consists of
--
--   1. a countable set $G\subset E$ of grid points;
--   2. for every state $x\in E$, weights $\lambda_y(x)\ge 0$ on finitely many grid points $y\in G$ with $\sum_y\lambda_y(x)=1$ and $\sum_y\lambda_y(x)\,y=x$; for $x\in G$ the weights are the point mass at $x$;
--   3. each weight $x\mapsto\lambda_y(x)$ is measurable;
--   4. a mesh size $h$: every grid point $y$ with $\lambda_y(x)>0$ lies within distance $h$ of $x$.
--
--   So every state is a convex combination $x=\sum_k\lambda_kx_k$ of nearby grid points $x_k\in G$, $\lambda_k\ge0$, $\sum_k\lambda_k=1$, as in the book's definition of the grid operator $\mathcal T_G$ and the grid bounding function $b_G$.
--
--   **Formalization Note** The book does not say which representation $x=\sum_k\lambda_kx_k$ is used when there are several, nor what the mesh size is. Here one representation per state is fixed, and every result is stated for every such scheme. "Mesh size" bounds the distance from a state to the grid points that interpolate it, which is the property the book's proof of Theorem 7.5.12 uses. Countability ("a discrete grid", p.220) and measurability of the weights make $b_G$ a measurable bounding function, as the book asserts.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.3, pp.220–221 (PDF 231–232): grid G ⊂ E, x = Σ_k λ_k x_k, x_k ∈ G, λ_k ≥ 0, Σ_k λ_k = 1, mesh size h

import Mathlib
open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LPDuality

/-- A **grid with an interpolation scheme and mesh size `h`** on a state space `S ⊆ V`, `V` a
real normed space (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), §7.5.3, p.221, PDF 232): a grid `G ⊂ E` and, for every state `x`, weights `λ_k ≥ 0` on
grid points `x_k ∈ G` with `∑_k λ_k = 1` and `x = ∑_k λ_k x_k`; on the grid the weights are the
point mass at `x`. All grid points used for `x` lie within distance `h` of `x`.

**Formalization Note** The book writes `x = ∑_k λ_k x_k` without saying which representation is
used when there are several; this structure fixes one representation per state (`wt x`, a finitely
supported weight vector on the grid), and every result of the mission is stated for every such
scheme. The grid is countable ("a discrete grid", p.220) and each weight `x ↦ λ_y(x)` is
measurable, which is what makes `b_G` a measurable bounding function as the book asserts. The book
does not define "mesh size"; here `h` bounds the distance from `x` to the grid points that
interpolate it, which is the property its proof of Theorem 7.5.12 uses ("Since `J_∞` is uniformly
continuous"). -/
structure GridScheme {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (S : Set V) where
  /-- The grid `G ⊂ E`. -/
  G : Set S
  countable : G.Countable
  /-- The interpolation weights `λ(x)` of the state `x`. -/
  wt : S → S →₀ ℝ
  supp_grid : ∀ x, ∀ y ∈ (wt x).support, y ∈ G
  nonneg : ∀ x y, 0 ≤ wt x y
  sum_one : ∀ x, (wt x).sum (fun _ c => c) = 1
  barycenter : ∀ x, (wt x).sum (fun y c => c • (y : V)) = (x : V)
  on_grid : ∀ x ∈ G, wt x = Finsupp.single x 1
  meas : ∀ y, Measurable fun x => wt x y
  /-- The mesh size. -/
  h : ℝ
  mesh : ∀ x, ∀ y ∈ (wt x).support, dist x y ≤ h

end BauerleRiederMDP.LPDuality


