-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_angQ
-- name    : SmoothedSimplex_Shadow_angQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:05:40.344654+00:00
-- url     : https://prove2.me/theorems/b8720fd1-93e3-464d-9df6-de653acabced
-- title:
--   Definition 4.0.3 — $\mathrm{ang}_q(a_1,\dots,a_n)$
-- statement:
--   For a vector $q$ and points $a_1,\dots,a_n\in\mathbb R^d$,
--
--   $$
--   \mathrm{ang}_q(a_1,\dots,a_n)=\mathrm{ang}\big(q,\ \partial\triangle(\mathrm{optSimp}_q(a_1,\dots,a_n))\big),
--   $$
--
--   where $\partial\triangle(\mathrm{optSimp}_q)$ is the boundary of the simplex $\triangle(A_I)$ spanned by the optimal index set $I$. It is the angle by which the objective direction $q$ can be turned before the ray through $q$ leaves the optimal facet; if the ray through $q$ does not pierce the convex hull of $a_1,\dots,a_n$, then $\mathrm{ang}_q=\infty$.
--
--   **Formalization Note** $\partial\triangle(A_I)$ is the relative boundary of the $(d-1)$-simplex, written as the union of its facets $\bigcup_{j\in I}\triangle(A_{I-\{j\}})$. When $\mathrm{optSimp}_q=\emptyset$ the value is $\infty$; when it has several elements (an event of probability zero under Gaussian perturbations, where the paper's $\triangle(\mathrm{optSimp}_q)$ is undefined) the minimum over its elements is taken.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 4.0.3, printed p. 38 (PDF p. 38)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_optSimp
import Definitions.Def_SmoothedSimplex_Shadow_ang

namespace SmoothedSimplex.Shadow

/-- `ang_q(a₁, …, aₙ) = ang(q, ∂△(optSimp_q(a₁, …, aₙ)))` (Spielman & Teng,
arXiv:cs/0111050v7, Definition 4.0.3, printed p. 38, PDF p. 38), where `∂△(A_I)` is the boundary
of the simplex `△(A_I)`.

**Formalization Note.**
* `∂△(A_I)` is the *relative* boundary of the `(d−1)`-simplex `△(A_I)`, written as the union of
  its facets `⋃_{j∈I} △(A_{I−{j}})` (the decomposition used in the proof of Lemma 4.0.7, p. 41).
  Its boundary in `ℝ^d` would be the whole simplex.
* `optSimp_q(a)` is a set of index sets. When it is empty, `ang_q = ∞` (the paper: "if the ray
  through `q` does not pierce the convex hull, `ang_q = ∞`"). When it has two or more elements
  (a probability-zero event under Gaussian perturbations) the paper's `△(optSimp_q)` is
  undefined; this definition takes the minimum over its elements. -/
noncomputable def angQ {d n : ℕ} (q : EuclideanSpace ℝ (Fin d))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ⨅ I ∈ optSimp q a, ang q (⋃ j ∈ I, convexHull ℝ (a '' ((I.erase j : Finset (Fin n)) : Set (Fin n))))

end SmoothedSimplex.Shadow


