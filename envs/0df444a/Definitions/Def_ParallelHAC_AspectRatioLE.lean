-- Prove2me | Definitions.Def_ParallelHAC_AspectRatioLE
-- name    : ParallelHAC_AspectRatioLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:34.21593+00:00
-- url     : https://prove2.me/theorems/cdcc761a-dcb8-418c-a879-abb9afc66d55
-- title:
--   Polynomial aspect ratio $\max d(u,v)/\min d(u,v)\le\rho n^\rho$
-- statement:
--   For a finite point set $P$ with $n=|P|$ and a linkage $d$, write $d(u,v):=d(\{u\},\{v\})$. The instance $(P,d)$ has **aspect ratio at most $\rho n^{\rho}$** when
--
--   1. $d(u,v)>0$ for all distinct $u,v\in P$, and
--   2. $d(u,v)\le \rho\,n^{\rho}\,d(w,x)$ for all $u\ne v$ and $w\ne x$ in $P$,
--
--   that is, $\displaystyle\frac{\max_{u\ne v}d(u,v)}{\min_{u\ne v}d(u,v)}\le\rho\,n^{\rho}$.
--
--   This is the hypothesis "poly($n$) aspect ratio" of Theorem 3; it bounds how many times the largest merge value can double (Lemma 18).
--
--   **Formalization Note** The extrema range over distinct pairs (at $u=v$ the ratio is undefined); $\mathrm{poly}(n)$ is pinned as $\rho n^\rho$.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.2, p.7 (PDF p.10)

import Mathlib

namespace ParallelHAC

/-- **Polynomial aspect ratio** (§2.2, p.7): the instance `(P, d)` has aspect ratio
`max_{u,v∈P} d(u, v) / min_{u,v∈P} d(u, v)` at most `ρ · |P|^ρ`, where `d(u, v) := d({u}, {v})`
(p.6). Concretely: every singleton distance between distinct points is positive, and any two such
distances satisfy `d(u, v) ≤ ρ |P|^ρ · d(w, x)`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.2, p.7; Theorem 3, p.7 ("poly(n) aspect ratio").

**Formalization Note.** The maximum and minimum range over pairs of distinct points (at `u = v`
the ratio would be undefined). Positivity of the minimum is part of a finite aspect ratio.
`poly(n)` is pinned as `ρ n^ρ` with `n = |P|`. -/
def AspectRatioLE {V : Type*} [DecidableEq V] (P : Finset V)
    (d : Finset V → Finset V → ℝ) (ρ : ℝ) : Prop :=
  (∀ u ∈ P, ∀ v ∈ P, u ≠ v → 0 < d {u} {v}) ∧
  ∀ u ∈ P, ∀ v ∈ P, ∀ w ∈ P, ∀ x ∈ P, u ≠ v → w ≠ x →
    d {u} {v} ≤ ρ * (P.card : ℝ) ^ ρ * d {w} {x}

end ParallelHAC


