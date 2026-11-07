-- Prove2me | Definitions.Def_PolySphereLP_piProj
-- name    : PolySphereLP_piProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:16.262851+00:00
-- url     : https://prove2.me/theorems/96796021-c110-484b-b85d-7cbfbd0d10f2
-- title:
--   The harmonic projection $\Pi_k$
-- statement:
--   Let $\sigma$ be the uniform probability measure on $S^{n-1}$. For a real polynomial $g$, $\Pi_k g$ is the orthogonal projection of $g$ onto $\mathcal H_{n,k}$ in $L^2(\sigma)$: the unique $p\in\mathcal H_{n,k}$ with
--   $$\int (g-p)\,y\,d\sigma=0\qquad\text{for every }y\in\mathcal H_{n,k}.$$
--   For homogeneous $g$ of degree $k$ it is the top term of the Fischer decomposition $g=\Pi_kg+\|x\|^2R$ (16); it annihilates every polynomial of degree less than $k$.
--
--   **Formalization Note** Defined on all real polynomials (Lemma 2.6 applies $\Pi_q$ to a non-homogeneous test). For $n\ge1$ the projection exists and is unique, so the fallback value $0$ of the definition is never used.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (16), pp.10–11; (39), p.16

import Mathlib
import Definitions.Def_SphereSOS_Rate_SphereMeasure
import Definitions.Def_PolySphereLP_harmonicSpace

namespace PolySphereLP

open Classical in
/-- **The harmonic projection `Π_k`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (16), pp.10–11 and (39), p.16: "On the sphere, `Π_k`
is orthogonal projection onto `ℋ_{n,k}`; in particular, it annihilates every polynomial restriction
of degree strictly less than `k`" and "`Π_q` is the spherical `L²` projection onto `ℋ_{n,q}`".

`piProj n k g` is the element `p ∈ ℋ_{n,k}` with `∫ (g − p)·y dσ = 0` for every `y ∈ ℋ_{n,k}`, where
`σ = SphereSOS.Rate.sigma n` is the uniform probability measure on `S^{n−1}`.

**Formalization Note.** Defined on all real polynomials, because Lemma 2.6 applies `Π_q` to a
non-homogeneous test `g`. For `n ≥ 1` such a `p` exists and is unique (finite-dimensional `ℋ_{n,k}`,
positive-definite `L²(σ)` form on it), so the `else 0` branch is never taken; for homogeneous `G`
of degree `k` it agrees with the Fischer top component of (16), since `‖x‖² = 1` on the sphere and
`|x|²R` restricts to a sum of harmonics of degree `< k`. The integrands are polynomials, integrable
against `σ` (a probability measure carried by the compact sphere). -/
noncomputable def piProj (n k : ℕ) (g : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  if h : ∃ p ∈ harmonicSpace n k, ∀ y ∈ harmonicSpace n k,
      ∫ x, (MvPolynomial.eval x g - MvPolynomial.eval x p) * MvPolynomial.eval x y
        ∂(SphereSOS.Rate.sigma n) = 0
  then h.choose else 0

end PolySphereLP


