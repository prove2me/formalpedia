-- Prove2me | Definitions.Def_HDXConc_SecondEigLE
-- name    : HDXConc_SecondEigLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:03.319652+00:00
-- url     : https://prove2.me/theorems/bd751375-edc8-41ae-939e-48e067593439
-- title:
--   $\lambda_2$ of a weighted random walk is at most $\lambda$, in Rayleigh form
-- statement:
--   Let $W$ be a finite set with weights $w:W\times W\to\mathbb R$ and degrees $\deg v=\sum_{u\in W}w(v,u)$. The predicate says that for every $g:W\to\mathbb R$ with $\sum_{v\in W}\deg v\,g(v)=0$,
--
--   $$\sum_{u,v\in W}w(u,v)\,g(u)\,g(v)\le\lambda\sum_{v\in W}\deg v\,g(v)^2.$$
--
--   For symmetric nonnegative weights with positive degrees and $|W|\ge2$, this says exactly that the second largest eigenvalue of the random walk $Ah(v)=\frac{1}{\deg v}\sum_{u}w(v,u)h(u)$ is at most $\lambda$. Indeed, $A$ is self-adjoint for the inner product weighted by $\deg$, the constants are eigenvectors with the top eigenvalue $1$, and Courant–Fischer gives the second eigenvalue as the maximal Rayleigh quotient on the orthogonal complement of the constants.
--
--   The predicate is the mission's form of $\lambda(G)\le\lambda$. A negative $\lambda$ is meaningful.
--
--   **Formalization Note.** The degrees are those of the weights given to the predicate, so a change of weights changes the stationary measure with them.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), §2.1 "Expansion", p.11

import Mathlib

namespace HDXConc

/-!
# "The second eigenvalue of a weighted random walk is at most `λ`"

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), §2.1 "Expansion", p.11.

**Formalization Note.** For symmetric nonnegative weights `w` on a finite vertex set `W` with positive degrees
`deg v = ∑_{u ∈ W} w v u`, the walk `A h (v) = (1 / deg v) ∑_{u ∈ W} w v u · h u` is self-adjoint for the inner
product weighted by `deg`, and the constants are its eigenvectors with eigenvalue `1`. By Courant–Fischer, when
`|W| ≥ 2` its second largest eigenvalue `λ₂(A)` is at most `lam` exactly when the Rayleigh quotient is at most
`lam` on the `deg`-orthogonal complement of the constants. That is the predicate below. It uses the degrees of
the weights it is given, needs no sorting of eigenvalues, and has no junk value. For `w = π₂` this is the paper's
`A_G` (p.11), since `π₁(v) = (1/2) ∑_u π₂({u, v})`.
-/

variable {V : Type*}

/-- The weighted degree `deg v = ∑_{u ∈ W} w v u`. -/
def weightedDeg (W : Finset V) (w : V → V → ℝ) (v : V) : ℝ := ∑ u ∈ W, w v u

/-- `λ₂(A) ≤ lam` for the random walk `A` of the weighted graph `(W, w)`, in Rayleigh form: for all
`g` with `∑_{v ∈ W} deg v · g v = 0`, we have
`∑_{u, v ∈ W} w u v · g u · g v ≤ lam · ∑_{v ∈ W} deg v · (g v)²`. -/
def SecondEigLE (W : Finset V) (w : V → V → ℝ) (lam : ℝ) : Prop :=
  ∀ g : V → ℝ, ∑ v ∈ W, weightedDeg W w v * g v = 0 →
    ∑ u ∈ W, ∑ v ∈ W, w u v * g u * g v ≤ lam * ∑ v ∈ W, weightedDeg W w v * (g v) ^ 2

end HDXConc


