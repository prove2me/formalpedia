-- Prove2me | Definitions.Def_SteurerHDX_lambdaTau
-- name    : SteurerHDX_lambdaTau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:08.833648+00:00
-- url     : https://prove2.me/theorems/09eaab7e-053b-4bb4-95ea-62a5664ec8ef
-- title:
--   $\lambda_2(\tau)$: second eigenvalue of the walk on the 1-skeleton of a link
-- statement:
--   For a face $\tau$ of a complex $\mathcal X$, $\lambda_2(\tau)$ is the second eigenvalue (with multiplicity) of the simple random walk on the 1-skeleton of the link $\mathcal X_\tau$, i.e. of $D^{-1}A$ for the $0/1$ adjacency matrix $A$ of that graph.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Definition 2.2, p.3

import Mathlib
import Definitions.Def_SteurerHDX_link
import Definitions.Def_SteurerHDX_skeleton1
import Definitions.Def_SteurerHDX_lambdaTwo

namespace SteurerHDX

/-- **λ₂(τ) of a link.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Definition 2.2, p.3: "We define λ₂(τ) as the 2nd-eigenvalue
of the simple random walk on the 1-skeleton of X_τ."

**Formalization Note.** The simple random walk on a graph G is D⁻¹A for the 0/1 adjacency matrix
A of G, so λ₂(τ) = `lambdaTwo` of the adjacency matrix of `skeleton1 (link X τ)`. -/
noncomputable def lambdaTau {V : Type*} [DecidableEq V] (X : Finset (Finset V))
    (τ : Finset V) : ℝ := by
  classical
  exact lambdaTwo ((skeleton1 (link X τ)).adjMatrix ℝ)

end SteurerHDX


