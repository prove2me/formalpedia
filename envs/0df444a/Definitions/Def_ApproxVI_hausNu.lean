-- Prove2me | Definitions.Def_ApproxVI_hausNu
-- name    : ApproxVI_hausNu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:02.080826+00:00
-- url     : https://prove2.me/theorems/b20dd587-1d38-4b64-bcab-5527857cb349
-- title:
--   Hausdorff metric $H_\nu$ for the weighted max-norm
-- statement:
--   For $A,B\subseteq\mathbb R^d$, the **Hausdorff metric with respect to** $\|\cdot\|_\nu$ is
--
--   $$
--   H_\nu(A,B)=\sup_{x\in A}d_\nu(x,B)\ \vee\ \sup_{y\in B}d_\nu(y,A).
--   $$
--
--   It measures how far apart the values $\tilde Tx$ and $\tilde Ty$ of the perturbed Bellman operator are, which is the quantity in the coupling bound (13).
--
--   **Formalization Note** The suprema are taken in $[0,\infty]$, so $H_\nu$ is $\infty$ on unbounded sets instead of a junk real value.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §5, Definition (Hausdorff metric), pp.14–15

import Mathlib
import Definitions.Def_ApproxVI_distNu

namespace ApproxVI

open scoped ENNReal

/-- The Hausdorff metric with respect to the weighted max-norm, Ramaswamy & Bhatnagar,
*Analyzing Approximate Value Iteration Algorithms*, arXiv:1709.04673v5, §5, Definition,
pp.14–15: `H_ν(A, B) := sup_{x ∈ A} d_ν(x, B) ∨ sup_{y ∈ B} d_ν(y, A)`.

**Formalization Note** The suprema are taken in `ℝ≥0∞`, so `H_ν(A, B)` is a genuine extended
value: `∞` for unbounded sets or when exactly one set is empty, never a junk real `sSup`. -/
noncomputable def hausNu {d : ℕ} (ν : Fin d → ℝ) (A B : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  (⨆ x ∈ A, distNu ν x B) ⊔ (⨆ y ∈ B, distNu ν y A)

end ApproxVI


