-- Prove2me | Definitions.Def_PolySphereLP_orthProjT
-- name    : PolySphereLP_orthProjT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:39.29934+00:00
-- url     : https://prove2.me/theorems/0a04a7a8-d2ef-4638-89bb-a49236d5bc72
-- title:
--   Hermitian orthogonal projection $A_W$ onto a subspace of tensors
-- statement:
--   For a complex subspace $W$ of order-$k$ tensors, $A_WT$ is the unique $w\in W$ with $\langle T-w,u\rangle_F=0$ for every $u\in W$: the orthogonal projection of $T$ onto $W$ for the Frobenius inner product.
--
--   **Formalization Note** The tensor space is finite-dimensional and $\langle\cdot,\cdot\rangle_F$ is positive definite, so the projection exists and is unique; the fallback value $0$ of the definition is never used.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Fact 2.3, p.13

import Mathlib
import Definitions.Def_PolySphereLP_Tensor

namespace PolySphereLP

open Classical in
/-- **The Hermitian orthogonal projection `A_W` onto a complex subspace `W` of tensors.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…),
Fact 2.3, p.13: "`A_W` is its Hermitian orthogonal projection"; Frobenius inner product of §2.3.

`orthProjT W T` is the `w ∈ W` with `⟨T − w, u⟩_F = 0` for all `u ∈ W`.

**Formalization Note.** The tensor space is finite-dimensional and `⟨·,·⟩_F` is positive definite, so
this `w` exists and is unique; the `else 0` branch is never taken. -/
noncomputable def orthProjT {n k : ℕ} (W : Submodule ℂ (Tensor n k)) (T : Tensor n k) :
    Tensor n k :=
  if h : ∃ w ∈ W, ∀ u ∈ W, frob (T - w) u = 0 then h.choose else 0

end PolySphereLP


