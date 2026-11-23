-- Prove2me | Definitions.Def_SpatialDemandEq_Optimal_Supplement_MMatrix
-- name    : SpatialDemandEq_Optimal_Supplement_MMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:36:33.550804+00:00
-- url     : https://prove2.me/theorems/0443854c-e53f-4b52-b1a9-fa3a7ec4c006
-- title:
--   §3.3, p. 11 — M-matrix: nonpositive off-diagonal entries and eigenvalues with positive real part
-- statement:
--   Following Carlsson, Peng and Ryzhov (after Young 1971), a real square matrix $C$ indexed by a finite set is an **M-matrix** if
--
--   1. its off-diagonal entries are nonpositive: $C_{ij} \le 0$ for all $i \ne j$; and
--   2. every eigenvalue of $C$ has positive real part:
--   $$\operatorname{Re} z > 0 \quad \text{for every } z \in \mathbb C \text{ with } \det(zI - C) = 0 .$$
--
--   Eigenvalues are taken over $\mathbb C$, so complex eigenvalues of a real matrix are included. The paper uses this notion in Lemma 4, where $I - D$ is shown to be an M-matrix, and in Theorem 3 through the monotonicity of M-matrices ($Cv \ge 0 \Rightarrow v \ge 0$).
--
--   **Formalization Note** The eigenvalues are the points of the spectrum of $C$ viewed as a complex matrix (`spectrum ℂ (C.map (algebraMap ℝ ℂ))`), which for a finite square matrix are exactly the roots of its characteristic polynomial. This is the paper's definition; it is not replaced by the equivalent-for-Z-matrices "nonnegative inverse" characterization.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 11, §3.3, definition of M-matrix

import Mathlib

namespace SpatialDemandEq.Optimal.Supplement

/-- An M-matrix in the sense of Carlsson, Peng & Ryzhov, p. 11 (after Young 1971): a real square
matrix `C` whose off-diagonal entries are nonpositive (`C i j ≤ 0` for `i ≠ j`) and all of whose
eigenvalues, taken over `ℂ`, have positive real part. Eigenvalues are the points of the spectrum
of `C` viewed as a complex matrix. -/
def IsMMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℝ) : Prop :=
  (∀ i j, i ≠ j → C i j ≤ 0) ∧
    ∀ z ∈ spectrum ℂ (C.map (algebraMap ℝ ℂ)), 0 < z.re

end SpatialDemandEq.Optimal.Supplement


