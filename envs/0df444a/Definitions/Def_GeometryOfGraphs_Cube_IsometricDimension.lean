-- Prove2me | Definitions.Def_GeometryOfGraphs_Cube_IsometricDimension
-- name    : GeometryOfGraphs_Cube_IsometricDimension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:03.253008+00:00
-- url     : https://prove2.me/theorems/dcf336e2-8dab-4856-9164-dc2acb24db8d
-- title:
--   Norms, isometric graph embeddings, and isometric dimension
-- statement:
--   A norm on the real vector space $\mathbb R^d$ is a nonnegative function $N$ that vanishes only at zero, is absolutely homogeneous, and satisfies the triangle inequality. For a finite graph $G$ with graph distance $d_G$, say that $G$ embeds isometrically in dimension $d$ if there are such a norm and vertex map $\varphi$ with
--
--   $$
--   N(\varphi(x)-\varphi(y))=d_G(x,y)\qquad\text{for all vertices }x,y.
--   $$
--
--   The isometric dimension $\dim(G)$ is the least such $d$. This is the central quantity of Section 5 and allows any norm on a real space of the stated dimension.
--
--   **Formalization Note** Every finite-dimensional real normed space can be represented by a norm on $\mathbb R^d$. The natural-number infimum represents the least possible dimension; finite graph metrics have such a realization.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), pp. 218–219, Definition 2.1; p. 229, Section 5.1; https://doi.org/10.1007/BF01200757

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_IsNormFun

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- An isometric realization of the graph metric in a real normed space of dimension `d`. -/
def EmbedsIsometrically {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ N : (Fin d → ℝ) → ℝ, GeometryOfGraphs.Clique.IsNormFun N ∧
    ∃ φ : V → (Fin d → ℝ), ∀ x y, N (φ x - φ y) = (G.dist x y : ℝ)

/-- Least real normed-space dimension of an isometric realization of a graph. -/
noncomputable def isoDim {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {d : ℕ | EmbedsIsometrically G d}

end GeometryOfGraphs.Cube


