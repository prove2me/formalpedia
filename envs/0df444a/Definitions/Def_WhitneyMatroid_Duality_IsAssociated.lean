-- Prove2me | Definitions.Def_WhitneyMatroid_Duality_IsAssociated
-- name    : WhitneyMatroid_Duality_IsAssociated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:24:32.47558+00:00
-- url     : https://prove2.me/theorems/f59e2e4b-5d8d-448c-9bde-18274c436c74
-- title:
--   The matroid associated with a subspace of $E_n$ (§12, Theorem 27)
-- statement:
--   Let $E_n$ be $n$-dimensional Euclidean space with coordinates $x_1,\dots,x_n$, and let $H$ be a hyperplane through the origin in $E_n$, i.e. a linear subspace of any dimension. For a set $S\subseteq\{1,\dots,n\}$ of coordinates let $E'_S$ be the coordinate subspace of $E_n$ containing the $x_i$ axes for $i\in S$, and let
--
--   $$
--   \pi_S : E_n \to E'_S,\qquad (x_1,\dots,x_n)\mapsto (x_i)_{i\in S}
--   $$
--
--   be the projection onto it. The **rank** that $H$ gives to $S$ is the dimension of the projection of $H$ onto $E'_S$:
--
--   $$
--   r_H(S) = \dim \pi_S(H).
--   $$
--
--   A matroid $M$ is **associated with $H$** if its elements are $e_1,\dots,e_n$, one corresponding to each coordinate of $E_n$, and every subset $\{e_i : i\in S\}$ has rank $r_H(S)$.
--
--   If $H$ is spanned by the rows of a matrix $\mathbf M$, the projection of $H$ onto $E'_S$ is spanned by the rows of the submatrix of the columns in $S$, so $r_H(S)$ is the rank of those columns (Whitney's (12.1)); the associated matroid is therefore the column matroid of any matrix whose row space is $H$.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)` (coordinates indexed $0,\dots,n-1$) and $H$ is a real `Submodule`. The projection is the linear map to `S → ℝ` keeping the coordinates in $S$, and $r_H(S)$ is the `finrank` of the image of $H$ (not the dimension of $H\cap E'_S$, which is a different set function). The matroid's ground set is all of `Fin n`; its rank `eRk` must equal $r_H$ on every subset. This definition is a predicate on matroids: existence and uniqueness of an associated matroid is Theorem 27.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 525, §12 (b), (12.1), and p. 526, Theorem 27 and its proof

import Mathlib

namespace WhitneyMatroid.Duality

/-- The coordinate projection of Euclidean space `Eₙ` onto the coordinate subspace `E′` spanned by
the axes `x_i`, `i ∈ S`: a point keeps exactly its coordinates indexed by `S`. -/
noncomputable def coordProj {n : ℕ} (S : Set (Fin n)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (S → ℝ) :=
  LinearMap.pi fun i : S => EuclideanSpace.projₗ (𝕜 := ℝ) (i : Fin n)

/-- Whitney §12 and Theorem 27 (p. 526): the rank that the matroid associated with a hyperplane
(linear subspace) `H` of `Eₙ` gives to the set of elements `{e_i : i ∈ S}`, namely the dimension
of the projection of `H` onto the coordinate subspace `E′` of the coordinates in `S`. -/
noncomputable def subspaceRank {n : ℕ} (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (Fin n)) : ℕ :=
  Module.finrank ℝ (H.map (coordProj S))

/-- Whitney §12, Theorem 27: `M` is a matroid associated with the hyperplane through the origin
`H` of `Eₙ`: its elements are `e₁, …, eₙ`, one for each coordinate of `Eₙ` (the whole type
`Fin n` is the ground set), and every subset `S` has rank `subspaceRank H S`. -/
def IsAssociated {n : ℕ} (M : Matroid (Fin n)) (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  M.E = Set.univ ∧ ∀ S : Set (Fin n), M.eRk S = (subspaceRank H S : ℕ∞)

end WhitneyMatroid.Duality


