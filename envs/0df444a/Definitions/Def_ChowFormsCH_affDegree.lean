-- Prove2me | Definitions.Def_ChowFormsCH_affDegree
-- name    : ChowFormsCH_affDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:39.077052+00:00
-- url     : https://prove2.me/theorems/cf1a1b39-d010-465c-8ccf-d5f2c82c801e
-- title:
--   Degree $\deg V$ of a variety: sum of the degrees of its irreducible components
-- statement:
--   The **degree** of an irreducible set $Z\subseteq K^\sigma$ is the largest finite cardinality of an intersection $Z\cap E$ with an affine linear subspace $E$ (Heintz's degree). The **degree of a variety** $V$ is
--   $$
--   \deg V=\sum_{Z \text{ irreducible component of } V}\deg Z .
--   $$
--   For $V\subseteq\mathbb P^n$ the degree of a component is computed on its affine cone.
--
--   The degree enters Definition 3.2 (projective Noether position) and the bound $1-5nD/|B|$ of Lemma 4.8.
--
--   **Formalization Note** For an irreducible variety of dimension $r$ the maximum is attained by a generic affine subspace of codimension $r$, and Heintz's Bézout inequality bounds every finite linear section by the degree; so the supremum over all affine subspaces is the degree. A component of a subset of $\mathbb P^n$ is represented by its punctured cone in $K^{n+1}$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §2.1, p.8 (with [Hei83, Definition 1]); Definition 3.2, p.22; Lemma 4.8, p.33

import Mathlib
import Definitions.Def_ChowFormsCH_comps

set_option autoImplicit false

namespace ChowFormsCH

/-- The degree of an irreducible set `Z ⊆ K^σ` in the sense of Heintz: the largest finite
cardinality of an intersection of `Z` with an affine linear subspace
(Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via Chow forms*,
arXiv:2611.05289, held version, sha256 75e796c6…, §2.1, p.8, "degree", with the paper's reference
[Hei83, Definition 1]).

**Formalization Note** For an irreducible variety of dimension `r` the maximum is attained by a
generic affine subspace of codimension `r`, and Heintz's Bézout inequality bounds every finite
section by the degree, so the supremum over all affine subspaces is the degree. -/
noncomputable def heintzDeg {σ K : Type*} [Field K] (Z : Set (σ → K)) : ℕ :=
  sSup {N : ℕ | ∃ E : AffineSubspace K (σ → K),
    (Z ∩ (E : Set (σ → K))).Finite ∧ (Z ∩ (E : Set (σ → K))).ncard = N}

/-- The degree `deg V` of an affine variety `V ⊆ K^σ`: the sum of the degrees of its irreducible
components (§2.1, p.8: "The degree of a variety V, denoted deg V, is defined as the sum of the
degrees of all irreducible components of V"). -/
noncomputable def affDegree {σ K : Type*} [Field K] (V : Set (AffSp σ K)) : ℕ :=
  ∑ᶠ Z ∈ comps V, heintzDeg (σ := σ) (K := K) Z

/-- The degree `deg V` of `V ⊆ P^n`: the sum over the irreducible components of `V` of the degree
of the component, computed on its affine cone (§2.1, p.8).

**Formalization Note** The degree of an irreducible projective variety equals the Heintz degree of
its affine cone; a component is represented by its punctured cone in `K^{n+1}`, which has the same
finite linear sections as the cone away from the origin. -/
noncomputable def projDegree {n : ℕ} {K : Type*} [Field K] (V : Set (ProjSpace n K)) : ℕ :=
  ∑ᶠ Z ∈ comps V, heintzDeg (Subtype.val '' Z : Set (Fin (n + 1) → K))

end ChowFormsCH


