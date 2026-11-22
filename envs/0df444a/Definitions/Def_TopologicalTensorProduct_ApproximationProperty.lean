-- Prove2me | Definitions.Def_TopologicalTensorProduct_ApproximationProperty
-- name    : TopologicalTensorProduct_ApproximationProperty
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:20:23.380088+00:00
-- url     : https://prove2.me/theorems/64456c55-e62a-4bef-a880-af86c9d7c990
-- title:
--   Grothendieck's approximation property of a topological vector space (uniform convergence on pre-compact sets)
-- statement:
--   This file defines **Grothendieck's approximation property** of a topological vector space, together with the notion of pre-compact subset it refers to.
--
--   Let $E$ be a topological vector space over a non-trivially normed field $\mathbb k$ (in the source: a Hausdorff locally convex space over $\mathbb C$), with continuous dual $E'$.
--
--   1. A subset $K\subseteq E$ is **pre-compact** (totally bounded) if for every neighbourhood $U$ of $0$ there are finitely many points $x_1,\dots,x_n\in E$ with
--   $$K\subseteq\bigcup_{k=1}^{n}(x_k+U).$$
--   2. $E$ has the **approximation property** if the identity map of $E$ lies in the closure of the continuous linear maps of finite rank in $\mathscr L_\gamma(E,E)$, the space of continuous linear endomorphisms with the topology of uniform convergence on pre-compact subsets. Explicitly: for every pre-compact $K\subseteq E$ and every neighbourhood $U$ of $0$ there are $N\ge 0$, functionals $\varphi_1,\dots,\varphi_N\in E'$ and vectors $y_1,\dots,y_N\in E$ such that
--   $$x-\sum_{i=1}^{N}\varphi_i(x)\,y_i\in U\qquad\text{for all }x\in K.$$
--
--   The maps $x\mapsto\sum_i\varphi_i(x)y_i$ are exactly the image of the canonical map $\lambda:E'\otimes E\to\mathscr L(E,E)$, $\lambda(\varphi\otimes f)=\langle\cdot,\varphi\rangle f$, of (C.2.4.6)–(C.2.4.7). In the paper the approximation property is the standing hypothesis under which traces of nuclear operators are computed as matrix traces (§C.3); every nuclear space has it (Lemma C.2.4.16).
--
--   **Formalization Note.** `TopologicalTensorProduct.IsPrecompact K` and `TopologicalTensorProduct.HasApproximationProperty 𝕜 E` are stated with neighbourhoods of $0$ only, so no uniform structure is needed; for a topological group `IsPrecompact` is Mathlib's `TotallyBounded` for the group uniformity. The convergence is uniform on **pre-compact** sets, not on bounded sets (uniform convergence on bounded sets would be a strictly stronger property, which already fails for infinite-dimensional Hilbert spaces). The definition is built on Mathlib alone; `E'` is `StrongDual 𝕜 E` (the type of continuous linear functionals).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 689–690, §C.2.4.5, (C.2.4.6)–(C.2.4.7) and Lemma C.2.4.15(1); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 9.1

import Mathlib

/-!
# Grothendieck's approximation property for topological vector spaces

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix C,
§C.2.4.5, Lemma C.2.4.15 (pp. 689–690), which recalls [H. H. Schaefer, M. P. Wolff,
*Topological Vector Spaces*, 2nd ed., Ch. III, 9.1].

A topological vector space `E` has the *approximation property* if the identity map of `E` lies in
the closure of the continuous linear maps of finite rank for the topology of uniform convergence
on the pre-compact subsets of `E`.
-/

namespace TopologicalTensorProduct

open Topology

/-- A subset `K` of a commutative topological group `X` is *pre-compact* (totally bounded): for
every neighbourhood `U` of `0` it is covered by finitely many translates `x + U`. -/
def IsPrecompact {X : Type*} [AddCommGroup X] [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ U ∈ 𝓝 (0 : X), ∃ t : Finset X, K ⊆ ⋃ x ∈ t, {y : X | y - x ∈ U}

/-- **Grothendieck's approximation property.**  The identity map of `E` is a limit, uniformly on
every pre-compact subset of `E`, of continuous linear maps of finite rank
`x ↦ ∑ i, φ i x • y i` (`φ i ∈ E'`, `y i ∈ E`): for every pre-compact `K ⊆ E` and every
neighbourhood `U` of `0` there is such a map `R` with `x - R x ∈ U` for all `x ∈ K`. -/
def HasApproximationProperty (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] : Prop :=
  ∀ K : Set E, IsPrecompact K → ∀ U ∈ 𝓝 (0 : E),
    ∃ (N : ℕ) (φ : Fin N → StrongDual 𝕜 E) (y : Fin N → E),
      ∀ x ∈ K, x - ∑ i, φ i x • y i ∈ U

end TopologicalTensorProduct


