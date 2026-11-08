-- Prove2me | Definitions.Def_UniversalSubmod_threshSet
-- name    : UniversalSubmod_threshSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:51:30.018138+00:00
-- url     : https://prove2.me/theorems/1e3ee337-aa81-4872-a685-aeeda25f6c06
-- title:
--   Threshold sets $R_z(t)=\{i : \langle v_i,z\rangle\ge t\}$
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb R^k$, $z\in\mathbb R^k$ and $t\in\mathbb R$. The **threshold set** is
--   $$
--   R_z(t)=\{i\in[n] : \langle v_i,z\rangle\ge t\},
--   $$
--   the elements whose vectors lie on the far side of the hyperplane with normal $z$ at level $t$. With $z$ a Gaussian vector and $t$ a random threshold this is Gaussian (random-hyperplane) rounding; with $z$ on a grid it produces the members of the universal family.
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)` with its standard inner product. The unit-norm condition $\|v_i\|=1$ is not part of the definition; every theorem using it assumes it.
-- source:
--   Adamczyk, Ueltzen, Vondrák, Optimal universal sets for submodular functions, manuscript (Nov. 3, 2026; sha256 8a53c0912e8ad39b1019cbabfbde98980fd3eea456a8c7e5b28eb55d58343714), Theorem 2.4 and Lemma 2.6, pp.7–8; §4.3, p.13

import Mathlib

namespace UniversalSubmod

open scoped RealInnerProductSpace

/-- **Threshold sets** `R_z(t) = {i ∈ [n] : ⟨vᵢ, z⟩ ≥ t}` for vectors `v₁, …, vₙ ∈ ℝ^k`,
`z ∈ ℝ^k` and `t ∈ ℝ` (Adamczyk, Ueltzen, Vondrák, *Optimal universal sets for submodular
functions*, manuscript of November 3, 2026, Theorem 2.4 and Lemma 2.6, pp.7–8, and §4.3, p.13).

**Formalization Note.** `ℝ^k` is `EuclideanSpace ℝ (Fin k)` with its standard inner product
`⟪·,·⟫`; the ground set `[n]` is `Fin n`. The unit-norm condition on the `vᵢ` is not part of the
definition; every statement using it assumes `‖vᵢ‖ = 1` as the paper does. -/
noncomputable def threshSet {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin k))
    (z : EuclideanSpace ℝ (Fin k)) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => t ≤ ⟪v i, z⟫)

end UniversalSubmod


