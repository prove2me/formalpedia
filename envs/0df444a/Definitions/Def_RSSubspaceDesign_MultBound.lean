-- Prove2me | Definitions.Def_RSSubspaceDesign_MultBound
-- name    : RSSubspaceDesign_MultBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:06.159952+00:00
-- url     : https://prove2.me/theorems/eb1ac3fb-d0e9-4ddc-b999-3d40fc442c5b
-- title:
--   Display (4.1) — the root-multiplicity condition on evaluation points
-- statement:
--   Let $K$ be a field, $F$ a $K$-algebra (in the paper, a finite field extension), $n,r\ge1$, and $\alpha_1,\dots,\alpha_n\in F$. The points satisfy **condition (4.1)** if for every nonzero $K$-subspace $\mathcal Q\subseteq K[X]_{<nr}$ of dimension at most $2^r$,
--   $$\sum_{i=1}^n\max_{0\ne q\in\mathcal Q}\operatorname{mult}_{\alpha_i}q\;\le\;\max_{0\ne q\in\mathcal Q}\deg q,$$
--   where $\operatorname{mult}_\alpha q$ is the multiplicity of $\alpha$ as a root of $q$ (viewed in $F[X]$).
--
--   Polynomials of a low-dimensional space of bounded degree cannot vanish to high order at many of the points simultaneously. This is clause (ii) of Definition 4.1 and the last property of Theorem 7.2.
--
--   **Formalization Note** Both maxima are over the finite nonempty set $\mathcal Q\setminus\{0\}$ and are attained, so the condition is stated in the equivalent form: for every choice $q_i\in\mathcal Q\setminus\{0\}$ ($i=1,\dots,n$) there is $q_0\in\mathcal Q\setminus\{0\}$ with $\sum_i\operatorname{mult}_{\alpha_i}q_i\le\deg q_0$. Here $nr$ is the product $n\cdot r$.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Definition 4.1 (ii), display (4.1), p.18 (PDF p.20)

import Mathlib

open Polynomial

namespace RSSubspaceDesign

/-- **Display (4.1), Definition 4.1 (ii).** Alrabiah–Goyal–Guruswami, arXiv:2610.36215 (held
version, sha256 cf26424b…f36206), Definition 4.1 (ii), p.18.

Points `α₁, …, αₙ ∈ F` satisfy (4.1) for the parameters `n, r` if for every nonzero `K`-subspace
`Q ⊆ K[X]_{<nr}` of dimension at most `2^r`,
`∑ᵢ max_{0 ≠ q ∈ Q} mult_{αᵢ} q ≤ max_{0 ≠ q ∈ Q} deg q`,
where `mult_α q` is the multiplicity of `α` as a root of `q`.

**Formalization Note.** Both maxima range over the finite nonempty set `Q ∖ {0}` and are attained,
so (4.1) is stated in its equivalent choice-function form: for every choice `qs i ∈ Q ∖ {0}` there
is `q₀ ∈ Q ∖ {0}` with `∑ᵢ mult_{αᵢ}(qs i) ≤ deg q₀`. This avoids the junk values of `⨆`.
`mult_α q` is `rootMultiplicity α (q.map (algebraMap K F))`. `K[X]_{<nr}` is `degreeLT K (n * r)`
(the product `n·r`), and the dimension bound is `2 ^ r`. Coordinates are `Fin n`. -/
def MultBound (K : Type*) {F : Type*} [Field K] [CommRing F] [Algebra K F] (n r : ℕ)
    (α : Fin n → F) : Prop :=
  ∀ Q : Submodule K K[X], Q ≤ degreeLT K (n * r) → Q ≠ ⊥ → Module.finrank K Q ≤ 2 ^ r →
    ∀ qs : Fin n → K[X], (∀ i, qs i ∈ Q ∧ qs i ≠ 0) →
      ∃ q₀ ∈ Q, q₀ ≠ 0 ∧
        ∑ i, ((qs i).map (algebraMap K F)).rootMultiplicity (α i) ≤ q₀.natDegree

end RSSubspaceDesign


