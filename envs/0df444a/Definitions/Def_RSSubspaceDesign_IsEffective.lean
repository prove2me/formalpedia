-- Prove2me | Definitions.Def_RSSubspaceDesign_IsEffective
-- name    : RSSubspaceDesign_IsEffective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:16.210307+00:00
-- url     : https://prove2.me/theorems/03302a98-58c9-4301-8df5-366b6e3d6029
-- title:
--   Definition 4.1 — $(n,g,b,r)_{F,K}$-effective evaluation points
-- statement:
--   Let $K\subseteq F$ be fields (finite in the paper) and fix integers $n,g\ge1$, $0\le b\le n$, $r\ge2$. A tuple of $n$ distinct points $A=(\alpha_1,\dots,\alpha_n)\in F^n$ is **$(n,g,b,r)_{F,K}$-effective** if
--
--   1. there are automorphisms $\sigma_1,\dots,\sigma_g$ generating $\mathrm{Gal}(F/K)$ such that $|\{i\in[n]:\sigma_j(\alpha_i)\ne\alpha_i\}|\le b$ for every $j\in[g]$;
--   2. condition (4.1) holds: for every nonzero $K$-subspace $\mathcal Q\subseteq K[X]_{<nr}$ of dimension at most $2^r$, $\sum_i\max_{0\ne q\in\mathcal Q}\operatorname{mult}_{\alpha_i}q\le\max_{0\ne q\in\mathcal Q}\deg q$.
--
--   Effective points are the hypothesis of the subspace-design bound (Theorem 4.2): few points move under each generator, and low-dimensional polynomial spaces cannot vanish heavily on them.
--
--   **Formalization Note** The parameter ranges and the distinctness of the points are clauses of the predicate. $\mathrm{Gal}(F/K)$ is the group of $K$-algebra automorphisms of $F$.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Definition 4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RSSubspaceDesign_MultBound

open Polynomial

namespace RSSubspaceDesign

open Classical in
/-- **Definition 4.1 (Properties required of the evaluation points).** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Definition 4.1, p.18.

Let `K ⊆ F` be finite fields and fix integers `n, g ≥ 1`, `0 ≤ b ≤ n`, `r ≥ 2`. A set of `n`
distinct points `α₁, …, αₙ ∈ F` is `(n, g, b, r)_{F,K}`-effective if
(i) there are automorphisms `σ₁, …, σ_g` generating `Gal(F/K)` such that
`|{i ∈ [n] : σⱼ(αᵢ) ≠ αᵢ}| ≤ b` for every `j ∈ [g]`; and
(ii) for every nonzero `K`-subspace `Q ⊆ K[X]_{<nr}` of dimension at most `2^r`, (4.1) holds
(`MultBound`).

**Formalization Note.** The parameter ranges `n, g ≥ 1`, `b ≤ n`, `r ≥ 2` under which the paper
defines the notion and the distinctness of the points are clauses of the predicate. `Gal(F/K)` is
the group `F ≃ₐ[K] F`; "generating" is `Subgroup.closure (range σ) = ⊤`. Coordinates and generator
indices are `Fin n`, `Fin g` (0-based). The paper's remark that the `σⱼ` commute is a consequence
(the group is cyclic), not a condition. -/
def IsEffective (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] (n g b r : ℕ)
    (α : Fin n → F) : Prop :=
  1 ≤ n ∧ 1 ≤ g ∧ b ≤ n ∧ 2 ≤ r ∧ Function.Injective α ∧
    (∃ σ : Fin g → (F ≃ₐ[K] F), Subgroup.closure (Set.range σ) = ⊤ ∧
      ∀ j, (Finset.univ.filter fun i => σ j (α i) ≠ α i).card ≤ b) ∧
    MultBound K n r α

end RSSubspaceDesign


