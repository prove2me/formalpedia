-- Prove2me | Definitions.Def_DDNNFNeg_IsRectangle
-- name    : DDNNFNeg_IsRectangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:05.329738+00:00
-- url     : https://prove2.me/theorems/e7d631b4-e770-4544-aa2d-0b775d9814e1
-- title:
--   Combinatorial rectangle $S \times T$ with respect to $(A, B)$
-- statement:
--   A set $R \subseteq \{0,1\}^X$ is a **(combinatorial) rectangle** with respect to the partition $(A, B)$ of $X$ if $R = S \times T$ for some $S \subseteq \{0,1\}^A$ and $T \subseteq \{0,1\}^B$, where an assignment $x$ is identified with the pair $(x|_A, x|_B)$ of its restrictions.
--
--   **Formalization Note** $B = X \setminus A$, and $R$ is the set of $x$ with $x|_A \in S$ and $x|_B \in T$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.2, p.8

import Mathlib

namespace DDNNFNeg

/-- `R ⊆ {0,1}^X` is a (combinatorial) rectangle with respect to the partition `(A, Aᶜ)` of
`X` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.2, p.8): `R = S × T` for some `S ⊆ {0,1}^A` and `T ⊆ {0,1}^{Aᶜ}`.

**Formalization Note** An assignment `x ∈ {0,1}^X` is identified with the pair
`(x|_A, x|_{Aᶜ})` of its restrictions, so `S × T` is the set of `x` whose restriction to `A`
lies in `S` and whose restriction to `Aᶜ` lies in `T`. -/
def IsRectangle {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X)
    (R : Set (X → Bool)) : Prop :=
  ∃ (S : Set (A → Bool)) (T : Set (↥(Aᶜ) → Bool)),
    R = {x | (fun a : A => x a) ∈ S ∧ (fun b : ↥(Aᶜ) => x b) ∈ T}

end DDNNFNeg


