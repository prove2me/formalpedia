-- Prove2me | Definitions.Def_ResistantSets_reflProd
-- name    : ResistantSets_reflProd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:40.52605+00:00
-- url     : https://prove2.me/theorems/82c28aa7-ca8f-45d1-b32a-350d478a9c46
-- title:
--   Reflective product $S_1\ast S_2$
-- statement:
--   For $S_1\subseteq\{0,1\}^{n_1}$ and $S_2\subseteq\{0,1\}^{n_2}$, the **reflective product** is
--   $$
--   S_1\ast S_2=(S_1\times S_2)\cup(\overline{S_1}\times\overline{S_2})\subseteq\{0,1\}^{n_1+n_2},
--   $$
--   where $\overline{S_i}$ is the complement of $S_i$ in its cube. A point $(x,y)$ belongs to $S_1\ast S_2$ exactly when $x\in S_1$ and $y\in S_2$ hold together or fail together.
--
--   The reflective product builds the sets $R_{k,1}$ and $R_5$, and it preserves resistance (Theorem 1.7 (3)).
--
--   **Formalization Note** The first $n_1$ coordinates of a point of $\{0,1\}^{n_1+n_2}$ form $x$ and the last $n_2$ form $y$.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.4, §1.1 (product, coproduct and reflective product)

import Mathlib

namespace ResistantSets

/-- **Reflective product** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.1, p.4): for `S₁ ⊆ {0,1}^{n₁}` and `S₂ ⊆ {0,1}^{n₂}`,
`S₁ ∗ S₂ := (S₁ × S₂) ∪ (S̄₁ × S̄₂)`, where `S̄` is the complement of `S` in its cube.

**Formalization Note** A point of `{0,1}^{n₁} × {0,1}^{n₂}` is a point `z` of `{0,1}^{n₁+n₂}`
whose first `n₁` coordinates form `x` and last `n₂` coordinates form `y`. So `z ∈ S₁ ∗ S₂`
iff `x ∈ S₁ ∧ y ∈ S₂` or `x ∉ S₁ ∧ y ∉ S₂`. -/
def reflProd {n₁ n₂ : ℕ} (S₁ : Finset (Fin n₁ → Bool)) (S₂ : Finset (Fin n₂ → Bool)) :
    Finset (Fin (n₁ + n₂) → Bool) :=
  Finset.univ.filter fun z =>
    ((fun i => z (Fin.castAdd n₂ i)) ∈ S₁ ∧ (fun j => z (Fin.natAdd n₁ j)) ∈ S₂) ∨
    ((fun i => z (Fin.castAdd n₂ i)) ∉ S₁ ∧ (fun j => z (Fin.natAdd n₁ j)) ∉ S₂)

end ResistantSets


