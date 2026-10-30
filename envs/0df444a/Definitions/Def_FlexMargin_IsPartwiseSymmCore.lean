-- Prove2me | Definitions.Def_FlexMargin_IsPartwiseSymmCore
-- name    : FlexMargin_IsPartwiseSymmCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:19.153516+00:00
-- url     : https://prove2.me/theorems/2af87333-c6b4-43a3-8c72-cd68268f5793
-- title:
--   Clauses (1)–(2) of Definition 2.1
-- statement:
--   For a partition of the products into categories $s_1,\dots,s_T$, a set $U$ of vectors in $\mathbb R^n$ satisfies **clauses (1) and (2) of Definition 2.1** if
--
--   1. $U=U_1\times\dots\times U_T$ is a Cartesian product of sets $U_t$ of vectors indexed by $s_t$ (the demands of different categories vary independently), and
--   2. $U$ is closed under permuting coordinates within each category: if $d\in U$ and $\sigma$ is a permutation of $\{1,\dots,n\}$ mapping each $s_t$ onto itself, then $d_\sigma=(d_{\sigma(1)},\dots,d_{\sigma(n)})\in U$.
--
--   This is Definition 2.1 without its sign condition, so that it applies both to demand sets and to the residual sets $E=\{d-\mu\}$ of Definition 2.2.
--
--   **Formalization Note** Clause (2) is stated for all category-preserving permutations at once, which is equivalent to the page's "for any $\sigma^t\in\Omega(s_t)$, for each $t$".
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2.3, Definition 2.1, p. 14

import Mathlib

namespace FlexMargin

/-- **Clauses (1)–(2) of Definition 2.1 (product structure and within-category symmetry).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2.3, Definition 2.1, p. 14: "An uncertainty set U ⊂ R^n_+ is part-wise independently
symmetric if (1) U = U1 × ··· × UT, and (2) for any dst,−st ∈ U, we have dσt(st),−st ∈ U for any
permutation σt ∈ Ω(st) for each 1 ≤ t ≤ T", with "Ut := {dst | d ∈ U}" and "Ω(st) denote the set of
all permutations of index set st" (p. 14), and "dσ := [dσ(1),...,dσ(n)]" (p. 12).

`IsPartwiseSymmCore cat U` holds for a set `U` of vectors `Fin n → ℝ` when
1. there are sets `U_t` of vectors indexed by the category `s_t = {i | cat i = t}` with
   `U = {d | d restricted to s_t lies in U_t for every t}`, and
2. `U` is closed under `d ↦ d ∘ σ` for every permutation `σ` of `Fin n` that maps each category
   onto itself.

It omits the sign condition `U ⊂ ℝ^n_+`, so that it can also be applied to the residual set `E` of
Definition 2.2; `FlexMargin.IsPartwiseSymm` adds it back.

**Formalization Note.** (1) asks for some family `U_t`; this is equivalent to the page's
`U = U_1 × ⋯ × U_T` with `U_t` the projections (for nonempty `U` the `U_t` must be the projections;
for empty `U` both forms hold). (2) quantifies over all category-preserving permutations at
once, which is equivalent to the page's "any σt ∈ Ω(st) for each t": every within-category
permutation preserves categories, and every category-preserving permutation is a product of
within-category ones. -/
def IsPartwiseSymmCore {n T : ℕ} (cat : Fin n → Fin T) (U : Set (Fin n → ℝ)) : Prop :=
  (∃ Ut : (t : Fin T) → Set ({i : Fin n // cat i = t} → ℝ),
      U = {d | ∀ t, (fun i : {i : Fin n // cat i = t} => d i.1) ∈ Ut t}) ∧
    ∀ d ∈ U, ∀ σ : Equiv.Perm (Fin n), (∀ i, cat (σ i) = cat i) → (fun i => d (σ i)) ∈ U

end FlexMargin


