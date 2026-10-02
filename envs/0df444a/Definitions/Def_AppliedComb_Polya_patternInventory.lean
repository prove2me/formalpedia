-- Prove2me | Definitions.Def_AppliedComb_Polya_patternInventory
-- name    : AppliedComb_Polya_patternInventory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:42:38.444562+00:00
-- url     : https://prove2.me/theorems/21109ce3-0d51-45a1-8310-ea121e9c4285
-- title:
--   Section 15.4.2 — colorings, the equivalence induced by G, and the pattern inventory
-- statement:
--   Let $S$ be a finite set and $c_1, \ldots, c_m$ colors. A **coloring** of $S$ is a map $f : S \to \{c_1, \ldots, c_m\}$; let $\mathcal C$ be the set of all of them. A permutation $\pi$ of $S$ acts on colorings by $\pi^*(f) = f \circ \pi^{-1}$, carrying the color at $s$ to $\pi(s)$. For a permutation group $G$ of $S$, two colorings are **equivalent**, $f \sim f'$, when $\pi^*(f) = f'$ for some $\pi \in G$; this is an equivalence relation on $\mathcal C$.
--
--   The **weight** of a coloring $f$ is the monomial $c_1^{a_1} \cdots c_m^{a_m}$ in commuting variables, where $a_i$ is the number of elements of $S$ that $f$ colors $c_i$:
--
--   $$w(f) = \prod_{s \in S} f(s).$$
--
--   The **generating function for the number of nonequivalent colorings** (the **pattern inventory**) is the polynomial in $c_1, \ldots, c_m$ whose coefficient of $c_1^{a_1}\cdots c_m^{a_m}$ is the number of equivalence classes of colorings that use each color $c_i$ exactly $a_i$ times; it is the sum over the equivalence classes of the weight of a representative:
--
--   $$\sum_{\langle f\rangle \in \mathcal C/\sim} w(f).$$
--
--   **Formalization Note.** Colors are `Fin m` (index `i` is $c_{i+1}$), colorings are `S → Fin m`, and $\sim$ is `colorSetoid G m`, with `f ∼ f'` iff `∃ π ∈ G, f' = f ∘ π⁻¹`. The pattern inventory is an element of `MvPolynomial (Fin m) ℚ`; each class contributes the weight of the representative chosen by `Quotient.out`. That the weight does not depend on the representative is part of what Theorem 15.11 asserts, not an assumption.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 294, 297–298 and 301–303, Sections 15.1, 15.3, 15.4.2

import Mathlib

namespace AppliedComb.Polya

open MvPolynomial

/-- Keller–Trotter, Sections 15.1 and 15.3 (pp. 294, 297–298). The colorings of `S` with the `m`
colors `c_1, …, c_m` are the maps `f : S → Fin m` (color index `i : Fin m` stands for
`c_{i+1}`). A permutation `π` of `S` acts on colorings by `π^*(f) = f ∘ π⁻¹` (the color that `f`
puts at `s` is carried to `π(s)`), and two colorings are equivalent, `f ∼ f'`, when
`π^*(f) = f'` for some `π ∈ G`. This is the equivalence relation on colorings induced by the
permutation group `G` (a subgroup of `Equiv.Perm S`). -/
def colorSetoid {S : Type*} (G : Subgroup (Equiv.Perm S)) (m : ℕ) : Setoid (S → Fin m) where
  r f f' := ∃ π ∈ G, f' = f ∘ ⇑π⁻¹
  iseqv := by
    refine ⟨fun f => ⟨1, G.one_mem, by simp⟩, ?_, ?_⟩
    · rintro f f' ⟨π, hπ, rfl⟩
      refine ⟨π⁻¹, G.inv_mem hπ, ?_⟩
      funext s
      simp
    · rintro f f' f'' ⟨π, hπ, rfl⟩ ⟨τ, hτ, rfl⟩
      refine ⟨τ * π, G.mul_mem hτ hπ, ?_⟩
      funext s
      simp [mul_inv_rev]

/-- The weight of a coloring `f : S → Fin m`: the monomial `c_1^{a_1} ⋯ c_m^{a_m}` in commuting
variables `c_1, …, c_m`, where `a_i` is the number of elements of `S` that `f` colors `c_i`. It
is written as the product over `s ∈ S` of the variable of the color of `s`. -/
noncomputable def colorWeight {S : Type*} [Fintype S] {m : ℕ} (f : S → Fin m) :
    MvPolynomial (Fin m) ℚ :=
  ∏ s : S, X (f s)

open Classical in
/-- Keller–Trotter, Section 15.4.2 (pp. 301–303). The generating function for the number of
nonequivalent colorings of `S` (the *pattern inventory*): the polynomial in the colors
`c_1, …, c_m` whose coefficient of `c_1^{a_1} ⋯ c_m^{a_m}` is the number of equivalence classes
of colorings (under the relation `colorSetoid G m` induced by `G`) that use color `c_i` exactly
`a_i` times. It is the sum, over the equivalence classes, of the weight of a representative
(`Quotient.out`) of the class. -/
noncomputable def patternInventory {S : Type*} [Fintype S] (G : Subgroup (Equiv.Perm S))
    (m : ℕ) : MvPolynomial (Fin m) ℚ :=
  ∑ q : Quotient (colorSetoid G m), colorWeight q.out

end AppliedComb.Polya


