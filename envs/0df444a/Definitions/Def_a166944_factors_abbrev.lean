-- Prove2me | Definitions.Def_a166944_factors_abbrev
-- name    : a166944_factors_abbrev
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-19T15:42:15.018401+00:00
-- url     : https://prove2.me/theorems/9fc042dd-66b4-451b-aa46-44d7aa1cc1df
-- title:
--   OEIS A166944 - factor predicates as abbreviations, for decision procedures
-- statement:
--   The two factor predicates of the A166944 terminal argument, declared with `abbrev` rather than `def`:
--
--   - $\operatorname{NoSmallFactor}(N,\rho)$: no integer $f$ with $2\le f\le\rho$ divides $N$;
--   - $\operatorname{NoProperFactor}(N)$: no $f$ with $2\le f<N$ divides $N$.
--
--   The distinction from the `def` form in `a166944_factor_layer` is not cosmetic. An `abbrev` is transparent during elaboration, so Lean can synthesise the `Decidable` instance for a bounded universal quantifier over `Fin N`, and `decide` can evaluate concrete instances. A `def` blocks that synthesis. The replay checker decides propositions of exactly this shape -- finitely many indices, each with a divisibility test -- so it needs the abbreviation form.
--
--   Both predicates carry a `D` suffix so they can coexist with the `def` versions in the same namespace and environment; they are definitionally the same statements for any use that does not go through `decide`.
-- source:
--   Derived within this development; same predicates as a166944_factor_layer, in abbreviation form. See https://github.com/tara-sooo/A166944-Lean

/-!
# Factor predicates, as abbreviations

The same two predicates as `a166944_factor_layer`, declared with `abbrev` rather than
`def`. The difference matters for `decide`: an `abbrev` is transparent during
elaboration, so `Decidable` instances for finite `∀` over `Fin` synthesise, while a
`def` blocks them. The replay checker in the terminal argument decides propositions
of exactly that shape, so the abbreviation form is the one it needs.

`NoSmallFactor N root` says no `f` in `[2, root]` divides `N`.
`NoProperFactor N` says no `f` in `[2, N)` does.
-/

namespace A166944Research

/-- No divisor of `N` lies in `[2, root]`. -/
abbrev NoSmallFactorD (N root : Nat) : Prop :=
  ∀ f : Fin (root + 1), 2 ≤ f.val → ¬ f.val ∣ N

/-- No divisor of `N` lies in `[2, N)`. -/
abbrev NoProperFactorD (N : Nat) : Prop :=
  ∀ f : Fin N, 2 ≤ f.val → ¬ f.val ∣ N

end A166944Research


