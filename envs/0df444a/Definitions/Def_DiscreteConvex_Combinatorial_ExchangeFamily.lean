-- Prove2me | Definitions.Def_DiscreteConvex_Combinatorial_ExchangeFamily
-- name    : DiscreteConvex_Combinatorial_ExchangeFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:25.259635+00:00
-- url     : https://prove2.me/theorems/9a84edf3-0c38-4d35-a0d4-d4c5d0ce29ee
-- title:
--   Simultaneous exchange axiom (B) for a base family
-- statement:
--   A family $\mathcal B$ of subsets of a finite ground set $V$ satisfies Murota's **simultaneous exchange axiom (B)** if for every $J, J' \in \mathcal B$ and every $i \in J \setminus J'$ there exists $j \in J' \setminus J$ such that both $J - i + j := (J\setminus\{i\})\cup\{j\}$ and $J' + i - j := (J'\setminus\{j\})\cup\{i\}$ again lie in $\mathcal B$.
--
--   A pair $(V,\mathcal B)$ with $\mathcal B$ nonempty and satisfying (B) is a **matroid** with base family $\mathcal B$. This is the classical (simultaneous) exchange axiom, distinct from — though classically equivalent to — the single-element exchange axiom used elsewhere in the literature.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, axiom (B).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, axiom (B)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, axiom (B): the simultaneous exchange
property of a base family. This is the definitional predicate behind Theorem 2.29 and
Theorem 2.32 in `DiscreteConvex.Combinatorial`.
-/

namespace DiscreteConvex.Combinatorial

/-- A family `𝓑` of subsets of a finite ground set `V` satisfies Murota's **simultaneous
exchange axiom (B)** if for every `J, J' ∈ 𝓑` and every `i ∈ J \ J'` there is some
`j ∈ J' \ J` such that both `J - i + j` and `J' + i - j` again lie in `𝓑`. A matroid's base
family is exactly a nonempty family satisfying this axiom. -/
def ExchangeFamily {V : Type*} [DecidableEq V] (𝓑 : Finset (Finset V)) : Prop :=
  ∀ J ∈ 𝓑, ∀ J' ∈ 𝓑, ∀ i ∈ J \ J', ∃ j ∈ J' \ J,
    insert j (J.erase i) ∈ 𝓑 ∧ insert i (J'.erase j) ∈ 𝓑

end DiscreteConvex.Combinatorial


