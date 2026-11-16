-- Prove2me | Definitions.Def_CircTrichotomy_Supplement_IsDisjointMonomial
-- name    : CircTrichotomy_Supplement_IsDisjointMonomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:14:12.957906+00:00
-- url     : https://prove2.me/theorems/0ecb15e8-0530-49ad-bca6-c622400e2a9b
-- title:
--   Disjoint monomials $\Gamma^*a_0\Gamma^*\cdots a_{n-1}\Gamma^*$
-- statement:
--   A **disjoint monomial** over $\Sigma$ is a language
--   $$\Gamma^*a_0\Gamma^*a_1\cdots\Gamma^*a_{n-1}\Gamma^*,$$
--   where $n\in\mathbb N$, $\Gamma\subseteq\Sigma$ and $a_0,\dots,a_{n-1}\in\Sigma\setminus\Gamma$. A word belongs to it iff its letters outside $\Gamma$, read left to right, are exactly $a_0a_1\cdots a_{n-1}$.
--
--   For $n=0$ the disjoint monomial is $\Gamma^*$, which contains the empty word; $\emptyset^*=\{\varepsilon\}$. Boolean combinations of disjoint monomials are clause (6) of Theorem 5.1.
--
--   **Formalization Note** This is the non-modular notion of Straubing [Str82]; the modular disjoint monomials of Definition B.19 (published `IsModDisjointMonomial`) are a different notion. The language is built by concatenation of languages, each $a_i$ standing for the singleton $\{a_i\}$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §B.4, p.29; §2, p.6

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- `Γ*`: the words all of whose letters are in `Γ` (the empty word included). -/
def letterStar {α : Type} (Γ : Set α) : Language α := {w | ∀ a ∈ w, a ∈ Γ}

/-- The language `Γ* a₀ Γ* a₁ ⋯ a_{n−1} Γ*` for the word `as = a₀ ⋯ a_{n−1}` (concatenation of
languages, each letter `a_i` read as the singleton language `{a_i}`). -/
def dmLang {α : Type} (Γ : Set α) (as : List α) : Language α :=
  as.foldl (fun acc a => acc * ({[a]} : Language α) * letterStar Γ) (letterStar Γ)

/-- **Disjoint monomial** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular
Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §B.4, p.29; also
§2, p.6): "A disjoint monomial [Str82] over the alphabet Σ is a language of the form
Γ∗a0Γ∗ . . . an−1Γ∗, where a0, . . . , an−1 ∈ Σ \ Γ and Γ ⊆ Σ."

**Formalization Note** `n ∈ ℕ` may be `0` (the language `Γ*`, which contains the empty word; for
`Γ = ∅` it is `{ε}`). This is the non-modular notion of [Str82]; the modular variant of
Definition B.19 is the published `IsModDisjointMonomial`, a different notion. -/
def IsDisjointMonomial {α : Type} (K : Language α) : Prop :=
  ∃ Γ : Set α, ∃ as : List α, (∀ a ∈ as, a ∉ Γ) ∧ K = dmLang Γ as

end Supplement

end CircTrichotomy


