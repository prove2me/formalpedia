-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
-- name    : ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:16:30.068641+00:00
-- url     : https://prove2.me/theorems/2c2d096e-879b-4d24-bf2a-c0eae97567e6
-- title:
--   Active k-generation and active generation in the limit
-- statement:
--   Let $C$ be a family of infinite languages over a string universe $U$, and choose a repetition convention $q\in\{\mathrm R,\mathrm{NR}\}$. Write $\operatorname{Correct}_{q}(G,L,x,t)$ for correctness of the generator on the full injective enumeration $x$ of $L$ at time $t$ under that convention. For a positive integer $k$,
--
--   $$
--   \operatorname{Act}_{k,q}(C)\iff
--   \exists G:U^\star\to U\ \forall L\in C\ \exists x\text{ enumerating }L\ \forall t\ge k,
--   \operatorname{Correct}_{q}(G,L,x,t).
--   $$
--
--   Active generation in the limit instead means
--
--   $$
--   \operatorname{Act}_{\infty,q}(C)\iff
--   \exists G:U^\star\to U\ \forall L\in C\ \exists x\text{ enumerating }L\ \exists t^\star\ge1\ \forall t\ge t^\star,
--   \operatorname{Correct}_{q}(G,L,x,t).
--   $$
--
--   There is one generator for the entire collection. The favorable enumeration can depend on the language and generator; the finite success threshold in the limit definition is chosen after the enumeration. These predicates measure how many received examples suffice for sustained generation.
--
--   **Formalization Note** Thresholds are natural numbers with explicit positivity, and at stream index $n$ the test is $k\le n+1$ or $t^\star\le n+1$. Zero is outside the domain of active k-generation. NR correctness still excludes every previous output, even those before the threshold. No increasing-order presentation or global freshness requirement is added.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Definitions 2.1–2.2 and 2.7, printed pp.4–6 (PDF pp.5–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Definition 2.2 with Definition 2.7's repetition convention.
The generator is fixed before the language and its favorable full presentation are chosen.
Only positive thresholds are in the paper's domain. -/
def ActiveKGeneratable {U : Type} (mode : Repetition)
    (C : LanguageCollection U) (k : ℕ) : Prop :=
  0 < k ∧ ∃ G : Generator U, ∀ L ∈ C, ∃ x : ℕ → U,
    IsEnumeration L x ∧ ∀ n : ℕ, k ≤ n + 1 → CorrectAt mode G L x n

/-- Definition 2.1 with Definition 2.7: one generator, and for each language a favorable
full presentation and a finite positive success time. All earlier outputs still count for NR. -/
def ActiveLimitGeneratable {U : Type} (mode : Repetition)
    (C : LanguageCollection U) : Prop :=
  ∃ G : Generator U, ∀ L ∈ C, ∃ x : ℕ → U,
    IsEnumeration L x ∧ ∃ tStar : ℕ, 0 < tStar ∧
      ∀ n : ℕ, tStar ≤ n + 1 → CorrectAt mode G L x n

end ActiveLanguageGeneration.Hierarchy


