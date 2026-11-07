-- Prove2me | Definitions.Def_UniqueOptScores_WeaklyOneGeneric
-- name    : UniqueOptScores_WeaklyOneGeneric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:54.246999+00:00
-- url     : https://prove2.me/theorems/68997a74-0f1d-4e68-afe4-bef645db9662
-- title:
--   Weakly 1-generic oracles
-- statement:
--   An oracle $\chi$ is **weakly 1-generic** if it meets every computably enumerable dense set of finite strings: for every c.e. set $W$ of finite bit strings such that every string has an extension in $W$, some initial segment of $\chi$ (in length-lexicographic order) belongs to $W$. Equivalently, $\chi$ lies in every c.e. dense open subset of oracle Cantor space.
--
--   **Formalization Note** "Computably enumerable" is Mathlib's `REPred` on `List Bool`, and $\sigma \preceq \tau$ is the prefix relation of lists. The identification of oracles with sequences is the length-lexicographic one (p.30).
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Theorem 1.2, p.3; Section 8, p.30 ("A weakly 1-generic oracle meets every c.e. dense open set")

import Mathlib
import Definitions.Def_UniqueOptScores_IsPrefixOf

namespace UniqueOptScores

/-- **Weakly 1-generic oracles.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Theorem 1.2, p.3, and §8, p.30: "A weakly 1-generic oracle meets every c.e. dense open set";
"Identify oracle bits with a binary sequence in length-lexicographic order."

`χ` is weakly 1-generic if for every computably enumerable set `W` of finite strings that is dense
(every string has an extension in `W`), some initial segment of `χ` lies in `W`.

**Formalization Note.** Standard definition, with the length-lexicographic identification of
`List Bool → Bool` with binary sequences (`str`, `IsPrefixOf`); "computably enumerable" is
Mathlib's `REPred`, and `σ <+: τ` is "`σ` is a prefix of `τ`". -/
def WeaklyOneGeneric (χ : List Bool → Bool) : Prop :=
  ∀ W : List Bool → Prop, REPred W → (∀ σ : List Bool, ∃ τ, σ <+: τ ∧ W τ) →
    ∃ τ, W τ ∧ IsPrefixOf τ χ

end UniqueOptScores


