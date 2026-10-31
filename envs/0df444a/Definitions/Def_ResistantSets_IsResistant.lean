-- Prove2me | Definitions.Def_ResistantSets_IsResistant
-- name    : ResistantSets_IsResistant
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:22.044853+00:00
-- url     : https://prove2.me/theorems/95c9e8b6-671a-4f86-b748-fd4f39515451
-- title:
--   Resistant set $S\subseteq\{0,1\}^n$
-- statement:
--   Let $S\subseteq\{0,1\}^n$. For a point $x$, the **induced clutter** of $S$ with respect to $x$ is the clutter over $[n]$ whose members are
--   $$
--   \operatorname{ind}(S\triangle x)=\text{the minimal sets of }\{C\subseteq[n] : \chi_C\in S\triangle x\}.
--   $$
--   The set $S$ is **resistant** if, for every point $x$, the members of $\operatorname{ind}(S\triangle x)$ are pairwise disjoint.
--
--   Resistant sets are cube-ideal, so the cuboids of resistant sets are ideal clutters; this is the class the whole mission studies. For instance $R_{1,1}=\{000,110,101,011\}$ is resistant, while the fragile set $\{101,011\}$ is not.
--
--   **Formalization Note** The members of the induced clutter are read off as the supports of the minimal points of $S\triangle x$ (`IsMinimalPoint`); two distinct members are disjoint when no coordinate is $1$ in both. The condition is imposed for every $x$; for feasible $x$ it holds trivially.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.3, §1.1 (induced clutter; "We say that S is resistant if for every induced clutter, the members are pairwise disjoint")

import Mathlib
import Definitions.Def_ResistantSets_twist
import Definitions.Def_ResistantSets_IsMinimalPoint

namespace ResistantSets

/-- **Resistant set** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1.1, p.3): "Take an integer n ≥ 1 and a set S ⊆ {0,1}ⁿ. We say that
S is resistant if for every induced clutter, the members are pairwise disjoint." The induced
clutter of `S` with respect to `x` has as members the minimal sets of
`{C ⊆ [n] : χ_C ∈ S △ x}` (p.3), i.e. the supports of the minimal points of `S △ x`.

**Formalization Note** The clutter is not built: its members are read off as the supports of the
inclusion-minimal points of `twist S x`, and two distinct members are disjoint when no
coordinate is `true` in both. The condition is required for every `x`; for a feasible `x`
the only minimal point is `0` (the clutter `{∅}`), where it holds trivially. -/
def IsResistant {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∀ x : Fin n → Bool, ∀ a b : Fin n → Bool,
    IsMinimalPoint (twist S x) a → IsMinimalPoint (twist S x) b → a ≠ b →
      ∀ i, ¬ (a i = true ∧ b i = true)

end ResistantSets


