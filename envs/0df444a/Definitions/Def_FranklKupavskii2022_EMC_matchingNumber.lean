-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
-- name    : FranklKupavskii2022_EMC_matchingNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:12:38.100837+00:00
-- url     : https://prove2.me/theorems/04dc8eba-1a38-44c5-80a8-0ea28e1c9002
-- title:
--   Matching number $\nu(\mathcal F)$ of a set family
-- statement:
--   Let $\mathcal F$ be a finite family of finite sets. A **matching** in $\mathcal F$ is a subfamily $\mathcal M\subseteq\mathcal F$ whose members are pairwise disjoint. The **matching number** of $\mathcal F$ is the largest size of a matching:
--
--   $$
--   \nu(\mathcal F)=\max\{|\mathcal M| : \mathcal M\subseteq\mathcal F,\ M\cap M'=\emptyset \text{ for all distinct } M,M'\in\mathcal M\}.
--   $$
--
--   The condition $\nu(\mathcal F)\le s$ says that $\mathcal F$ contains no $s+1$ pairwise disjoint members; it is the constraint of the Erdős Matching Conjecture.
--
--   **Formalization Note** Families are finite sets of finite sets of natural numbers. Since a matching is a subfamily, its members are distinct sets; $\nu(\emptyset)=0$, and a family containing the empty set has $\nu\ge 1$.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 1, p. 1 (definition of matching and ν(F))

import Mathlib

namespace FranklKupavskii2022.EMC

/-- The matching number `ν(F)` of a family of finite sets (Frankl–Kupavskii, *The Erdős Matching
Conjecture and concentration inequalities*, arXiv:1806.08855v3, Sect. 1, p. 1): "A matching in F
is a collection of pairwise disjoint sets in F. We denote by ν(F) the matching number of F, that
is, the maximum size of a matching in F."

**Formalization Note.** A matching is a *subfamily* `M ⊆ F` whose distinct members are pairwise
disjoint, so its members are distinct sets; `ν(F)` is the largest cardinality of such a
subfamily (a finite maximum; `ν(∅) = 0`). A family containing `∅` has `ν ≥ 1`, since `{∅}` is
a matching of size one. -/
def matchingNumber (F : Finset (Finset ℕ)) : ℕ :=
  (F.powerset.filter (fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B)).sup Finset.card

end FranklKupavskii2022.EMC


