-- Prove2me | Definitions.Def_NKtLB_Supplement_PromiseIn
-- name    : NKtLB_Supplement_PromiseIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:25:45.605228+00:00
-- url     : https://prove2.me/theorems/573c03b7-de2e-4da0-9f9d-6da8cc99b7e8
-- title:
--   Membership of a promise problem in a class of languages
-- statement:
--   For a promise problem $\Pi=(\mathrm{YES},\mathrm{NO})$ and a class $\mathcal C$ of languages, "$\Pi\in\mathcal C$ if there is a language $L\in\mathcal C$ such that $\mathrm{YES}\subseteq L$ and $\mathrm{NO}\subseteq\{0,1\}^*\setminus L$" (p.10). "$\Pi\notin\mathcal C$" is its negation: no language of $\mathcal C$ separates YES from NO (p.12).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.2, p.10 (and p.12)

import Mathlib

namespace NKtLB.Supplement

/-- **A promise problem in a class of languages** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.2, p.10): "For a promise problem
`Π = (YES, NO)` and a complexity class `C`, we say that `Π ∈ C` if there is a language `L ∈ C` such
that `YES ⊆ L` and `NO ⊆ {0,1}^* \ L`" (p.12 states `Π ∉ C` as its negation). -/
def PromiseIn (P : Set (List Bool) × Set (List Bool)) (C : Set (Set (List Bool))) : Prop :=
  ∃ L ∈ C, P.1 ⊆ L ∧ Disjoint P.2 L

end NKtLB.Supplement


