-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_PromiseNPHard
-- name    : MeanBudgetXC_Supplement_PromiseNPHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:12:31.155209+00:00
-- url     : https://prove2.me/theorems/08dc713e-fc0a-4bce-afe1-07eb1c64b1fc
-- title:
--   NP-hardness of a promise problem under polynomial-time reductions
-- statement:
--   A promise problem with YES and NO instances (sets of binary strings) is **NP-hard under deterministic polynomial-time reductions** if for every finite nonempty alphabet $\Sigma$ and every language $L\in\mathrm{NP}$ over $\Sigma$ there is a polynomial-time computable map $f$ with
--   $$x\in L\ \Rightarrow\ f(x)\in\mathrm{YES},\qquad x\notin L\ \Rightarrow\ f(x)\in\mathrm{NO}.$$
--   NP, polynomial-time computability and the machine model are the platform's `CookPvsNP` definitions (one-tape Turing machines, following Cook's Clay problem description).
--
--   **Formalization Note** `CookPvsNP.PolyReducible` is a reduction between languages; distinguishing two value ranges is a promise problem, so the map is only required to land in YES or NO according to membership.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 7.2, p.36

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace MeanBudgetXC.Supplement

/-- **NP-hardness of a promise problem under deterministic polynomial-time reductions** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 7.2, p.36: "it is NP-hard under deterministic polynomial-time
reductions to distinguish …"): for every finite nonempty alphabet `Sym` and every language
`L ∈ NP` over `Sym`, a polynomial-time computable map `f` sends every member of `L` into `YES` and
every non-member into `NO`. NP, polynomial-time computability and the machine model are the
platform's `CookPvsNP` definitions (one-tape Cook machines).

**Formalization Note** `CookPvsNP.PolyReducible` reduces between languages; distinguishing two
value ranges is a promise problem, so the reduction is required only to land in `YES` or `NO`
according to membership. -/
def PromiseNPHard (YES NO : Set (List Bool)) : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym), L ∈ CookPvsNP.NP Sym →
    ∃ f : List Sym → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ x, (x ∈ L → f x ∈ YES) ∧ (x ∉ L → f x ∈ NO)

end MeanBudgetXC.Supplement


