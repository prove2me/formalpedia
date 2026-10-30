-- Prove2me | Definitions.Def_XuMultistage_Structure_RevenueOrdered
-- name    : XuMultistage_Structure_RevenueOrdered
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:23:37.396916+00:00
-- url     : https://prove2.me/theorems/e9d1f720-d40b-4903-9a3d-fc9bd22f4bc3
-- title:
--   Definition 1 — revenue-ordered assortment
-- statement:
--   An assortment is revenue-ordered when it is a prefix of the fixed weakly decreasing price order:
--   $$S=\{1,\ldots,m\},\qquad 0\le m\le n.$$
--   Cutoff zero gives the empty assortment; the outside option is never an ordinary product in the prefix. Equal-price products retain their specified index order, so a prefix may end within a tie.
--
--   This predicate expresses the source's combinatorial structure without building it into the admissible policies.
--
--   **Formalization Note** The cutoff and indices use `Fin (n + 1)`, and membership means $0<i\le m$. It applies to either stage separately.
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), Definition 1, p. 13

import Mathlib

namespace XuMultistage.Structure

/-- Definition 1: ordinary products form a prefix of the fixed price order.
Index zero is excluded; cutoff zero represents the empty assortment. -/
def RevenueOrdered {n : ℕ} (S : Finset (Fin (n + 1))) : Prop :=
  ∃ m : Fin (n + 1), ∀ i : Fin (n + 1), i ∈ S ↔ 0 < i ∧ i ≤ m

end XuMultistage.Structure


