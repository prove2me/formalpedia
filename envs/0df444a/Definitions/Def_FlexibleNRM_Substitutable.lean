-- Prove2me | Definitions.Def_FlexibleNRM_Substitutable
-- name    : FlexibleNRM_Substitutable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:33.877194+00:00
-- url     : https://prove2.me/theorems/080cca06-2eaa-4ff7-a70b-bdd74cbee447
-- title:
--   The substitutability property of the choice probabilities
-- statement:
--   The choice probabilities satisfy the **substitutability property** if for every period $t$, all assortments $S\subseteq Q\subseteq\mathcal J$ and every $j\in S$,
--   $$\phi_{jt}(S)\ge\phi_{jt}(Q).$$
--   Offering a smaller assortment raises the choice probability of each product in it. All choice models based on random utility maximization have this property, and it is the only structural assumption the performance guarantee makes on the choice model.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, §2, p.7

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- The **substitutability property** `φ_jt(S) ≥ φ_jt(Q)` for all `S ⊆ Q ⊆ J`, `j ∈ S`, `t ∈ T`.

Zhu, Topaloglu, manuscript of November 16, 2022, §2, p.7.

**Formalization Note** This is the paper's form. The published
`PersonalizedAssortment.IB.Substitutable` is an insert form over a family of assortments and is not
used. -/
def Substitutable {n m r : ℕ} (N : Network n m r) : Prop :=
  ∀ t ∈ Finset.Icc 1 N.T, ∀ S Q : Finset (Fin n), S ⊆ Q → ∀ j ∈ S,
    (N.φ t).prob Q j ≤ (N.φ t).prob S j

end FlexibleNRM


