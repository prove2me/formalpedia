-- Prove2me | Definitions.Def_SponsoredAssort_singletons
-- name    : SponsoredAssort_singletons
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:38.949614+00:00
-- url     : https://prove2.me/theorems/e91082aa-3298-4876-b61e-b37a05fe959f
-- title:
--   Partition into singletons $\{\{1\},\dots,\{n\}\}$
-- statement:
--   The partition $P=\{\{1\},\dots,\{n\}\}$ consisting of all singletons. Its partition mechanism is denoted $m^{\downarrow}$: it displays the single seller of highest welfare $R(\{i\},v)=r_iv_i/(1+v_i)$.
--
--   **Formalization Note** Defined as the nested partition $P_1$, whose block $\{1\}$ is itself a singleton.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §5.3, p.28

import Mathlib
import Definitions.Def_SponsoredAssort_nested

namespace SponsoredAssort

/-- The **partition into singletons** `P = {{1}, …, {n}}` (Balseiro, Désir, SSRN 3821382
(Feb. 21, 2022), §5.3, p.28), whose partition mechanism is `m↓`.

**Formalization Note.** Defined as the nested partition `P₁`: its block `{1}` is a singleton,
so every part is a singleton. -/
noncomputable def singletons (n : ℕ) : Finpartition (Finset.univ : Finset (Fin n)) :=
  nested n 1

end SponsoredAssort


