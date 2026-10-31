-- Prove2me | Definitions.Def_MWMSLagrange_Instance_Valid
-- name    : MWMSLagrange_Instance_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:34.767332+00:00
-- url     : https://prove2.me/theorems/656417e4-a55c-4b02-95f7-65e3cd7f5eb3
-- title:
--   Sign conditions: $C_j, h_i, b_i, c_{i,j}\ge 0$
-- statement:
--   An MWMS instance is **valid** when
--
--   1. every initial warehouse inventory is nonnegative, $C_j\ge 0$;
--   2. holding and lost-sales costs are nonnegative, $h_i\ge0$, $b_i\ge0$;
--   3. shipping costs on the network are nonnegative, $c_{i,j}\ge 0$ for $j\in\mathcal M_i$.
--
--   The end-of-horizon costs $w_j$ are unrestricted in sign. These are the standing assumptions of §2.
--
--   **Formalization Note** $C_j\ge0$ is implicit on the page. That every store has at least one warehouse is not a separate condition: the theorems assume an allocation with $\sum_{j\in\mathcal M_i}\rho_{i,j}=1$, which implies it.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.6–7 (cost list: h_i ≥ 0, b_i ≥ 0, c_{i,j} ≥ 0, w_j ∈ R)

import Mathlib
import Definitions.Def_MWMSLagrange_Instance

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.6–7: the sign
conditions on an MWMS instance: initial inventories `C_j ≥ 0`, holding costs `h_i ≥ 0`,
lost-sales costs `b_i ≥ 0`, and shipping costs `c_{i,j} ≥ 0` for `j ∈ 𝓜_i`. The end-of-horizon
costs `w_j ∈ ℝ` are unrestricted ("w > 0 if it is a cost, and w < 0 if it has a salvage
value", p.7).

**Formalization Note.** `C_j ≥ 0` is implicit on the page (an inventory). The page's
"every store can be replenished from some warehouse" is not a field: every theorem of the
mission that needs it assumes an allocation with `∑_{j ∈ 𝓜_i} ρ_{i,j} = 1`, which implies
`𝓜_i ≠ ∅`. -/
def Instance.Valid {M N : ℕ} (I : Instance M N) : Prop :=
  (∀ j, 0 ≤ I.C j) ∧ (∀ i, 0 ≤ I.h i) ∧ (∀ i, 0 ≤ I.b i) ∧
    (∀ i j, I.adj i j = true → 0 ≤ I.c i j)

end MWMSLagrange


