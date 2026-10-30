-- Prove2me | Definitions.Def_NestedLogitNBR_nestRevenue
-- name    : NestedLogitNBR_nestRevenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:35:21.811545+00:00
-- url     : https://prove2.me/theorems/94e1d6e6-4325-4adb-ab8a-5885d6f4a2a5
-- title:
--   Expected revenue $R_i(S)$ of a nest given that it is chosen
-- statement:
--   Let $r_{ij}$ and $v_{ij}\ge0$ be the revenue and preference weight of product $j$ in nest $i$, and $V_i(S)=\sum_{j\in S}v_{ij}$. The expected revenue obtained from nest $i$ when it is chosen and the assortment $S$ is offered there is
--
--   $$
--   R_i(S)=\frac{\sum_{j\in S}r_{ij}v_{ij}}{V_i(S)},
--   $$
--
--   with the interpretation $R_i(\emptyset)=0$ (p. 7). It is the $v$-weighted average of the revenues of the products in $S$. $R_i(S)$ appears in the constraints $y_i\ge V_i(S)^{\gamma_i}(R_i(S)-x)$ of the linear programs (3) and (4), and in the performance factor (6).
--
--   **Formalization Note** Lean's convention $x/0=0$ gives $R_i(\emptyset)=0$, the paper's interpretation, and $R_i(S)=0$ whenever every product of $S$ has weight $0$ (such products are never purchased, p. 7).
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), §1, p. 7 (definition of R_i(S_i), with R_i(∅) = 0)

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight

namespace NestedLogitNBR

/-- **Expected revenue `R_i(S)` from nest `i` given that the nest is chosen.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), §1, p. 7: "`R_i(S_i) = Σ_{j∈S_i} r_ij P_ij(S_i) = Σ_{j∈S_i} r_ij v_ij / V_i(S_i)`, with the
interpretation that `R_i(∅) = 0`."

`nestRevenue r v i S = (Σ_{j∈S} r_ij v_ij) / V_i(S)`, a weighted average of the revenues of the
products in `S` (weights `v_ij`), with `V_i` as in `prefWeight` (`v_i0 = 0`, Section 4, p. 16).

**Formalization Note.** Lean's `x / 0 = 0` gives `R_i(∅) = 0`, the paper's own interpretation,
and more generally `R_i(S) = 0` whenever every product of `S` has weight `0` (such products are
never purchased, p. 7). -/
noncomputable def nestRevenue {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m)
    (S : Finset (Fin n)) : ℝ :=
  (∑ j ∈ S, r i j * v i j) / prefWeight v i S

end NestedLogitNBR


