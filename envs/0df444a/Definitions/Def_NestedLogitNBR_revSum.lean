-- Prove2me | Definitions.Def_NestedLogitNBR_revSum
-- name    : NestedLogitNBR_revSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:36:37.037799+00:00
-- url     : https://prove2.me/theorems/e3f7dea2-62d1-435a-b7c6-725f08fab863
-- title:
--   Revenue sum $R_{ik'}=\sum_{j=1}^{k'}r_{ij}v_{ij}$ of the first $k'$ products
-- statement:
--   In the proof of Theorem 7 the paper abbreviates, for nest $i$ and $k'=1,\dots,n$,
--
--   $$
--   R_{ik'}=\sum_{j=1}^{k'}r_{ij}v_{ij},\qquad q_{ik'}=\sum_{j=1}^{k'}v_{ij}=V_i(N_{ik'}).
--   $$
--
--   $R_{ik'}$ is a sum, not the average $R_i(N_{ik'})=R_{ik'}/q_{ik'}$. It appears in the intermediate inequalities (20)-(24) of the proof, where the threshold vector of Lemma 6 has value $(R_{i,k-1}+r_{ik}v_{ik}\rho)/(q_{i,k-1}+v_{ik}\rho)$ inside the bracket.
--
--   **Formalization Note** $R_{i0}=0$ (empty sum).
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7), p. 41 (R_ik′ and q_ik′)

import Mathlib
import Definitions.Def_NestedLogitNBR_nbr

namespace NestedLogitNBR

/-- **Revenue sum `R_ik' = Σ_{j=1}^{k'} r_ij v_ij` of the first `k'` products.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), App. A.1 (proof of Theorem 7), p. 41: "For notational convenience, let
`R_ik′ = Σ_{j=1}^{k′} r_ij v_ij` and `q_ik′ = Σ_{j=1}^{k′} v_ij` for all `k′ = 1, …, n`."

`revSum r v i k' = Σ_{j ∈ N_ik'} r_ij v_ij`. This is a **sum**, not the average
`R_i(N_ik') = R_ik' / q_ik'` (`nestRevenue`). The companion `q_ik'` is
`prefWeight v i (nbr k')`.

**Formalization Note.** `revSum r v i 0 = 0` (the empty sum), consistent with `N_i0 = ∅`. -/
def revSum {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m) (k' : ℕ) : ℝ :=
  ∑ l ∈ (nbr k' : Finset (Fin n)), r i l * v i l

end NestedLogitNBR


