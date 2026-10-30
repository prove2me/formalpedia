-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Feas10
-- name    : NestedLogitAssort_PartialCapture_Feas10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:38.515963+00:00
-- url     : https://prove2.me/theorems/bc1dc7ff-235e-4b3d-92ce-0eba21d4ef02
-- title:
--   Feasibility in problem (10)
-- statement:
--   Problem (10) is
--
--   $$
--   \min\ x\quad\text{s.t.}\quad v_0x\ge\sum_{i\in M}y_i,\qquad y_i\ge\max_{\epsilon_i\ge 0}\Bigl\{(v_{i0}+\epsilon_i)^{\gamma_i}\Bigl[\frac{K_i(\epsilon_i)}{v_{i0}+\epsilon_i}-x\Bigr]\Bigr\}\quad\forall\,i\in M.
--   $$
--
--   A pair $(x,y)$ is feasible for (10) when $v_0x\ge\sum_i y_i$ and, for every nest $i$, $y_i$ is at least the value of the objective of (10) at every $\epsilon\ge 0$.
--
--   **Formalization Note** "$y_i\ge\max$" is encoded as "$y_i$ bounds every value", which is the same whenever the maximum exists and avoids a junk supremum when the set is unbounded.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (10), p. 22

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_val10

namespace NestedLogitAssort.PartialCapture

/-- **Feasibility in problem (10).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (10), p. 22:
`min x` s.t. `v_0 x ≥ ∑_{i ∈ M} y_i`,
`y_i ≥ max_{ϵ_i ≥ 0} {(v_{i0} + ϵ_i)^{γ_i} [K_i(ϵ_i)/(v_{i0} + ϵ_i) − x]}` for all `i ∈ M`.

**Formalization Note.** "`y_i ≥ max_{ϵ_i ≥ 0}{…}`" is encoded as "`y_i` is at least every value
`val10 I i ϵ x` with `ϵ ≥ 0`", i.e. `y_i` is an upper bound of the set; no `sSup` is taken (for
`x < 0` the set can be unbounded above, where `sSup` would return a junk value). Whenever the
maximum exists the two readings agree. -/
def Feas10 {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n) (x : ℝ) (y : M → ℝ) : Prop :=
  ∑ i, y i ≤ I.v0 * x ∧ ∀ (i : M) (ε : ℝ), 0 ≤ ε → val10 I i ε x ≤ y i

end NestedLogitAssort.PartialCapture


