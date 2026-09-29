-- Prove2me | Definitions.Def_MonotoneDP_Decrease_Assumptions
-- name    : MonotoneDP_Decrease_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:02:35.983983+00:00
-- url     : https://prove2.me/theorems/946b39f7-112a-4e80-8873-3b5ffbfac9dc
-- title:
--   Assumptions D (uniform decrease), D.1 (continuity from above) and D.2 (uniform shift bound)
-- statement:
--   In the abstract dynamic programming model (state space $S$, constraint sets $U(x)$, monotone mapping $H$, terminal function $\bar J$, unit function $e(x)=1$), Bertsekas (1977) introduces the following assumptions.
--
--   1. **Assumption D (uniform decrease).** For all $x\in S$ and $u\in U(x)$,
--   $$\bar J(x)\ \ge\ H(x,u,\bar J).\tag{23}$$
--   2. **Assumption D.1.** If $\{J_k\}\subset F$ is a sequence satisfying $J_{k+1}\le J_k\le\bar J$ for all $k$, then
--   $$\lim_{k\to\infty}H(x,u,J_k)=H\Bigl(x,u,\lim_{k\to\infty}J_k\Bigr)\qquad\forall x\in S,\ u\in U(x).\tag{34}$$
--   3. **Assumption D.2** (with scalar $\alpha$). $\alpha>0$, and for all scalars $r>0$ and all $J\in F$ with $J\le\bar J$,
--   $$H(x,u,J)-\alpha r\ \le\ H(x,u,J-re)\ \le\ H(x,u,J)\qquad\forall x\in S,\ u\in U(x).\tag{35}$$
--   "D.2 holds" means that such an $\alpha$ exists.
--
--   Assumption D covers, for instance, deterministic and stochastic optimal control problems with nonpositive costs per stage (Blackwell's positive dynamic programming model). D.1 is a continuity-from-above property of $H$ along nonincreasing sequences, and D.2 bounds how much $H$ can drop when its argument is lowered uniformly.
--
--   **Formalization Note** In D.1 both limits are `limUnder atTop`; both sequences are nonincreasing (the left one by monotonicity of $H$), so the limits exist in $[-\infty,\infty]$. In D.2, only real scalars are subtracted from extended reals, so no undefined expression $\infty-\infty$ arises.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 442 (PDF p. 5), Assumption D, eq. (23); p. 447 (PDF p. 10), Assumptions D.1, D.2, eqs. (34), (35). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model

namespace MonotoneDP.Decrease

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- Assumption D (uniform decrease), eq. (23): `J̄(x) ≥ H(x, u, J̄)` for all `x ∈ S`, `u ∈ U(x)`. -/
def AssumptionD : Prop := ∀ x, ∀ u ∈ m.U x, m.H x u m.Jbar ≤ m.Jbar x

/-- Assumption D.1, eq. (34): if `{J_k} ⊂ F` satisfies `J_{k+1} ≤ J_k ≤ J̄` for all `k`, then
`lim_k H(x, u, J_k) = H(x, u, lim_k J_k)` for all `x ∈ S`, `u ∈ U(x)`, where `lim_k J_k` is the
pointwise limit (it exists because the sequence is nonincreasing, and so does the left-hand
limit, by monotonicity of `H`). -/
def AssumptionD1 : Prop :=
  ∀ Js : ℕ → S → EReal, (∀ k, Js k ≤ m.Jbar) → (∀ k, Js (k + 1) ≤ Js k) →
    ∀ x, ∀ u ∈ m.U x,
      limUnder atTop (fun k => m.H x u (Js k)) =
        m.H x u (fun y => limUnder atTop (fun k => Js k y))

/-- Assumption D.2 with the scalar `α`, eq. (35): `α > 0` and for all scalars `r > 0` and all
`J ∈ F` with `J ≤ J̄`,
`H(x, u, J) − α r ≤ H(x, u, J − r e) ≤ H(x, u, J)` for all `x ∈ S`, `u ∈ U(x)`, where `e` is the unit
function. "D.2 holds" is `∃ α, m.AssumptionD2 α`. -/
def AssumptionD2 (α : ℝ) : Prop :=
  0 < α ∧ ∀ r : ℝ, 0 < r → ∀ J : S → EReal, J ≤ m.Jbar → ∀ x, ∀ u ∈ m.U x,
    m.H x u J - ((α * r : ℝ) : EReal) ≤ m.H x u (fun y => J y - (r : EReal)) ∧
      m.H x u (fun y => J y - (r : EReal)) ≤ m.H x u J

end Model

end MonotoneDP.Decrease


