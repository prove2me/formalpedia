-- Prove2me | Definitions.Def_MonotoneDP_Increase_Assumptions
-- name    : MonotoneDP_Increase_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:55:39.027074+00:00
-- url     : https://prove2.me/theorems/7379fa13-99e7-48ba-9969-f4ddfbe6fe65
-- title:
--   Assumptions I (uniform increase), I.1 (monotone continuity of H) and I.2 (Lipschitz-type bound with scalar α)
-- statement:
--   Three conditions on the abstract model $(S,C,U,H,\bar J)$ of Bertsekas (1977), used together in Section 5.
--
--   **Assumption I (uniform increase).**
--
--   $$\bar J(x)\le H(x,u,\bar J)\qquad\forall x\in S,\ u\in U(x).$$
--
--   **Assumption I.1.** If $\{J_k\}\subset F$ is a sequence with $\bar J\le J_k\le J_{k+1}$ for all $k$, then
--
--   $$\lim_{k\to\infty}H(x,u,J_k)=H\Bigl(x,u,\lim_{k\to\infty}J_k\Bigr)\qquad\forall x\in S,\ u\in U(x),$$
--
--   where $\lim_k J_k$ is the pointwise limit.
--
--   **Assumption I.2 (with scalar $\alpha$).** $\alpha>0$, and for all scalars $r>0$ and all $J\in F$ with $\bar J\le J$,
--
--   $$H(x,u,J)\le H(x,u,J+re)\le H(x,u,J)+\alpha r\qquad\forall x\in S,\ u\in U(x),$$
--
--   where $e$ is the unit function, $e(x)=1$. "I.2 holds" means that such an $\alpha$ exists.
--
--   Assumption I makes the value iterates $T^k(\bar J)$ and the partial compositions defining $J_\pi$ nondecreasing; I.1 lets limits pass through $H$; I.2 controls how $H$ reacts to a uniform upward shift of its function argument. Deterministic and stochastic optimal control problems with nonnegative costs satisfy all three.
--
--   **Formalization Note** I.2 is parameterized by $\alpha$ so that statements can refer to the scalar (Proposition 4 uses "if the scalar $\alpha$ in I.2 satisfies $\alpha<1$"). In I.1 the two limits are `limUnder atTop`; both sequences are nondecreasing (the second by monotonicity of $H$), so they are genuine limits in $[-\infty,\infty]$. Adding a real $r$ to an extended real leaves $\pm\infty$ unchanged.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 442 (PDF p. 5), Assumption I, eq. (22); p. 447 (PDF p. 10), Assumptions I.1 and I.2, eqs. (32)–(33). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model

namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- Assumption I (uniform increase), eq. (22): `J̄(x) ≤ H(x, u, J̄)` for all `x ∈ S`, `u ∈ U(x)`. -/
def AssumptionI : Prop := ∀ x, ∀ u ∈ m.U x, m.Jbar x ≤ m.H x u m.Jbar

/-- Assumption I.1, eq. (32): if `{J_k} ⊂ F` satisfies `J̄ ≤ J_k ≤ J_{k+1}` for all `k`, then
`lim_k H(x, u, J_k) = H(x, u, lim_k J_k)` for all `x ∈ S`, `u ∈ U(x)`, where `lim_k J_k` is the
pointwise limit (it exists because the sequence is nondecreasing). -/
def AssumptionI1 : Prop :=
  ∀ Js : ℕ → S → EReal, (∀ k, m.Jbar ≤ Js k) → (∀ k, Js k ≤ Js (k + 1)) →
    ∀ x, ∀ u ∈ m.U x,
      limUnder atTop (fun k => m.H x u (Js k)) =
        m.H x u (fun y => limUnder atTop (fun k => Js k y))

/-- Assumption I.2 with the scalar `α`, eq. (33): `α > 0` and for all scalars `r > 0` and all
`J ∈ F` with `J̄ ≤ J`,
`H(x, u, J) ≤ H(x, u, J + r e) ≤ H(x, u, J) + α r` for all `x ∈ S`, `u ∈ U(x)`, where `e` is the unit
function. "I.2 holds" is `∃ α, m.AssumptionI2 α`. -/
def AssumptionI2 (α : ℝ) : Prop :=
  0 < α ∧ ∀ r : ℝ, 0 < r → ∀ J : S → EReal, m.Jbar ≤ J → ∀ x, ∀ u ∈ m.U x,
    m.H x u J ≤ m.H x u (fun y => J y + (r : EReal)) ∧
      m.H x u (fun y => J y + (r : EReal)) ≤ m.H x u J + ((α * r : ℝ) : EReal)

end Model

end MonotoneDP.Increase


