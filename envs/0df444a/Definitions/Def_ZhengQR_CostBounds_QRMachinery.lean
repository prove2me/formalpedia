-- Prove2me | Definitions.Def_ZhengQR_CostBounds_QRMachinery
-- name    : ZhengQR_CostBounds_QRMachinery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:54:53.532215+00:00
-- url     : https://prove2.me/theorems/1ff3c9fd-8668-415e-8649-084c677132a8
-- title:
--   The (Q, r) machinery for a generic cost rate G: c(Q, r), r(Q), y⁰, H, C, A, H₀, C₀ and optimal Q
-- statement:
--   Let $G:\mathbb R\to\mathbb R$ be an inventory-cost rate (the expected holding-plus-backorder cost rate at inventory position $y$), $\lambda$ the demand rate and $K$ the fixed ordering cost. This file builds, for an arbitrary $G$, every object of §2 of Zheng (1992).
--
--   1. **Average cost of a $(Q,r)$ policy** (Eq. (1), p. 88): for order quantity $Q>0$ and reorder point $r$,
--   $$c(Q,r)=\frac{\lambda K+\int_r^{r+Q}G(y)\,dy}{Q}.$$
--   2. **Optimal reorder point** (p. 90): $r$ is optimal for $Q$ if it minimizes $c(Q,\cdot)$ over all of $\mathbb R$; $r(Q)$ denotes a chosen such minimizer.
--   3. **Ideal point** (p. 90): $y^0$ is a chosen global minimizer of $G$.
--   4. **The function $H$** (Eq. (6), p. 91): $H(Q)=G(r(Q))$ for $Q>0$ and $H(0)=G(y^0)$.
--   5. **Optimal-reorder cost** (p. 91): $C(Q)=c(Q,r(Q))$.
--   6. **The area function** (Eq. (9), p. 92): $A(Q)=QH(Q)-\int_0^Q H(y)\,dy$.
--   7. **Controllable parts** (p. 92, Eq. (14)): $H_0(Q)=H(Q)-G(y^0)$ and
--   $$C_0(Q)=\frac{\lambda K+\int_0^Q H_0(y)\,dy}{Q}.$$
--   8. **Optimal order quantity** (p. 92): $Q^*$ is optimal if $Q^*>0$ and $C(Q^*)\le C(Q)$ for every $Q>0$.
--
--   Building the machinery for a generic $G$ lets the same definitions serve both the stochastic model (at the newsvendor cost of the leadtime demand) and the deterministic EOQ model (at $G_d$), exactly as the paper does when it "rederives the optimal control parameters for the EOQ model by using the optimality conditions established in the previous section" (p. 94).
--
--   **Formalization Note** $r(Q)$ and $y^0$ are chosen with `Exists.choose` behind an `if`; when no minimizer exists they take the junk value $0$, which never occurs under the model's standing assumptions (convex coercive $G$ with a unique minimizer). $r(Q)$ is defined as a minimizer of $c(Q,\cdot)$, never by the equation $G(r)=G(r+Q)$ (that is Lemma 2). For $Q<0$, $H(Q)$ takes the junk value $G(y^0)$; the paper uses $H$ on $[0,\infty)$ only. $c$, $C$, $C_0$ are meaningful only for $Q>0$ and every statement about them carries that hypothesis.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 Eq. (1); p. 90 (r(Q), y⁰); p. 91 Eq. (6) and C(Q); p. 92 Eqs. (9), (13)–(14) and Q*

import Mathlib

namespace ZhengQR.CostBounds

open MeasureTheory Classical

/-- Eq. (1), p. 88: the average cost of the `(Q, r)` policy for a generic inventory-cost rate `G`,
`c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- p. 90: `r` is an optimal reorder point for the fixed order quantity `Q`, i.e. `r` minimizes
`c(Q, ·)` over all of `ℝ`. -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

/-- p. 90: `r(Q)`, a chosen optimal reorder point for `Q` (junk value `0` if none exists). -/
noncomputable def reorderPt (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if hr : ∃ r, IsOptReorder G lam K Q r then hr.choose else 0

/-- p. 90: `y⁰`, a chosen global minimizer of `G` (the unique one under the paper's standing
assumption; junk value `0` if `G` has no minimizer). -/
noncomputable def idealPt (G : ℝ → ℝ) : ℝ :=
  if hy : ∃ y, ∀ z, G y ≤ G z then hy.choose else 0

/-- Eq. (6) and the line under it, p. 91: `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)`.
(For `Q < 0` the value `G(y⁰)` is a junk value; the paper uses `H` on `[0, ∞)` only.) -/
noncomputable def Hfun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then G (reorderPt G lam K Q) else G (idealPt G)

/-- p. 91: `C(Q) = c(Q, r(Q))`, the average cost when the reorder point is optimal for `Q`. -/
noncomputable def Cfun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (reorderPt G lam K Q)

/-- Eq. (9), p. 92: `A(Q) = Q H(Q) − ∫_0^Q H(y) dy`. -/
noncomputable def Afun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Q * Hfun G lam K Q - ∫ y in (0 : ℝ)..Q, Hfun G lam K y

/-- p. 92: `H₀(Q) = H(Q) − G(y⁰)`. -/
noncomputable def H0fun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Hfun G lam K Q - G (idealPt G)

/-- Eq. (14), p. 92: the average controllable cost `C₀(Q) = (λK + ∫_0^Q H₀(y) dy) / Q`. -/
noncomputable def C0fun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  (lam * K + ∫ y in (0 : ℝ)..Q, H0fun G lam K y) / Q

/-- p. 92: `Q` is an optimal order quantity: `Q > 0` and `C(Q) ≤ C(Q')` for every `Q' > 0`. -/
def IsOptQty (G : ℝ → ℝ) (lam K Q : ℝ) : Prop :=
  0 < Q ∧ ∀ Q' : ℝ, 0 < Q' → Cfun G lam K Q ≤ Cfun G lam K Q'

end ZhengQR.CostBounds


