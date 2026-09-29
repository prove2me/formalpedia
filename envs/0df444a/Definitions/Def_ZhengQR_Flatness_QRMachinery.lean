-- Prove2me | Definitions.Def_ZhengQR_Flatness_QRMachinery
-- name    : ZhengQR_Flatness_QRMachinery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T02:03:14.139814+00:00
-- url     : https://prove2.me/theorems/1e525c08-909d-45b9-9263-2a620f4edcfd
-- title:
--   The (Q, r) machinery for a cost rate G: c(Q, r), r(Q), y⁰, H(Q), H₀(Q), C(Q), A(Q)
-- statement:
--   Fix an inventory cost rate $G:\mathbb{R}\to\mathbb{R}$, a demand rate $\lambda$ and a fixed ordering cost $K$. The following objects are defined for any such $G$ and are later instantiated at the stochastic cost rate $G$ and at the EOQ cost rate $G_d$.
--
--   1. The long-run average cost of the $(Q, r)$ policy (Eq. (1)):
--   $$c(Q, r) = \frac{\lambda K + \int_r^{r+Q} G(y)\,dy}{Q}.$$
--   2. A reorder point $r$ is **optimal for $Q$** if it minimizes $c(Q,\cdot)$ over $\mathbb{R}$; $r(Q)$ denotes a chosen optimal reorder point.
--   3. $y^0$ denotes a chosen global minimizer of $G$.
--   4. $H(Q) = G(r(Q))$ for $Q>0$ and $H(0) = G(y^0)$ (Eq. (6)); $H_0(Q) = H(Q) - G(y^0)$.
--   5. $C(Q) = c(Q, r(Q))$, the average cost of the order quantity $Q$ when the reorder point is chosen optimally for it.
--   6. $A(Q) = Q\,H(Q) - \int_0^Q H(y)\,dy$ (Eq. (9)).
--
--   These are the objects in terms of which the paper states all its optimality conditions and comparison results.
--
--   **Formalization Note** $r(Q)$ is defined as a chosen minimizer of $c(Q,\cdot)$, not through the equation $G(r) = G(r+Q)$ (that equation is Lemma 2 of the paper). If no minimizer exists, $r(Q)$ is the junk value $0$; similarly $y^0$ is $0$ if $G$ has no minimizer. For $Q<0$, $H(Q)$ is the junk value $G(y^0)$, and $c$, $C$ are meaningful for $Q>0$ only; every statement restricts to $Q>0$ or $Q\ge 0$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 88 Eq. (1); p. 90 (r(Q), y⁰); p. 91 Eq. (6) and C(Q); p. 92 Eq. (9), H₀

import Mathlib

namespace ZhengQR.Flatness

/-- Zheng (1992), p. 88, Eq. (1): the long-run average cost of the `(Q, r)` policy,
`c(Q, r) = (λK + ∫_r^{r+Q} G(y) dy) / Q`, for an inventory cost rate `G`, demand rate `lam`
and fixed ordering cost `K`. Meaningful for `Q > 0` only. -/
noncomputable def qrCost (G : ℝ → ℝ) (lam K Q r : ℝ) : ℝ :=
  (lam * K + ∫ y in r..r + Q, G y) / Q

/-- `r` is an optimal reorder point for the fixed order quantity `Q`: it minimizes
`c(Q, ·)` over all of `ℝ` (Zheng 1992, p. 90). -/
def IsOptReorder (G : ℝ → ℝ) (lam K Q r : ℝ) : Prop :=
  ∀ r' : ℝ, qrCost G lam K Q r ≤ qrCost G lam K Q r'

open Classical in
/-- Zheng (1992), p. 90: `r(Q)`, an optimal reorder point for `Q` fixed, chosen among the
minimizers of `c(Q, ·)` (junk value `0` if there is none). -/
noncomputable def optReorder (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if hex : ∃ r, IsOptReorder G lam K Q r then hex.choose else 0

open Classical in
/-- `y⁰`: a global minimizer of `G` (Zheng 1992, p. 90), chosen; junk value `0` if `G`
has no global minimizer. -/
noncomputable def minPoint (G : ℝ → ℝ) : ℝ :=
  if hex : ∃ y, ∀ z, G y ≤ G z then hex.choose else 0

/-- Zheng (1992), p. 91, Eq. (6): `H(Q) = G(r(Q))` for `Q > 0`, and `H(0) = G(y⁰)`.
(For `Q < 0` the value `G(y⁰)` is a junk value; the paper uses `H` on `[0, ∞)` only.) -/
noncomputable def Hfun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  if 0 < Q then G (optReorder G lam K Q) else G (minPoint G)

/-- Zheng (1992), p. 92: `H₀(Q) = H(Q) - G(y⁰)`. -/
noncomputable def Hzero (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Hfun G lam K Q - G (minPoint G)

/-- Zheng (1992), p. 91: `C(Q) = c(Q, r(Q))`, the average cost of order quantity `Q` when the
reorder point is chosen optimally for `Q`. Meaningful for `Q > 0` only. -/
noncomputable def optCost (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  qrCost G lam K Q (optReorder G lam K Q)

/-- Zheng (1992), p. 92, Eq. (9): `A(Q) = Q H(Q) - ∫_0^Q H(y) dy`. -/
noncomputable def Afun (G : ℝ → ℝ) (lam K Q : ℝ) : ℝ :=
  Q * Hfun G lam K Q - ∫ y in (0 : ℝ)..Q, Hfun G lam K y

end ZhengQR.Flatness


