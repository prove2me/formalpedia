-- Prove2me | Definitions.Def_FedergruenTzur_MinPred_Breakpoint
-- name    : FedergruenTzur_MinPred_Breakpoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:36:16.883653+00:00
-- url     : https://prove2.me/theorems/153ce53c-23b2-4965-b52b-b72250bde2d7
-- title:
--   The intercept A(k, l) of (4) and the root G(k, l) of (5), extended symmetrically
-- statement:
--   In the dynamic lot size model with costs $F$ given by the recursion (2), Federgruen and Tzur compare two candidate last setup periods $k < l$ through the difference $\Delta_{k,l}(t) = F(k,t) - F(l,t)$, which is an affine function of the cumulative demand $D(t)$ with intercept
--   $$
--   A(k, l) = F(k-1) + K_k - F(l-1) - K_l + S(k, l-1) + c_k\,[D(l-1) - D(k-1)] + D(l-1)\,(c_l - c_{k,l})
--   $$
--   (the first line of (4)) and slope $c_{k,l} - c_l = \tilde C(k) - \tilde C(l)$. Its root is
--   $$
--   G(k, l) = \begin{cases} A(k,l)/(\tilde C(l) - \tilde C(k)) & \text{if } \tilde C(l) \ne \tilde C(k),\\ +\infty & \text{if } \tilde C(l) = \tilde C(k) \text{ and } A(k,l) \le 0,\\ -\infty & \text{if } \tilde C(l) = \tilde C(k) \text{ and } A(k,l) > 0, \end{cases} \qquad k < l, \tag{5}
--   $$
--   and it is extended to all pairs symmetrically: $G(l, k) = G(k, l)$ for $k < l$.
--
--   The values $G(k,l)$ are the breakpoints at which one period overtakes another as the better last setup period; they define the critical values $g(\cdot)$ of the paper's main theorem.
--
--   **Formalization Note.** $G$ takes values in the extended reals `EReal`, with $+\infty = \top$ and $-\infty = \bot$ distinct from every real number. The diagonal value $G(k,k)$, never used by the paper, is the formula (5) applied to the pair $(k,k)$.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, pp. 913–914, eq. (4) (first line), eq. (5), and the symmetric extension of G after LEMMA 2

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Model

/-!
# Federgruen–Tzur (1991), §1: the intercept `A(k, l)` of (4) and the root `G(k, l)` of (5)

A. Federgruen and M. Tzur, Management Science 37(8), 1991, pp. 913–914, eqs. (4), (5) and the
symmetric extension of `G` stated after Lemma 2.

* `A k l` is the first line of (4):
  `A(k, l) = F(k-1) + K_k - F(l-1) - K_l + S(k, l-1) + c_k [D(l-1) - D(k-1)] + D(l-1)(c_l - c_{k,l})`.
* `Gord k l` is (5) for an ordered pair `k < l`:
  `A(k, l) / (C̃(l) - C̃(k))` if `C̃(l) ≠ C̃(k)`, `+∞` if `C̃(l) = C̃(k)` and `A(k, l) ≤ 0`, and `−∞` if
  `C̃(l) = C̃(k)` and `A(k, l) > 0`.
* `G k l` is the symmetric extension `G(l, k) = G(k, l)` for `k < l`.

**Formalization Note.** Values live in `EReal`, so `+∞ = ⊤` and `−∞ = ⊥` are kept apart from every
real value. The diagonal value `G k k` (never used by the paper) is `Gord k k`.
-/

namespace FedergruenTzur.MinPred

namespace LotSizing

variable (P : LotSizing)

/-- `A(k, l)`, the first line of (4). -/
noncomputable def A (k l : ℕ) : ℝ :=
  P.Fopt (k - 1) + P.K k - P.Fopt (l - 1) - P.K l + P.S k (l - 1)
    + P.c k * (P.D (l - 1) - P.D (k - 1)) + P.D (l - 1) * (P.c l - P.cij k l)

/-- `G(k, l)` of (5) for an ordered pair `k < l`. -/
noncomputable def Gord (k l : ℕ) : EReal :=
  if P.Ctil l ≠ P.Ctil k then ((P.A k l / (P.Ctil l - P.Ctil k) : ℝ) : EReal)
  else if P.A k l ≤ 0 then ⊤ else ⊥

/-- `G(k, l)` extended symmetrically: `G(k, l)` of (5) when `k ≤ l`, and `G(l, k)` when `l < k`. -/
noncomputable def G (k l : ℕ) : EReal :=
  if k ≤ l then P.Gord k l else P.Gord l k

end LotSizing

end FedergruenTzur.MinPred


