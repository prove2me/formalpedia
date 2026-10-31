-- Prove2me | Definitions.Def_RepairSched_IsRegulated
-- name    : RepairSched_IsRegulated
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:51.770561+00:00
-- url     : https://prove2.me/theorems/3913a18c-57a7-4f03-bc41-2e55039dec38
-- title:
--   Conditions C1–C3 of the two-sided regulator mappings
-- statement:
--   For a drift $\beta$, a barrier $b$ and an input $x$, the triple $(w,\ell,u)\in\mathbb D^3$ satisfies C1–C3 if
--
--   1. $w(t)=x(t)-\int_0^t\beta(w(y))\,dy+\ell(t)-u(t)\in[0,b]$ for all $t\ge0$;
--   2. $\ell(0)=u(0)=0$ and $\ell,u$ are nondecreasing;
--   3. $\int_0^\infty w\,d\ell=\int_0^\infty(b-w)\,du=0$.
--
--   Definition 5 is the case $\beta(w)=\sum_i(\lambda_i/\mu_i)(q_i^*(w)-s_i)^+$, and Definition A.4.2 the case $\beta(w)=\lambda(w-s)^+$.
--
--   **Formalization Note** The drift path is integrable on every $[0,t]$. C3 uses the Lebesgue–Stieltjes measures of $\ell$ and $u$, extended by $0$ to negative times so that there is no atom at $0$: $d\ell$ gives no mass to $\{w>0\}$ and $du$ no mass to $\{w<b\}$, jumps included.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Definition 5, p.25; Definition A.4.2, OA p.23

import Mathlib
import Definitions.Def_RepairSched_IsCadlag

open MeasureTheory Set

namespace RepairSched

/-- **Conditions C1–C3 of the two-sided regulator mappings** with state-dependent drift `β`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Definition 5, p.25 (with `β` the drift `Σᵢ (λᵢ/μᵢ)(q*ᵢ − sᵢ)⁺`) and Definition A.4.2,
OA p.23 (with `β(w) = λ(w − s)⁺`):
C1. `w(t) = x(t) − ∫₀ᵗ β(w(y)) dy + ℓ(t) − u(t) ∈ [0,b]` for all `t ≥ 0`,
C2. `ℓ(0) = u(0) = 0` and both `ℓ` and `u` are nondecreasing,
C3. `∫₀^∞ w(t) dℓ(t) = ∫₀^∞ (b − w(t)) du(t) = 0`.
Moreover `(w, ℓ, u) ∈ D³`.

**Formalization Note.** Times `t < 0` play no role. The drift path is integrable on every `[0,t]`,
so the integral in C1 is a genuine one. C3 uses the Lebesgue–Stieltjes measures of `ℓ` and `u`,
extended by `0` to negative times so that there is no atom at `0`. Since `w ∈ [0,b]`, it says
that `dℓ` gives no mass to `{w > 0}` and `du` no mass to `{w < b}`, jumps included. -/
def IsRegulated (β : ℝ → ℝ) (b : ℝ) (x w l u : ℝ → ℝ) : Prop :=
  IsCadlag w ∧ IsCadlag l ∧ IsCadlag u ∧
    (∀ t, 0 ≤ t → IntervalIntegrable (fun y => β (w y)) volume 0 t) ∧
    (∀ t, 0 ≤ t → w t = x t - (∫ y in (0 : ℝ)..t, β (w y)) + l t - u t ∧ w t ∈ Icc 0 b) ∧
    l 0 = 0 ∧ u 0 = 0 ∧ MonotoneOn l (Ici 0) ∧ MonotoneOn u (Ici 0) ∧
    (∃ F : StieltjesFunction ℝ, (∀ t, F t = l (max t 0)) ∧ F.measure ({t | 0 < w t} ∩ Ici 0) = 0) ∧
    (∃ F : StieltjesFunction ℝ, (∀ t, F t = u (max t 0)) ∧ F.measure ({t | w t < b} ∩ Ici 0) = 0)

end RepairSched


