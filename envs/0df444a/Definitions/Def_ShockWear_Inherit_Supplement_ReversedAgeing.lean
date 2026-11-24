-- Prove2me | Definitions.Def_ShockWear_Inherit_Supplement_ReversedAgeing
-- name    : ShockWear_Inherit_Supplement_ReversedAgeing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:48:40.206849+00:00
-- url     : https://prove2.me/theorems/7cfac111-401e-4377-b7c7-208004b9f81c
-- title:
--   Reversed ageing classes IMRL, DHRA, NWU and NWUE
-- statement:
--   For a life survival function $\bar F$, write $R(t)=\int_0^\infty\bar F(x+t)\,dx\in[0,\infty]$. The four predicates reverse the directions of the corresponding classes on pp. 631–632:
--
--   $$
--   \mathrm{IMRL}:R(t)/\bar F(t)\text{ increases};\quad
--   \mathrm{DHRA}:\bar F(t)^{1/t}\text{ increases};\quad
--   \mathrm{NWU}:\bar F(x)\bar F(t)\le\bar F(x+t);\quad
--   \mathrm{NWUE}:R(0)\le R(t)/\bar F(t).
--   $$
--
--   IMRL and NWUE compare nonnegative ages with positive survival, DHRA compares positive ages, and NWU uses nonnegative $x,t$. All monotonicity is weak. These predicates supply the missing reversed classes for Theorem 3.2.
--
--   **Formalization Note** The residual integral is the published `ShockWear.Inherit.resInt`; its ratios are in $[0,\infty]$, without a finite-mean assumption. DHR and logarithmically convex density are already defined by the published model and are reused.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 630–632, Definition 2.3 and ageing definitions; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

open scoped ENNReal

/-- (iii′), pp. 631–632: extended mean residual life increases on its defined domain. -/
def IsIMRL (Fb : ℝ → ℝ) : Prop :=
  MonotoneOn (fun t => resInt Fb t / ENNReal.ofReal (Fb t))
    {t | 0 ≤ t ∧ 0 < Fb t}

/-- (iv′): survival roots increase at positive ages. -/
def IsDHRA (Fb : ℝ → ℝ) : Prop :=
  MonotoneOn (fun t => Fb t ^ (1 / t)) (Set.Ioi 0)

/-- (v′): new worse than used, cross-multiplied. -/
def IsNWU (Fb : ℝ → ℝ) : Prop :=
  ∀ x t, 0 ≤ x → 0 ≤ t → Fb x * Fb t ≤ Fb (t + x)

/-- (vi′): extended expected life is at most the defined residual mean. -/
def IsNWUE (Fb : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → 0 < Fb t → resInt Fb 0 ≤ resInt Fb t / ENNReal.ofReal (Fb t)

end ShockWear.Inherit.Supplement


