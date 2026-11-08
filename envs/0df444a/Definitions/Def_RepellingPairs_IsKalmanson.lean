-- Prove2me | Definitions.Def_RepellingPairs_IsKalmanson
-- name    : RepellingPairs_IsKalmanson
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:41.732255+00:00
-- url     : https://prove2.me/theorems/ee994244-66d5-4ba0-b9bf-687bc23604b9
-- title:
--   Kalmanson (Okamura-Seymour) four-point condition
-- statement:
--   A metric $D$ on terminals with a prescribed cyclic order is a **Kalmanson metric**, or OS metric, if whenever $t_1,t_2,t_3,t_4$ occur in this order,
--
--   $$
--   \max\{D(t_1,t_2)+D(t_3,t_4),\ D(t_1,t_4)+D(t_2,t_3)\}\le D(t_1,t_3)+D(t_2,t_4).
--   $$
--
--   This condition characterizes the metrics realized by OS instances with the given order.
--
--   **Formalization Note** It is stated for $a<b<c<d$. For a symmetric $D$ the inequality is unchanged under rotation and reflection of the quadruple, so this is the same as the condition for every quadruple in cyclic order.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.5

import Mathlib

set_option autoImplicit false

namespace RepellingPairs

/-- The Kalmanson (Okamura-Seymour) four-point condition for the cyclic order of `Fin k`: "whenever
t1, t2, t3, t4 occur in this order, max{D(t1, t2) + D(t3, t4), D(t1, t4) + D(t2, t3)} ≤ D(t1, t3) +
D(t2, t4)". Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.5.

**Formalization Note.** Stated for `a < b < c < d`. For a symmetric `D` the inequality is unchanged
under rotation and reflection of the quadruple, so this is the same as asking it for every quadruple in
cyclic order. -/
def IsKalmanson {k : ℕ} (D : Fin k → Fin k → ℝ) : Prop :=
  ∀ a b c d : Fin k, a < b → b < c → c < d →
    max (D a b + D c d) (D a d + D b c) ≤ D a c + D b d

end RepellingPairs


