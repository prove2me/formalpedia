-- Prove2me | Definitions.Def_RepellingPairs_CyclicallyOrdered
-- name    : RepellingPairs_CyclicallyOrdered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:40.109487+00:00
-- url     : https://prove2.me/theorems/d4436817-2c32-4467-80da-a72cfbc9a41b
-- title:
--   Four points in cyclic order on a circle
-- statement:
--   Points $a,b,c,d$ of $\{0,\dots,n-1\}$, arranged on a circle in the natural cyclic order, **occur in this order** if they are distinct and $(a,b,c,d)$ is a rotation of a strictly increasing quadruple.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.5

import Mathlib

set_option autoImplicit false

namespace RepellingPairs

/-- `a, b, c, d` are distinct and occur in this order around the circle whose points are `Fin n` in
their natural cyclic order: `(a, b, c, d)` is a rotation of a strictly increasing quadruple.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.5 ("occur in this
order"). -/
def CyclicallyOrdered {n : ℕ} (a b c d : Fin n) : Prop :=
  (a < b ∧ b < c ∧ c < d) ∨ (b < c ∧ c < d ∧ d < a) ∨ (c < d ∧ d < a ∧ a < b) ∨
    (d < a ∧ a < b ∧ b < c)

instance {n : ℕ} (a b c d : Fin n) : Decidable (CyclicallyOrdered a b c d) := by
  unfold CyclicallyOrdered; infer_instance

end RepellingPairs


