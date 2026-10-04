-- Prove2me | Definitions.Def_ZetaNine_GramContent
-- name    : ZetaNine_GramContent
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:08:19.288988+00:00
-- url     : https://prove2.me/theorems/39d7d208-ec83-47a7-af52-066c32893c39
-- title:
--   Integral row Gram data and divided determinant
-- statement:
--   For integral rows $u,v$ in any finite dimension, define their scalar product $C=\sum_i u_i v_i$, squared norms $T=\sum_i u_i^2$, $R=\sum_i v_i^2$, and the integer quotient $D_\Delta=(TR-C^2)/\Delta^2$. Integer division is used at the definition level; the companion theorem proves exact division when $u$ is primitive and $\Delta$ divides every minor. No primitivity, divisibility or positivity assumption is built into these definitions.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/direction-arithmetic-next-2026-10-02.md, section 1, equations (1) and (5).

import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators

namespace ZetaNine.GramContent

variable {ι : Type*} [Fintype ι]

/-- The integral scalar product, in arbitrary finite dimension. -/
def dot (u v : ι → ℤ) : ℤ := ∑ i, u i * v i

/-- The square norm of an integral row. -/
def normSq (u : ι → ℤ) : ℤ := dot u u

/-- The integral quotient representing the squared norm of the divided
exterior row. For a common minor divisor the division is exact. -/
def saturatedGram (u v : ι → ℤ) (Δ : ℤ) : ℤ :=
  (normSq u * normSq v - (dot u v) ^ 2) / (Δ ^ 2)


end ZetaNine.GramContent


