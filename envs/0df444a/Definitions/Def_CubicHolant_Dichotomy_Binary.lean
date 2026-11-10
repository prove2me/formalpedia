-- Prove2me | Definitions.Def_CubicHolant_Dichotomy_Binary
-- name    : CubicHolant_Dichotomy_Binary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:36:44.229033+00:00
-- url     : https://prove2.me/theorems/4216f687-6204-4ebb-96b3-52dc53143189
-- title:
--   The binary contraction $F_f(v)$ and the Kowalczyk–Cai table of tractable symmetric binary signatures
-- statement:
--   1. Attaching a right unary row $v=(r,s)$ to one input of $f=[f_0,f_1,f_2,f_3]$ gives the symmetric binary signature $F_f(v)(x,y)=\sum_z f(x,y,z)v_z$ (p. 21, Figure 10):
--   $$F_f(v)=[f_0r+f_1s,\ f_1r+f_2s,\ f_2r+f_3s].$$
--   For $f=[1,a,b,c]$ this is $[r+as,\ ar+bs,\ br+cs]$ (p. 22).
--   2. A symmetric binary $g=[g_0,g_1,g_2]$ is **in the Kowalczyk–Cai table** (p. 22) if it is of one of the following types:
--      - rank one: $g_0g_2=g_1^2$;
--      - diagonal: $g_1=0$;
--      - disequality: $g_0=g_2=0$;
--      - additional affine type: $g_1\neq0$, $g_0g_2=-g_1^2$ and $(g_0/g_1)^{12}=1$.
--
--   Otherwise it is **outside the table**. These are the binaries $g$ for which $\mathrm{Holant}(g\mid e)$ is tractable [KC16].
--
--   **Formalization Note** `contrBin f v : Fin 3 → ℂ` and `InKCTable g`. The table is invariant under nonzero scaling of $g$, so membership depends only on the projective direction of $v$.
-- source:
--   Yin Liu, A Dichotomy for Cubic Bipartite Holant Problems with Complex Algebraic Weights, STOC 2027 submission (manuscript sha256 f70906c3…), pp. 21–22, §3.4

import Mathlib

set_option autoImplicit false

namespace CubicHolant.Dichotomy

/-! # The binary contraction `F_f(v)` and the Kowalczyk–Cai table

Yin Liu, *A Dichotomy for Cubic Bipartite Holant Problems with Complex Algebraic Weights*, STOC 2027
submission (manuscript sha256 f70906c3…), §3.4, pp. 21–22. -/

/-- The binary contraction `F_f(v)` (p. 21, Figure 10): attaching the right unary row
`v = (r, s)` to one input of `f` gives the symmetric binary signature
`F(v)(x, y) = Σ_z f(x, y, z) v_z = [f₀r + f₁s, f₁r + f₂s, f₂r + f₃s]`; for `f = [1, a, b, c]` this is
`[r + as, ar + bs, br + cs]` (p. 22). -/
def contrBin (f : Fin 4 → ℂ) (v : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![f 0 * v 0 + f 1 * v 1, f 1 * v 0 + f 2 * v 1, f 2 * v 0 + f 3 * v 1]

/-- The binary `g = [g₀, g₁, g₂]` lies in the Kowalczyk–Cai tractable table (p. 22): rank one
(`g₀g₂ = g₁²`), diagonal (`g₁ = 0`), disequality (`g₀ = g₂ = 0`), or one of the additional affine
types (`g₁ ≠ 0`, `g₀g₂ = −g₁²`, `(g₀/g₁)¹² = 1`). -/
def InKCTable (g : Fin 3 → ℂ) : Prop :=
  g 0 * g 2 = g 1 ^ 2 ∨ g 1 = 0 ∨ (g 0 = 0 ∧ g 2 = 0) ∨
    (g 1 ≠ 0 ∧ g 0 * g 2 = -(g 1 ^ 2) ∧ (g 0 / g 1) ^ 12 = 1)

end CubicHolant.Dichotomy


