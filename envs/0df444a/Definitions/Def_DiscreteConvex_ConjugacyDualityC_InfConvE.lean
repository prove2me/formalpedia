-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE
-- name    : DiscreteConvex_ConjugacyDualityC_InfConvE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:11.110975+00:00
-- url     : https://prove2.me/theorems/00326fe0-2bf7-4871-a86c-bbe413e7279d
-- title:
--   Infimal convolution in the extended reals
-- statement:
--   The integer infimal convolution $(g_1\square g_2)(p)=\inf\{g_1(p_1)+g_2(p_2) : p_1+p_2=p\}$ computed in $\overline{\mathbb{R}}=\mathbb{R}\cup\{\pm\infty\}$, where the infimum is genuine.
--
--   The book's $L_2$-convex functions require $g_1\square g_2 > -\infty$, which is exactly "this value is never $-\infty$".
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §8.3, p.230.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §8.3, p.230

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ToEReal

namespace DiscreteConvex.ConjugacyDualityC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The integer infimal convolution `(g1□g2)(p) = inf{g1(p1)+g2(p2) : p1+p2=p}` computed in
`EReal`, where the infimum is genuine. `InfConv` takes the same infimum in `WithTop ℝ`, which is
only conditionally complete: when the values are unbounded below it reads the junk value `0`
(`g1(p) = p₁` and `g2(p) = -p₁ + p₂` are L-convex with `g1 □ g2 = -∞` everywhere, and `InfConv`
returns the constant `0`). Murota's L₂-convex functions require `g1 □ g2 > -∞`, which is
`InfConvE g1 g2 p ≠ ⊥`. -/
noncomputable def InfConvE (g1 g2 : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : EReal :=
  sInf {L : EReal | ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ L = ToEReal (g1 p1) + ToEReal (g2 p2)}

end DiscreteConvex.ConjugacyDualityC


