-- Prove2me | Definitions.Def_LL_Decomp587k_IsBuchstab
-- name    : LL_Decomp587k_IsBuchstab
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-20T07:42:06.932158+00:00
-- url     : https://prove2.me/theorems/b6428212-9d45-4a07-b1d2-74255f4169e8
-- title:
--   Buchstab's function
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega$ is continuous on $[1,\infty)$, that $\omega(u)=1/u$ for all $1\le u\le2$, and that for every $u>2$ the function $v\mapsto v\,\omega(v)$ has derivative $\omega(u-1)$ at $u$.

import Mathlib

namespace LL_Decomp587k

noncomputable section

open Real Set MeasureTheory
open scoped Classical

def IsBuchstab (ω : ℝ → ℝ) : Prop :=
  ContinuousOn ω (Ici 1) ∧ (∀ u : ℝ, 1 ≤ u → u ≤ 2 → ω u = 1 / u) ∧
    (∀ u : ℝ, 2 < u → HasDerivAt (fun v => v * ω v) (ω (u - 1)) u)

end

end LL_Decomp587k


