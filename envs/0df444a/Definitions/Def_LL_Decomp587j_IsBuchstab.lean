-- Prove2me | Definitions.Def_LL_Decomp587j_IsBuchstab
-- name    : LL_Decomp587j_IsBuchstab
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:15:52.411738+00:00
-- url     : https://prove2.me/theorems/6edf183c-4b36-48a0-8037-07a9eccc898d
-- title:
--   Buchstab's function
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, the proposition that $\omega$ is continuous on $[1,\infty)$, that $\omega(u)=1/u$ for all $1\le u\le2$, and that for every $u>2$ the function $v\mapsto v\,\omega(v)$ has derivative $\omega(u-1)$ at $u$.

import Mathlib

open Real Set MeasureTheory
open scoped Classical

namespace LL_Decomp587j

def IsBuchstab (ω : ℝ → ℝ) : Prop :=
  ContinuousOn ω (Ici 1) ∧ (∀ u : ℝ, 1 ≤ u → u ≤ 2 → ω u = 1 / u) ∧
    (∀ u : ℝ, 2 < u → HasDerivAt (fun v => v * ω v) (ω (u - 1)) u)

end LL_Decomp587j


