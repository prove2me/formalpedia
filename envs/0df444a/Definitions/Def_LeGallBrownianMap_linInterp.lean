-- Prove2me | Definitions.Def_LeGallBrownianMap_linInterp
-- name    : LeGallBrownianMap_linInterp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:24.388705+00:00
-- url     : https://prove2.me/theorems/52b09188-d9ad-457c-8fd7-65c0f0eeef4a
-- title:
--   Linear interpolation of a sequence
-- statement:
--   For a real sequence $(a_i)_{i\ge0}$ and $x\ge0$, the linear interpolation $a(x)=(\lfloor x\rfloor+1-x)\,a_{\lfloor x\rfloor}+(x-\lfloor x\rfloor)\,a_{\lfloor x\rfloor+1}$. The contour and label functions $C^n$, $\Lambda^n$ are extended to $[0,pn]$ this way.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.5, p.15

import Mathlib

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.5, p.15:
"We extend the definition of both C^n and Λ^n to the real interval [0, pn] by linear
interpolation."

`linInterp a x` is the linear interpolation of the sequence `a` at `x ≥ 0`:
`(⌊x⌋ + 1 − x) a_{⌊x⌋} + (x − ⌊x⌋) a_{⌊x⌋+1}`.

**Formalization Note.** `⌊x⌋` is `Nat.floor`; the formula is only used for `x ∈ [0, pn]`. At an
integer `x = m` it returns `a_m`. -/
noncomputable def linInterp (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ((⌊x⌋₊ : ℝ) + 1 - x) * a ⌊x⌋₊ + (x - ⌊x⌋₊) * a (⌊x⌋₊ + 1)

end LeGallBrownianMap


