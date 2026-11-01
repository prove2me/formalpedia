-- Prove2me | Definitions.Def_NoSignalPA_chshPow
-- name    : NoSignalPA_chshPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:24.75843+00:00
-- url     : https://prove2.me/theorems/70ea424a-a8e0-4ffa-837e-6f315ab2dda2
-- title:
--   The tensor power $|\mathrm{CHSH}\rangle^{\otimes N_r}$
-- statement:
--   The vector $|\mathrm{CHSH}\rangle^{\otimes n}\in\mathbb R^{16^n}$, with entries
--
--   $$
--   \mathrm{CHSH}^{\otimes n}(\mathbf a,\mathbf b,\mathbf x,\mathbf y)=\prod_{i=1}^{n}\mathrm{CHSH}(a_i,b_i,x_i,y_i),
--   $$
--
--   the product of the entries of (2) over the $n$ pairs of systems. It is the coefficient vector of the right side of the security bound (5).
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, eq. (5), p.2; Appendix, pp.4–5

import Mathlib
import Definitions.Def_NoSignalPA_Str
import Definitions.Def_NoSignalPA_chshCoef

namespace NoSignalPA

/-- **The tensor power `|CHSH⟩^{⊗Nr}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, eq. (5), p. 2, and Appendix, pp. 4–5 (entries `CHSH^{⊗Nr}(a, b, x, y)`), printed = PDF pages.

The entry of `|CHSH⟩^{⊗n}` at `(a, b, x, y) ∈ ({0,1}^n)^4` is the product over coordinates
`i` of the single-system entries `chshCoef (a i) (b i) (x i) (y i)`. -/
noncomputable def chshPow {n : ℕ} (a b x y : Str n) : ℝ :=
  ∏ i, chshCoef (a i) (b i) (x i) (y i)

end NoSignalPA


