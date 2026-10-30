-- Prove2me | Definitions.Def_JailletLu_fStar
-- name    : JailletLu_fStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:05.114249+00:00
-- url     : https://prove2.me/theorems/feab7d85-ea38-48aa-ac82-4237eb84d44a
-- title:
--   The numbers $f_{a_1}$ for $a_1\in A^*$, with $f_{a_d}=1$
-- statement:
--   For $b\in A^*=A\cup\{a_d\}$, $f_b$ is the total flow $f_b=\sum_i f_{b,i}$ if $b$ is a real advertiser, and $f_{a_d}=1$ for the dummy: "the dummy advertiser is full at the very beginning". These are the numbers $f_{a_1}$ appearing in $g(f_{a_1},m_{a_1,a})$ in §5.4.
--
--   **Formalization Note** The value at the dummy is the paper's convention $f_{a_d}\triangleq 1$, not the dummy's total flow.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib
import Definitions.Def_JailletLu_fTot

namespace JailletLu

/-- **The numbers `f_{a1}` for `a1 ∈ A* = A ∪ {a_d}`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "a dummy advertiser a_d with f_{a_d} ≜ 1".

`fStar f (some a) = f_a` (total flow) and `fStar f none = 1` (the dummy, `none` = `a_d`).

**Formalization Note.** The value at the dummy is the paper's convention `f_{a_d} ≜ 1`, not the
dummy's total flow `Σ_i (r_i − Σ_a f_{a,i})`. -/
noncomputable def fStar {A I : Type*} [Fintype I] (f : A → I → ℝ) : Option A → ℝ
  | none => 1
  | some a => fTot f a

end JailletLu


