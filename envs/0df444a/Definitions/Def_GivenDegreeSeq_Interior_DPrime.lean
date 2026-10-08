-- Prove2me | Definitions.Def_GivenDegreeSeq_Interior_DPrime
-- name    : GivenDegreeSeq_Interior_DPrime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:50:56.509408+00:00
-- url     : https://prove2.me/theorems/518db5fc-537c-4115-b355-4157921a47f2
-- title:
--   The space $D'[0,1]$, the modified $L^1$ norm $\|\cdot\|_{1'}$, and the functional $G_f$
-- statement:
--   1. $D'[0,1]$ is the set of functions $f:[0,1]\to\mathbb R$ that are nonincreasing on $[0,1]$ and left continuous at every point of the open interval $(0,1)$.
--   2. The **modified $L^1$ norm** of a function $f$ on $[0,1]$ is
--   $$\|f\|_{1'}:=|f(0)|+|f(1)|+\int_0^1|f(x)|\,dx.$$
--   3. For $f\in D'[0,1]$ and $x\in[0,1]$,
--   $$G_f(x):=\int_x^1\min\{f(y),x\}\,dy+x^2-\int_0^x f(y)\,dy.$$
--
--   $D'[0,1]$ is the space in which scaling limits of degree sequences live (left continuity selects a unique representative of a discontinuous limit), $\|\cdot\|_{1'}$ is the norm whose topology matches convergence of degree sequences in the sense of (2), and $G_f$ is the continuum analogue of the slack in the Erdős–Gallai inequalities.
--
--   **Formalization Note** Functions are `ℝ → ℝ`; only their values on $[0,1]$ enter these three objects (left continuity at $x\in(0,1)$ involves only values near $x$). The integrals are interval integrals. Every $f\in D'[0,1]$ is monotone, hence bounded and integrable on $[0,1]$, so the integrals are genuine (no junk value $0$ from non-integrability).
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 4 (D′[0,1] and ‖·‖_{1′}) and p. 23 (G_f, proof of Proposition 1.2)

import Mathlib

namespace GivenDegreeSeq.Interior

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5, p. 4: the space `D′[0,1]` and the modified `L¹` norm `‖·‖_{1′}`; p. 23: the
function `G_f`.

Functions on `[0,1]` are represented as `f : ℝ → ℝ`; only the values of `f` on `[0,1]` enter
`InDprime`, `norm1'` and `Gf` (the latter for arguments `x ∈ [0,1]`). -/

/-- `f ∈ D′[0,1]` (p. 4): `f` is nonincreasing on `[0,1]` and left continuous at every point of
`(0,1)`. Left continuity at `x ∈ (0,1)` only involves values of `f` near `x`, which lie in
`(0,1)`. -/
def InDprime (f : ℝ → ℝ) : Prop :=
  AntitoneOn f (Set.Icc 0 1) ∧ ∀ x ∈ Set.Ioo (0 : ℝ) 1, ContinuousWithinAt f (Set.Iic x) x

/-- The modified `L¹` norm `‖f‖_{1′} := |f(0)| + |f(1)| + ∫₀¹ |f(x)| dx` (p. 4). -/
noncomputable def norm1' (f : ℝ → ℝ) : ℝ :=
  |f 0| + |f 1| + ∫ x in (0 : ℝ)..1, |f x|

/-- `G_f(x) := ∫ₓ¹ min{f(y), x} dy + x² − ∫₀ˣ f(y) dy` (p. 23), the continuum Erdős–Gallai
functional. -/
noncomputable def Gf (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in x..1, min (f y) x) + x ^ 2 - ∫ y in (0 : ℝ)..x, f y

end GivenDegreeSeq.Interior


