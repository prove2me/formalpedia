-- Prove2me | Definitions.Def_KSPolySign_faceProj
-- name    : KSPolySign_faceProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:18.034595+00:00
-- url     : https://prove2.me/theorems/fd33e335-aaf9-446b-bcd4-e102080a5d32
-- title:
--   Projection onto the face of a fractional signing
-- statement:
--   For $y,x\in\mathbb R^k$, $\mathrm{faceProj}(y,x)$ is the vector whose $i$-th coordinate is $x_i$ if $|y_i|<1$ (an active coordinate of $y$) and $y_i$ otherwise. It moves the active coordinates of $y$ and keeps the signed ones fixed, so functions of $x$ composed with it are functions on the face of $y$.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.5, p.19 (PDF p.19); Definition 3.8, p.22 (PDF p.22)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Projection onto the face of `y`.** `faceProj y x` keeps the coordinates of `x` where `y` is
active (`|y_i| < 1`) and the coordinates of `y` where `y` is fixed (`|y_i| = 1`).
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.5, p.19 (PDF p.19): "A coordinate i is active when −1 < y_i < 1"; Definition 3.8,
p.22: "A direction r ∈ ℝ^{k_act} is extended by zero on the fixed coordinates". -/
noncomputable def faceProj {k : ℕ} (y x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if |y i| < 1 then x i else y i

end KSPolySign


