-- Prove2me | Definitions.Def_QuarticGap_lenSqDist
-- name    : QuarticGap_lenSqDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:15.722333+00:00
-- url     : https://prove2.me/theorems/fa005403-4e01-449b-936b-ab97cc90fadc
-- title:
--   Length-squared distribution, total variation distance, uniform averages
-- statement:
--   For a nonzero vector $x$ indexed by a finite set $Y$, the **length-squared distribution** is
--   $$
--   p_x(j) = \frac{|x_j|^2}{\|x\|^2} .
--   $$
--   The **total variation distance** between two distributions on $Y$ is $\mathrm{TV}(p,q) = \frac12 \sum_j |p(j) - q(j)|$. This item also fixes the expectation and the probability of an event under the uniform distribution on a finite set, which is how "uniformly random $f$" and "uniformly random $W$" are written, and the real value of a sign in $\{-1,1\}$.
--
--   These are the output task and the averaging used by every statement of the mission.
--
--   **Formalization Note** At $x = 0$ the quotient is $0$; statements carry $x \ne 0$ or a matrix for which it is provable. Independent uniform signs are the uniform distribution on the finite set of sign functions, so no measure is needed.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), §2.1, p.15

import Mathlib

namespace QuarticGap

/-- Length-squared distribution `p_x(j) = |x_j|² / ‖x‖²` of a vector `x` indexed by a finite set
(Chakrabarti, Herman, Kim, Ozgul, *The Quartic Gap Between Quantum and Dequantized Algorithms for
Linear Algebra Is Tight*, arXiv:2610.42069 (file sha256 9f68aaf9…), §2.1, p.15).

**Formalization Note** The source defines it for nonzero `x`; at `x = 0` the Lean value is `0`, and
every statement carries `x ≠ 0` or a matrix for which it is provable. -/
noncomputable def lenSqDist {Y E : Type*} [Fintype Y] [Norm E] (x : Y → E) (j : Y) : ℝ :=
  ‖x j‖ ^ 2 / ∑ i, ‖x i‖ ^ 2

/-- Total variation distance `TV(p, q) = ½ ∑_j |p(j) − q(j)|` (arXiv:2610.42069, §2.1, p.15). -/
noncomputable def tv {Y : Type*} [Fintype Y] (p q : Y → ℝ) : ℝ :=
  (1 / 2) * ∑ j, |p j - q j|

/-- Expectation of `g` under the uniform distribution on a finite set. Used for "uniformly random
`f`" and "uniformly random `W`" (arXiv:2610.42069, §2.4, §3.1).

**Formalization Note** Independent uniform signs are exactly the uniform distribution on the finite
set of sign functions, so no measure is needed. -/
noncomputable def uAvg {X : Type*} [Fintype X] (g : X → ℝ) : ℝ :=
  (∑ x, g x) / Fintype.card X

open Classical in
/-- Probability of an event under the uniform distribution on a finite set. -/
noncomputable def uProb {X : Type*} [Fintype X] (P : X → Prop) : ℝ :=
  uAvg fun x => if P x then 1 else 0

/-- A sign `u ∈ {−1, 1}` as a real number. Boolean functions and sign matrices take values in
`ℤˣ`, which has exactly the two elements `±1`. -/
def sgn (u : ℤˣ) : ℝ :=
  ((u : ℤ) : ℝ)

end QuarticGap


