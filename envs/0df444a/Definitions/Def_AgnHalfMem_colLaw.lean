-- Prove2me | Definitions.Def_AgnHalfMem_colLaw
-- name    : AgnHalfMem_colLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:59.49008+00:00
-- url     : https://prove2.me/theorems/8e087d88-e03e-4e7d-82f3-18e62dd585e1
-- title:
--   The learning problem of a matrix: the column law $D_h$ and the joint law
-- statement:
--   Let $H$ be a finite nonempty set, $\mu$ a probability measure on $X$ and $M:X\times H\to[-1,1]$. The **learning problem of $M$** is: a column $h\in H$ is drawn uniformly at random, and the learner sees i.i.d. samples $(x,y)$ with $x\sim\mu$ and
--   $$
--   \Pr[y\mid x]=\frac{1+y\,M(x,h)}{2},\qquad y\in\{-1,1\},
--   $$
--   so that $\mathbb E[y\mid x]=M(x,h)$. The law of one sample given $h$ is $D_h$, and $\mathrm{err}_h(g)=\Pr_{(x,y)\sim D_h}[g(x)\ne y]$. The joint law of $(h,(x_1,y_1),\dots,(x_T,y_T))$ draws $h$ uniformly and then $T$ samples i.i.d. from $D_h$; for a randomized learner an independent seed $\omega\sim P$ is drawn as well.
--
--   **Formalization Note** $D_h$ is the sum over $y$ of $\mu$ with density $(1+yM(\cdot,h))/2$, placed on $X\times\{y\}$; it is a probability measure with $X$-marginal $\mu$ when $M(\cdot,h)$ is measurable. $H$ carries the discrete σ-algebra where the joint law is used.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), §2, pp.6–7; Definition B.3, p.28

import Mathlib
import Definitions.Def_AgnHalfMem_sgn
import Definitions.Def_AgnHalfMem_err

open MeasureTheory

namespace AgnHalfMem

/-- **The learning problem of a matrix (§2, pp.6–7; Definition B.3, p.28).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), pp.6–7: "Let M : X × H → [−1, 1] be a matrix. Fix a probability
measure μ over X. The matrix M corresponds to the following learning problem: There is an unknown
element h ∈ H that was chosen uniformly at random. A learner tries to learn h from a stream of
samples of the form (x, y), where each x ∈ X is drawn i.i.d. from μ and E[y|x] = M(x, h), that is,
y = 1 with probability (M(x,h)+1)/2, and −1 with probability (1−M(x,h))/2."

`colLaw μ M h` is the law `D_h` of one sample `(x, y)` given the column `h`: `x ∼ μ` and
`Pr[y | x] = (1 + y M(x, h))/2`.

**Formalization Note.** Labels are `Bool` (`true ↔ +1`, `sgn` gives `±1`). `D_h` is written as
the sum over the two labels of `μ` with density `(1 + y M(·, h))/2` pushed to `X × {y}`. For
`M` measurable in `x` with values in `[−1, 1]` it is a probability measure with `X`-marginal `μ`. -/
noncomputable def colLaw {X H : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → H → ℝ)
    (h : H) : Measure (X × Bool) :=
  ∑ y : Bool, (μ.withDensity fun x => ENNReal.ofReal ((1 + sgn y * M x h) / 2)).map
    (fun x => (x, y))

/-- `err_h(g) = Pr_{x∼μ, y|x,h}[g(x) ≠ y]` (Definition B.3, p.28): the error of `g` on the data
distribution of column `h`. -/
noncomputable def errCol {X H : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → H → ℝ)
    (h : H) (g : X → Bool) : ℝ :=
  err (colLaw μ M h) g

/-- The joint law of `(h, (x₁, y₁), …, (x_T, y_T))`: `h` uniform on `H`, then `T` i.i.d. samples
from `D_h` (p.7; App. B, p.29: "the probability is over h, x1, x2, …, xm, y1, y2, …, ym"). -/
noncomputable def jointLaw {X H : Type*} [MeasurableSpace X] [Fintype H] [MeasurableSpace H]
    (μ : Measure X) (M : X → H → ℝ) (T : ℕ) : Measure (H × (Fin T → X × Bool)) :=
  ∑ h, ((Fintype.card H : ENNReal)⁻¹) •
    (Measure.dirac h).prod (Measure.pi fun _ : Fin T => colLaw μ M h)

/-- The joint law of `(h, ω, (x₁, y₁), …, (x_T, y_T))` for a randomized learner with seed law `P`:
`h` uniform, the seed `ω ∼ P` independent of `h` and of the samples, the samples i.i.d. from
`D_h` (the probability of Definition B.3, p.28, with the learner's own randomness added). -/
noncomputable def seededJointLaw {X H Ω : Type*} [MeasurableSpace X] [Fintype H]
    [MeasurableSpace H] [MeasurableSpace Ω] (μ : Measure X) (M : X → H → ℝ) (P : Measure Ω)
    (T : ℕ) : Measure (H × Ω × (Fin T → X × Bool)) :=
  ∑ h, ((Fintype.card H : ENNReal)⁻¹) •
    (Measure.dirac h).prod (P.prod (Measure.pi fun _ : Fin T => colLaw μ M h))

end AgnHalfMem


