-- Prove2me | Definitions.Def_BartlettNN_Margin_Classification
-- name    : BartlettNN_Margin_Classification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:27:12.829759+00:00
-- url     : https://prove2.me/theorems/acc8ded2-c2a9-4a09-96ee-f7080f96f0a5
-- title:
--   Threshold sgn, misclassification probability er_P(h) and margin error estimate êr^γ_z(h) (§II)
-- statement:
--   Let $X$ be a set (the input space) and let $P$ be a probability distribution on $X \times \{-1,1\}$. The **threshold function** $\operatorname{sgn}:\mathbb R\to\{-1,1\}$ is
--   $$
--   \operatorname{sgn}(\alpha)=\begin{cases}-1, & \alpha<0,\\ 1, & \alpha\ge 0,\end{cases}
--   $$
--   so that $\operatorname{sgn}(0)=1$. For a real-valued hypothesis $h$ on $X$, the **misclassification probability** is
--   $$
--   \operatorname{er}_P(h)=P\{(x,y): \operatorname{sgn}(h(x))\neq y\}.
--   $$
--   For a training sample $z=((x_1,y_1),\dots,(x_m,y_m))\in (X\times\{-1,1\})^m$ and $\gamma>0$, the **margin error estimate** is the proportion of examples not classified correctly with margin $\gamma$:
--   $$
--   \widehat{\operatorname{er}}{}^{\gamma}_z(h)=\frac1m\,\bigl|\{i : y_i h(x_i)<\gamma\}\bigr| .
--   $$
--   These are the quantities compared by every generalization bound of the paper.
--
--   **Formalization Note** Labels are `Bool`, read as real numbers through `pm`: `true` is $+1$ and `false` is $-1$. The sample is a function `Fin m → X × Bool`, indexed from $0$. The inequality in $\widehat{\operatorname{er}}{}^{\gamma}_z$ is strict, as on the page. $\operatorname{er}_P(h)$ is the real-valued measure `P.real` of the misclassification set; the paper assumes all sets considered are measurable (p. 526), and the theorems that use $\operatorname{er}_P$ assume each hypothesis measurable.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 526, Section II (definitions of sgn, er_P(h), êr^γ_z(h))

import Mathlib

open MeasureTheory

namespace BartlettNN.Margin

/-- Labels `{−1, 1}` are encoded as `Bool`: `pm true = 1` and `pm false = -1`
(Bartlett 1998, p. 526: `P` is a distribution on `X × {−1, 1}`). -/
def pm (b : Bool) : ℝ := if b then 1 else -1

/-- The threshold function `sgn : ℝ → {−1, 1}` of Bartlett (1998, p. 526):
`sgn α = −1` for `α < 0` and `sgn α = 1` for `α ≥ 0`. In particular `sgn 0 = 1`
(unlike `Real.sign`). -/
noncomputable def sgn (α : ℝ) : ℝ := if α < 0 then -1 else 1

/-- The misclassification probability `er_P(h) = P{sgn(h(x)) ≠ y}` of a real-valued hypothesis
`h` under a distribution `P` on `X × {−1, 1}` (p. 526). -/
noncomputable def er {X : Type*} [MeasurableSpace X] (P : Measure (X × Bool)) (h : X → ℝ) : ℝ :=
  P.real {p | sgn (h p.1) ≠ pm p.2}

/-- The margin error estimate `êr^γ_z(h) = (1/m) |{i : y_i h(x_i) < γ}|` of `h` on the sample
`z = ((x_1, y_1), …, (x_m, y_m))` (p. 526); the inequality is strict. Sample indices are 0-based. -/
noncomputable def erHat {X : Type*} (γ : ℝ) {m : ℕ} (z : Fin m → X × Bool) (h : X → ℝ) : ℝ :=
  ((Finset.univ.filter fun i => pm (z i).2 * h (z i).1 < γ).card : ℝ) / m

end BartlettNN.Margin


