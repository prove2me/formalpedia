-- Prove2me | Definitions.Def_SelectiveDPT_rangeProj
-- name    : SelectiveDPT_rangeProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:51.674785+00:00
-- url     : https://prove2.me/theorems/662b5ada-822d-4dfc-aab2-8257f4f961c8
-- title:
--   Projection $\Pi_{R^{-1}(y)}$
-- statement:
--   For a relation $R \subseteq D \times Y$ and $y \in Y$, $\Pi_{R^{-1}(y)}$ is the projection on $\mathbb C^D$
--   $$\Pi_{R^{-1}(y)} = \sum_{x \in D:\ (x,y) \in R} |x\rangle\langle x| ,$$
--   onto the inputs for which $y$ is a correct answer. For a function, $R^{-1}(y) = f^{-1}(y)$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.10

import Mathlib

namespace SelectiveDPT

/-- The projection `Π_{R⁻¹(y)} = Σ_{x ∈ R⁻¹(y)} |x⟩⟨x|` on `ℂ^D` (arXiv:2609.26678, §2.2, p.10:
"for each `y ∈ Y` we define `Π_{R⁻¹(y)}` to be the projection on `D`"), the diagonal matrix with
entry `1` at the inputs `x ∈ D` with `(x, y) ∈ R` and `0` elsewhere. For a function, `R⁻¹(y)` is
`f⁻¹(y)`. -/
noncomputable def rangeProj {α Y : Type*} [DecidableEq α] (D : Finset α) (R : α → Y → Prop)
    (y : Y) : Matrix D D ℂ := by
  classical
  exact Matrix.diagonal fun x => if R x.1 y then 1 else 0

end SelectiveDPT


