-- Prove2me | Definitions.Def_AdaptDRO_LiftedLDR_RecourseLP
-- name    : AdaptDRO_LiftedLDR_RecourseLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T18:47:12.268837+00:00
-- url     : https://prove2.me/theorems/25b63db3-89cb-47b8-a79f-4534a64823e6
-- title:
--   Free-variable linear recourse LP, feasibility, value, and dual feasibility
-- statement:
--   A free-variable **recourse linear program** has a matrix $B\in\mathbb R^{M\times N}$ and cost vector $d\in\mathbb R^N$. For a right-hand side $t\in\mathbb R^M$, its feasible vectors satisfy $By\ge t$, and its value is
--
--   $$
--   Q_B(t)=\inf\{d^\top y:By\ge t,\ y\in\mathbb R^N\}.
--   $$
--
--   Complete recourse means this set is nonempty for every $t$. Dual feasibility means there is a nonnegative $p\in\mathbb R^M$ with $B^\top p=d$. Together with primal feasibility, dual feasibility ensures that the displayed real infimum represents a finite LP minimum. This reusable object supplies the second-stage optimization problem in the paper.
--
--   **Formalization Note** The real infimum has Lean's default value when the feasible set is empty or unbounded below. Every theorem using the value carries primal and dual feasibility hypotheses that exclude those cases.
-- source:
--   Bertsimas, Sim, Zhang, Adaptive distributionally robust optimization, Management Science 65(2) (2019), p. 606, Eq. (1), Definitions 1–2; p. 608, dual polyhedron following Eq. (10)

import Mathlib

namespace AdaptDRO.LiftedLDR

/-- A free-variable linear recourse problem with constraints `B y ≥ t`. -/
structure RecourseLP (M N : ℕ) where
  B : Matrix (Fin M) (Fin N) ℝ
  d : Fin N → ℝ

def RecourseLP.Feasible {M N : ℕ} (R : RecourseLP M N) (t : Fin M → ℝ) : Prop :=
  ∃ y : Fin N → ℝ, t ≤ R.B.mulVec y

/-- The real LP minimum; its use requires primal and dual feasibility. -/
noncomputable def RecourseLP.value {M N : ℕ} (R : RecourseLP M N)
    (t : Fin M → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ y : Fin N → ℝ, t ≤ R.B.mulVec y ∧ c = dotProduct R.d y}

def RecourseLP.Complete {M N : ℕ} (R : RecourseLP M N) : Prop :=
  ∀ t : Fin M → ℝ, R.Feasible t

def RecourseLP.DualFeasible {M N : ℕ} (R : RecourseLP M N) : Prop :=
  ∃ p : Fin M → ℝ, 0 ≤ p ∧ R.B.transpose.mulVec p = R.d

end AdaptDRO.LiftedLDR


