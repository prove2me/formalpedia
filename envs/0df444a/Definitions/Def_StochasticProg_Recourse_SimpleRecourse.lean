-- Prove2me | Definitions.Def_StochasticProg_Recourse_SimpleRecourse
-- name    : StochasticProg_Recourse_SimpleRecourse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:46:29.750367+00:00
-- url     : https://prove2.me/theorems/bb6f0574-d2e0-4254-bfe1-172681d802c2
-- title:
--   Simple-recourse first-stage data
-- statement:
--   A **simple-recourse instance** packages the first-stage data $A, b, c$, the technology matrix $T
--   \in \mathbb{R}^{m_2 \times n_1}$, and the split recourse costs $q^+, q^- \in \mathbb{R}^{m_2}$
--   of a simple-recourse problem, where the recourse matrix itself is fixed to $W = [I,-I]$ (Birge &
--   Louveaux, p. 113) and so plays no further role once $q^+, q^-$ are separated. $q_i := q_i^+ +
--   q_i^-$ (p. 114) and $K_1 = \{x \mid Ax=b,\ x\ge 0\}$ are recorded alongside it.
--
--   **Formalization Note.** This is a separate, lighter structure from
--   `StochasticProg.Recourse.Instance`, used only for Corollary 10; it does not re-derive the
--   simple-recourse specialisation from the general instance's $W, q, h$ fields.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 113-114, Chapter 3, Section 3.1d

import Mathlib

namespace StochasticProg.Recourse

/-- First-stage data for a simple-recourse instance, `W = [I,-I]` (p. 113): the
recourse matrix itself plays no further role once `q⁺, q⁻` are separated, so only
the first-stage data and the split cost vectors are kept. -/
structure SimpleRecourseInstance (n1 m1 m2 : ℕ) where
  A : Matrix (Fin m1) (Fin n1) ℝ
  b : Fin m1 → ℝ
  c : Fin n1 → ℝ
  T : Matrix (Fin m2) (Fin n1) ℝ
  qplus : Fin m2 → ℝ
  qminus : Fin m2 → ℝ

variable {n1 m1 m2 : ℕ}

/-- `q_i = q⁺_i + q⁻_i` (p. 114). -/
def SimpleRecourseInstance.qsum (inst : SimpleRecourseInstance n1 m1 m2) (i : Fin m2) : ℝ :=
  inst.qplus i + inst.qminus i

/-- `K1 = {x | Ax = b, x ≥ 0}` (p. 105), as in the general instance. -/
def SimpleRecourseInstance.K1 (inst : SimpleRecourseInstance n1 m1 m2) : Set (Fin n1 → ℝ) :=
  {x | Matrix.mulVec inst.A x = inst.b ∧ ∀ j, 0 ≤ x j}

end StochasticProg.Recourse


