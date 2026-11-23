-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Supplement_Integral
-- name    : UniformPrecSched_Makespan_Supplement_Integral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:18:54.716713+00:00
-- url     : https://prove2.me/theorems/388b9a81-dd1b-4de1-ad42-156a6033dcad
-- title:
--   Integer relaxation, its attained optimum, and optimal makespan schedules
-- statement:
--   Let $I$ be an instance with positive job requirements and machine speeds and strict precedence, using the published scheduling model. A triple $(x,C,D)$ is integer-feasible when it satisfies every constraint of the published LP and
--
--   $$x_{kj}\in\{0,1\}.$$
--
--   It is integer-optimal when its $D$ is no greater than that of every other integer-feasible triple. An optimal makespan schedule is a feasible nonpreemptive schedule whose makespan is no greater than every other feasible schedule's makespan. Thus $D^*$ is the integer relaxation optimum, rather than the fractional LP optimum.
--
--   These predicates provide attained comparison values for the gap result. They introduce no infimum with an empty-set or unbounded-set default.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), pp. 5–6 (PDF 5–6), (1)–(6); p. 10 (PDF 10), Theorem 3.11

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_LP

namespace UniformPrecSched.Makespan.Supplement

variable {n m : ℕ}

/-- Chudak–Shmoys, authors' manuscript, pp. 5–6, PDF 5–6, (1)–(6).
The integer relaxation retains every published LP constraint and requires binary assignments. -/
def IPFeasible (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) : Prop :=
  LPFeasible I x C D ∧ ∀ k j, x k j = 0 ∨ x k j = 1

/-- The attained integer optimum D*, not the fractional optimum (p. 10, Theorem 3.11). -/
def IPOptimal (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ)
    (C : Fin n → ℝ) (D : ℝ) : Prop :=
  IPFeasible I x C D ∧ ∀ x' C' D', IPFeasible I x' C' D' → D ≤ D'

/-- An actual makespan minimizer; using a witness avoids infimum default values. -/
def IsMakespanOptimal (I : Instance n m) (σ : Schedule I) : Prop :=
  ∀ σ' : Schedule I, σ.makespan ≤ σ'.makespan

end UniformPrecSched.Makespan.Supplement


