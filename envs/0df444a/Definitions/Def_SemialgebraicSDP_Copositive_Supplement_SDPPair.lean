-- Prove2me | Definitions.Def_SemialgebraicSDP_Copositive_Supplement_SDPPair
-- name    : SemialgebraicSDP_Copositive_Supplement_SDPPair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:42:55.552807+00:00
-- url     : https://prove2.me/theorems/4607e64f-a839-4c1d-b2bf-7978837a834d
-- title:
--   §3.1 — primal and dual SDP feasibility and strict feasibility
-- statement:
--   For real symmetric matrices $A_i,C$ and real numbers $b_i$, the primal problem (3.1) minimizes $\operatorname{tr}(CX)$ over $X\succeq0$ satisfying $\operatorname{tr}(A_iX)=b_i$. The dual (3.2) maximizes $\sum_i b_i y_i$ subject to
--   $$C-\sum_i y_i A_i\succeq0.$$
--   This module defines those feasible predicates and their strict versions, which require positive definiteness of $X$ or of the dual slack. The trace pairing is exactly $\operatorname{tr}(UV)$. Dimensions and constraint counts are arbitrary finite naturals, including zero. Symmetry of the input data is imposed in the theorem. These predicates provide the setting for the corrected Theorem 3.1.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, pp. 296–297, §3.1 (3.1)–(3.2)

import Mathlib

namespace SemialgebraicSDP.Copositive.Supplement

/-- Trace pairing of §1.1, p. 294. -/
noncomputable def tracePair {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (U * V).trace

/-- Feasibility in (3.1), p. 296. PSD includes symmetry. -/
def PrimalFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.PosSemidef ∧ ∀ i, tracePair (A i) X = b i

/-- Feasibility in (3.2), with the sign C − Σ yᵢAᵢ. -/
def DualFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) : Prop :=
  (C - ∑ i, y i • A i).PosSemidef

/-- Strict primal feasibility: a positive definite feasible matrix. -/
def PrimalStrict {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ) : Prop :=
  ∃ X : Matrix (Fin n) (Fin n) ℝ, X.PosDef ∧ ∀ i, tracePair (A i) X = b i

/-- Strict dual feasibility: positive definite slack. -/
def DualStrict {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ y : Fin m → ℝ, (C - ∑ i, y i • A i).PosDef

end SemialgebraicSDP.Copositive.Supplement


