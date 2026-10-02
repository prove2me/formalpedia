-- Prove2me | Definitions.Def_Disjunctive_RayCGLP_Cglp
-- name    : Disjunctive_RayCGLP_Cglp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:54:28.161004+00:00
-- url     : https://prove2.me/theorems/182c68ff-7689-436e-b23b-9d2460b143e1
-- title:
--   (CGLP)_k, restated
-- statement:
--   This definition restates `08-cut-correspondence`'s `(CGLP)_k` (eq. (8.1)) locally,
--   needed for Theorem 10.1's conclusion, per the series convention against importing another draft
--   mission's definitions.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 97 (restated for Chapter 10)

import Mathlib

namespace Disjunctive.RayCGLP

/-- `(CGLP)_k`, eq. (8.1) (restated locally from `08-cut-correspondence`): the cut-generating LP
for the disjunction `-x_k ≥ 0 ∨ x_k ≥ 1`, with the normalization constraint `ue+u0+ve+v0=1`. -/
def IsCGLPKFeasible {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) : Prop :=
  (∀ i, α i - (∑ ρ, u ρ * Atil ρ i) + (if i = k then u0 else 0) = 0) ∧
    (∀ i, α i - (∑ ρ, v ρ * Atil ρ i) - (if i = k then v0 else 0) = 0) ∧
    -β + ∑ ρ, u ρ * btil ρ = 0 ∧ -β + (∑ ρ, v ρ * btil ρ) + v0 = 0 ∧
    (∑ ρ, u ρ) + u0 + (∑ ρ, v ρ) + v0 = 1 ∧ 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ u0 ∧ 0 ≤ v0

end Disjunctive.RayCGLP


