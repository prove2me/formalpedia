-- Prove2me | Definitions.Def_ProcessingNetworks_TaskAllocation_TaskAllocationModel
-- name    : ProcessingNetworks_TaskAllocation_TaskAllocationModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:38:48.428137+00:00
-- url     : https://prove2.me/theorems/14e7e340-b055-4c6f-b6fd-b47373ee8865
-- title:
--   The task allocation model data and general subcriticality (Sections 11.2-11.3, Eq. 11.6)
-- statement:
--   **Sections 11.2-11.3.** A task allocation model has `L` task categories and `K` servers; a
--   class is a pair $(\ell,k)$ (a category assigned to a server), and $m_{\ell k} > 0$ (Eq. 11.3)
--   is the mean service time for class $(\ell,k)$. External arrivals follow a Markovian arrival
--   process (MArP) with long-run average rate vector $\nu \ge 0$ (Section 11.4).
--
--   **General subcriticality (Eq. 11.6, last paragraph of Section 5.2).** The model is
--   subcritical if there exist $\lambda \ge 0$ with $G\lambda = \nu$ and $x \ge 0$ with $Rx =
--   \lambda$ and $Ax < b$, for this model's own source-buffer matrix $G$, input-output matrix
--   $R = M^{-1}$, capacity-consumption matrix $A$, and capacities $b=\mathbf 1$ (Eq. 11.1) — the
--   matrices Lemma 11.2's proof derives explicitly for this model.
--
--   **Formalization note.** Classes are represented directly as pairs `(ℓ,k) : Fin L × Fin K`
--   rather than flattened to a single `Fin I` with `I = LK`, avoiding an arbitrary choice of
--   bijection. `IsSubcriticalGeneral` substitutes `R = M⁻¹` directly (`x ℓ k = m ℓ k * lam ℓ k`)
--   rather than restating mission II's fully general SPN subcriticality machinery, which this
--   chunk's own `BRIEF.md` does not list as a dependency to import.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 209-215, Sections 11.2-11.4, Eqs. (11.1),(11.3),(11.6)

import Mathlib

namespace ProcessingNetworks.TaskAllocation

/-- The task allocation model's data (Sections 11.2-11.3): `L` categories, `K` servers, mean
service times `m ℓ k` for a class-`(ℓ,k)` task (Eq. 11.3, all strictly positive), and the
Markovian-arrival-process long-run average arrival rate vector `ν` (Section 11.4, `ν ≥ 0`). Class
`(ℓ,k)` is represented directly as the pair `(ℓ,k) : Fin L × Fin K` throughout this mission,
rather than flattened to a single `Fin I` with `I = LK` (Section 11.3): the two representations
are in bijection, and using the pair directly avoids an arbitrary encoding of the bijection. -/
structure TaskAllocationData (L K : ℕ) where
  m : Fin L → Fin K → ℝ
  hm : ∀ ℓ k, 0 < m ℓ k
  nu : Fin L → ℝ
  hnu : ∀ ℓ, 0 ≤ nu ℓ

/-- The task allocation model is subcritical (last paragraph of Section 5.2, restated locally per
this chunk's own `BRIEF.md`: mission II's general SPN subcriticality is not imported), in the
general form (11.6) that Lemma 11.2's proof derives for this model's own source-buffer matrix `G`
(`Gℓ,(ℓ,k) = 1`), input-output matrix `R = M⁻¹` (since `Γ = 0`, `B = I`), capacity-consumption
matrix `A` (`Ak,(ℓ,k) = 1`), and capacities `b = 1` (Eq. 11.1): there exist `λ ≥ 0` with `Gλ = ν`
and `x ≥ 0` with `Rx = λ` (i.e. `x = Mλ`, substituted directly here) and `Ax < b`. -/
def IsSubcriticalGeneral {L K : ℕ} (dat : TaskAllocationData L K) : Prop :=
  ∃ (lam x : Fin L → Fin K → ℝ),
    (∀ ℓ k, 0 ≤ lam ℓ k) ∧ (∀ ℓ k, 0 ≤ x ℓ k) ∧
    (∀ ℓ, ∑ k, lam ℓ k = dat.nu ℓ) ∧
    (∀ ℓ k, x ℓ k = dat.m ℓ k * lam ℓ k) ∧
    (∀ k, ∑ ℓ, x ℓ k < 1)

end ProcessingNetworks.TaskAllocation


