-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_MaximalStability
-- name    : ProcessingNetworks_ProportionalFairness_MaximalStability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:30:50.845985+00:00
-- url     : https://prove2.me/theorems/dcd2a387-e668-4f15-9b9b-eaaa6c1cd7fc
-- title:
--   The stability region and maximal stability of a control policy (Section 5.7, restated in shape from mission II)
-- statement:
--   Section 5.7's **stability region** $\Lambda^* := \{\lambda : \exists \text{ a stable policy for
--   } \lambda\}$, and a control policy $p$ is **maximally stable** if it is stable for every
--   $\lambda \in \Lambda^*$. A policy is represented abstractly by a value of a type `Policy`, with
--   `PolicyStable p lam` recording that `p` is a stable policy for arrival-rate vector `lam`.
--
--   **Formalization note.** Restated in shape from mission II's (`02-subcriticality`)
--   `Subcriticality.StabilityRegion`/`IsMaximallyStable` — a different sub-namespace, so no name
--   collision, but duplicated here since this chunk's own `BRIEF.md` dependency line does not list
--   mission II, per this series' restate-not-import convention.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 91, Section 5.7 (restated in shape from mission II)

import Mathlib

namespace ProcessingNetworks.ProportionalFairness

/-- The stability region `Λ*` for a family of networks indexed by arrival-rate vector `lam`
(Section 5.7), restated identically in shape from mission II's `Subcriticality.StabilityRegion`
(a different sub-namespace, so no name collision, but restated here rather than cross-imported
since this chunk's own `BRIEF.md` does not list mission II as a dependency). A policy is
represented abstractly by a value of `Policy`, and `PolicyStable p lam` records that `p` is a
stable policy for arrival-rate vector `lam`. -/
def StabilityRegion {I : ℕ} {Policy : Type*} (PolicyStable : Policy → (Fin I → ℝ) → Prop) :
    Set (Fin I → ℝ) :=
  {lam | ∃ p, PolicyStable p lam}

/-- A control policy `p` is maximally stable (Section 5.7) if it is a stable policy for every
`λ` in the stability region `Λ*`, restated identically in shape from mission II's
`Subcriticality.IsMaximallyStable`. -/
def IsMaximallyStable {I : ℕ} {Policy : Type*} (PolicyStable : Policy → (Fin I → ℝ) → Prop)
    (p : Policy) : Prop :=
  ∀ lam ∈ StabilityRegion PolicyStable, PolicyStable p lam

end ProcessingNetworks.ProportionalFairness


