-- Prove2me | Definitions.Def_ProcessingNetworks_FluidEquations_SatisfiesAssumption76
-- name    : ProcessingNetworks_FluidEquations_SatisfiesAssumption76
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:47:11.503732+00:00
-- url     : https://prove2.me/theorems/1421c262-ac04-4d44-ab84-3f5e50592929
-- title:
--   Assumption 7.6 — continuity away from 0 and homogeneity of degree 0
-- statement:
--   **Assumption 7.6.** The relaxed-control policy function $h : \mathbb{R}^I_+ \to
--   \mathbb{R}^I_+$ of (7.18) is continuous away from $0$: for each class $i$ and each $z \in
--   \mathbb{R}^I_+$ with $z_i > 0$, $h_i(\cdot)$ is continuous at $z$. Moreover, $h$ is
--   **homogeneous of degree zero**: $h(cz) = h(z)$ for all $c > 0$, $z \in \mathbb{R}^I_+$ (7.20)
--   — together with (7.18), this says the service-rate vector $\beta = h(\hat z)$ depends on the
--   updated job-count vector $\hat z$ only through the relative magnitudes of its components.
--
--   **Formalization note.** Continuity is stated component-wise (`ContinuousAt (fun w => h w i)
--   z`, only for the component $i$ whose coordinate $z_i$ is positive), matching the book's own
--   per-component phrasing exactly rather than the (subtly different, and not what the book
--   states) requirement that all of $h$ be continuous at every point with some positive
--   coordinate.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 132, Assumption 7.6

import Mathlib

namespace ProcessingNetworks.FluidEquations

/-- Assumption 7.6, Dai & Harrison p. 132 (PDF p. 148): the relaxed-control policy function
`h : ℝ^I_+ → ℝ^I_+` of (7.18) is continuous away from `0` — for each class `i` and each
`z ∈ ℝ^I_+` with `z i > 0`, the `i`-th component `h_i(·)` is continuous at `z` — and homogeneous
of degree `0`: `h(cz) = h(z)` for every `c > 0` and `z ∈ ℝ^I_+` (Eq. (7.20)). -/
def SatisfiesAssumption76 {I : ℕ} (h : (Fin I → ℝ) → (Fin I → ℝ)) : Prop :=
  (∀ (i : Fin I) (z : Fin I → ℝ), (∀ j, 0 ≤ z j) → 0 < z i → ContinuousAt (fun w => h w i) z) ∧
  (∀ (c : ℝ) (z : Fin I → ℝ), 0 < c → (∀ j, 0 ≤ z j) → h (c • z) = h z)

end ProcessingNetworks.FluidEquations


