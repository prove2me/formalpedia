-- Prove2me | Definitions.Def_BlockBochner_L20
-- name    : BlockBochner_L20
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:00.11833+00:00
-- url     : https://prove2.me/theorems/ae368449-f3e6-4481-869c-268d8a631dc3
-- title:
--   $L^2_0(\nu)$, mean-zero functions
-- statement:
--   For a probability measure $\nu$, $L^2_0(\nu)=\{f\in L^2(\nu):E_\nu f=0\}$.
--
--   **Formalization Note** The orthogonal complement of the constants (the functions measurable for the trivial $\sigma$-algebra); since $\langle f,1\rangle=E_\nu f$ this is the mean-zero subspace. The module records that it is complete.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.16

import Mathlib

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **`L²₀(ν)`, the mean-zero functions in `L²(ν)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.16: "Writing `L²₀(ν)` for the
subspace of functions that have zero mean w.r.t. ν".

**Formalization Note** The orthogonal complement in `L²(ν)` of the (classes of) functions measurable
for the trivial σ-algebra, i.e. of the constants; for a probability measure `⟨f, 1⟩ = E_ν f`, so this
is exactly the mean-zero subspace. -/
noncomputable def L20 (ν : Measure (∀ i, X i)) : Submodule ℝ (Lp ℝ 2 ν) :=
  (lpMeas ℝ ℝ ⊥ 2 ν)ᗮ

/-- `L²₀(ν)` is closed, hence complete. -/
instance instCompleteSpaceL20 (ν : Measure (∀ i, X i)) : CompleteSpace (L20 ν) :=
  inferInstanceAs (CompleteSpace ((lpMeas ℝ ℝ ⊥ 2 ν)ᗮ))

end BlockBochner


