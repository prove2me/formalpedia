-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
-- name    : ProcessingNetworks_ProportionalFairness_RestatedCore
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:28:25.609261+00:00
-- url     : https://prove2.me/theorems/aec3b665-8f99-48fd-a3d8-d591d3a772b4
-- title:
--   The PF objective, maximizer predicate, and allocation function ψ (restated from mission IX)
-- statement:
--   Section 10.1's concave optimization problem, restated identically from mission
--   `09-proportional-fairness-core`. Fix a bounded, closed, convex, monotone, nontrivial set
--   $\mathcal A \subset \mathbb R^I_+$ (`IsPFDomain`). For $z \in \mathbb R^I_+$, $f(z,x) := \sum_i z_i \log(x_i)$
--   (Eq. 10.2), with the convention $\log(0) = -\infty$, $0\log(0) = 0$. The **PF allocation
--   function** $\psi(z) := \operatorname{argmax}_{x\in\mathcal A} f(z,x)$ (Eqs. 10.4-10.5).
--   `groupAggregate grp x ℓ` is the group-level aggregate $a_\ell(x) := \sum_{i \in \mathcal
--   I(\ell)} x_i$ (Eq. 10.22) for a demand-group assignment `grp : Fin I → Fin L` encoding the
--   partition $\{\mathcal I(\ell), \ell \in \mathcal L\}$.
--
--   **Formalization note.** This chunk shares the `ProportionalFairness` sub-namespace with
--   mission IX but, per this series' convention, cannot import its draft (unpublished drafts do
--   not import one another); every definition of mission IX's this chunk's proofs need is
--   restated here, matching mission IX's code exactly, for a moderator to reconcile the two chunks
--   into one namespace at upload time. `f` is `EReal`-valued via `extLog` (`Real.log` at `0` is `0`
--   in Mathlib, not `-∞`); `IsPFMaximizer`/`psi` avoid `sSup`/`⨆` entirely, per this series'
--   junk-value-avoidance convention.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 183-184, 191, Section 10.1, Eqs. (10.1),(10.2),(10.4),(10.5); Section 10.3, Eq. (10.22) (restated from mission IX)

import Mathlib

namespace ProcessingNetworks.ProportionalFairness

open Classical

/-- The concave-optimization-problem domain (Section 10.1, before Eq. (10.1)): `A ⊂ ℝ^I_+` is
bounded, closed, convex, monotone (10.1) (downward-closed among nonnegative vectors), and
nontrivial (contains a strictly positive point). Restated identically from mission IX. -/
def IsPFDomain {I : ℕ} (AllocSet : Set (Fin I → ℝ)) : Prop :=
  Bornology.IsBounded AllocSet ∧ IsClosed AllocSet ∧ Convex ℝ AllocSet ∧
    (∀ x ∈ AllocSet, ∀ y : Fin I → ℝ, (∀ i, 0 ≤ y i) → y ≤ x → y ∈ AllocSet) ∧
    ∃ x ∈ AllocSet, ∀ i, 0 < x i

/-- The extended logarithm implementing the book's convention `log(0) = -∞` (Eq. 10.2). Restated
identically from mission IX (`09-proportional-fairness-core`): this chunk shares the
`ProcessingNetworks.ProportionalFairness` sub-namespace with mission IX but cannot import its
draft, so per this series' restate-not-import convention the definitions this chunk needs are
duplicated here, matching mission IX's own code exactly for a moderator to reconcile at upload
time. -/
noncomputable def extLog (x : ℝ) : EReal :=
  if x = 0 then ⊥ else (Real.log x : EReal)

/-- The objective `f(z,x) := ∑_i z_i log(x_i)` (Eq. 10.2), restated identically from mission IX. -/
noncomputable def f {I : ℕ} (z x : Fin I → ℝ) : EReal :=
  ∑ i, (z i : EReal) * extLog (x i)

/-- `x` is a maximizer of `f(z,·)` over `AllocSet`, restated identically from mission IX. -/
def IsPFMaximizer {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (z x : Fin I → ℝ) : Prop :=
  x ∈ AllocSet ∧ ∀ y ∈ AllocSet, f z y ≤ f z x

/-- The PF allocation function `ψ` (Eqs. 10.4-10.5), restated identically from mission IX. -/
noncomputable def psi {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (z : Fin I → ℝ) : Fin I → ℝ :=
  fun i =>
    if 0 < z i then
      (if h : ∃ x, IsPFMaximizer AllocSet z x then (Classical.choose h) i else 0)
    else 0

/-- The group-level aggregate `a_ℓ(x) := ∑_{i ∈ I(ℓ)} x_i` (Eq. 10.22), restated identically from
mission IX, given a demand-group assignment `grp : Fin I → Fin L`. -/
def groupAggregate {I L : ℕ} (grp : Fin I → Fin L) (x : Fin I → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => grp i = ℓ), x i

end ProcessingNetworks.ProportionalFairness


