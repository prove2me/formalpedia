-- Prove2me | Definitions.Def_ReplicableDecisions_profileValues
-- name    : ReplicableDecisions_profileValues
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:12.423725+00:00
-- url     : https://prove2.me/theorems/6b292b35-9e31-4f8b-8a4f-0ecb2b6908a1
-- title:
--   Value sets of the selector profiles $\Phi$, $\Psi$, $\Lambda$
-- statement:
--   For a law $\mu$ on selectors, common to all models, the objective is $\max_{P\in\mathcal P}\Pr_{f\sim\mu}[P\in B(f)]$ for a selector-indexed set $B(f)$. The three profiles are
--
--   $$
--   \Phi(G)=\min_\mu\max_{P}\Pr_{f\sim\mu}[P\in B_G(f)],
--   $$
--
--   $\Psi(G)$, which minimizes $\max_P\Pr[P\in\partial_Gf]$ over laws supported on everywhere-correct selectors, and $\Lambda(G)$, the same objective over laws supported on neighborhood-correct selectors, with $\Lambda(G)=+\infty$ if none exists.
--
--   These are linear programs over the finitely many selectors, and they measure how often a shared random labeling must fail at its worst model.
--
--   **Formalization Note** `phiValues`, `psiValues` and `lambdaValues` are the sets of objective values at feasible laws. A statement about a profile is an `IsLeast` over its set, so attainment is part of it. An empty `lambdaValues` is the paper's $\Lambda(G)=+\infty$.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2 "Selectors", p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment
import Definitions.Def_ReplicableDecisions_boundary

namespace ReplicableDecisions

/-- **The objective of the selector programs,** `max_{P∈P} Pr_{f∼µ}[P ∈ B(f)]`, for one law `µ` on
selectors common to all models. Chen, *Replicable Decisions in Finite Experiments*, STOC 2027
submission (sha256 52d181db…), §2, p.9 (PDF p.11).

**Formalization Note.** A law on the finitely many selectors is a point of `stdSimplex ℝ (ι → Y)`.
The supremum over the finite nonempty `ι` is the printed maximum. -/
noncomputable def worstCase {ι : Type*} {Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    (μ : (ι → Y) → ℝ) (B : (ι → Y) → Set ι) : ℝ :=
  ⨆ i, finProb μ {f | i ∈ B f}

/-- **Values of a selector program:** the objective at each selector law supported on `Adm`. Chen,
STOC 2027 submission (sha256 52d181db…), §2, p.9 (PDF p.11).

**Formalization Note.** The profiles are read through `IsLeast` of these sets, so every asserted
value is an attained minimum (the page: "All finite minima are attained"), and an empty set is the
page's `Λ(G) = +∞`. -/
def profileValues {ι : Type*} {Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    (Adm : (ι → Y) → Prop) (B : (ι → Y) → Set ι) : Set ℝ :=
  {v | ∃ μ ∈ stdSimplex ℝ (ι → Y), (∀ f, μ f ≠ 0 → Adm f) ∧ v = worstCase μ B}

/-- **Values of the joint profile** `Φ(G) = min_µ max_P Pr_{f∼µ}[P ∈ B_G(f)]`. Chen, STOC 2027
submission (sha256 52d181db…), §2, p.9 (PDF p.11). -/
def phiValues {ι : Type*} {Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    (G : SimpleGraph ι) (Γ : ι → Set Y) : Set ℝ :=
  profileValues (fun _ => True) (badSet G Γ)

/-- **Values of `Ψ(G)`:** `max_P Pr[P ∈ ∂_G f]` over laws supported on everywhere-correct selectors.
Chen, STOC 2027 submission (sha256 52d181db…), §2, p.9 (PDF p.11). -/
def psiValues {ι : Type*} {Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    (G : SimpleGraph ι) (Γ : ι → Set Y) : Set ℝ :=
  profileValues (EverywhereCorrect Γ) (boundary G)

/-- **Values of `Λ(G)`:** the same objective over laws supported on neighborhood-correct selectors,
(2.1). Chen, STOC 2027 submission (sha256 52d181db…), §2, p.9 (PDF p.11). -/
def lambdaValues {ι : Type*} {Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    (G : SimpleGraph ι) (Γ : ι → Set Y) : Set ℝ :=
  profileValues (NeighborhoodCorrect G Γ) (boundary G)

end ReplicableDecisions


