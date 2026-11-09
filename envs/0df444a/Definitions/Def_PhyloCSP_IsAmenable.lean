-- Prove2me | Definitions.Def_PhyloCSP_IsAmenable
-- name    : PhyloCSP_IsAmenable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:08.943163+00:00
-- url     : https://prove2.me/theorems/90f6541a-1b24-455a-abeb-21602f0431d4
-- title:
--   Amenable topological groups
-- statement:
--   A topological group $\Gamma$ is **amenable** if, whenever it acts continuously on a nonempty compact Hausdorff space $Y$, there is a Borel probability measure $\mu$ on $Y$ invariant under the action:
--   $$
--   g_*\mu=\mu\qquad\text{for every }g\in\Gamma .
--   $$
--
--   This is the property that lets the paper average a random relation over $\mathrm{Aut}(\mathcal F)$ (Lemma 7.9) even though that group carries no invariant probability measure.
--
--   **Formalization Note** A continuous action is a group action that is jointly continuous; $\mu$ lives on the Borel $\sigma$-algebra. The spaces $Y$ range over the first universe of types. This is not amenability of the underlying discrete group.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 7.3, p.22 (PDF p.24)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-- **Amenable topological groups (Section 7.3).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 7.3, p.22 (PDF p.24): "A topological group Γ is
amenable if, whenever it acts continuously on a nonempty compact Hausdorff space Y, there exists a
Borel probability distribution on Y invariant under this action; see Moore [Moo13, Section 1]."

**Formalization Note.** "Acts continuously" is a group action that is jointly continuous
(`ContinuousSMul`). The Borel σ-algebra is `borel Y`; invariance is `μ.map (g • ·) = μ` for every
`g`. The spaces `Y` range over `Type` (universe 0). This is not invariant-mean amenability of the
underlying discrete group. -/
def IsAmenable (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [Nonempty Y] [MulAction G Y]
    [ContinuousSMul G Y],
    letI : MeasurableSpace Y := borel Y
    ∃ μ : Measure Y, IsProbabilityMeasure μ ∧ ∀ g : G, μ.map (fun y => g • y) = μ

end PhyloCSP


