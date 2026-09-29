-- Prove2me | Definitions.Def_gribov_gauge_fixing
-- name    : gribov_gauge_fixing
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T14:13:47.227679+00:00
-- url     : https://prove2.me/theorems/5bb24768-f438-43b2-a78a-a48997db3c69
-- title:
--   Gauge fixing, principal actions and weak contractibility
-- statement:
--   For a group $G$ acting on a topological space $A$: the orbit space $A/G$ with the quotient topology; a *gauge fixing*, i.e. a continuous section $s : A/G \to A$ of the projection, which is a continuous choice of exactly one point on each orbit; the property of being a *principal $G$-space*, namely that the action is free and that the division map sending a pair of points of one orbit to a group element carrying the second to the first can be chosen continuously; and *weak contractibility*, namely that $A$ is nonempty and all its homotopy groups $\pi_j(A,a)$ are trivial.
-- source:
--   I. M. Singer, Some Remarks on the Gribov Ambiguity, Commun. Math. Phys. 60 (1978) 7-12, https://doi.org/10.1007/BF01609471, pp. 7-9, Sect. 1 (the map s with p o s = I) and Sect. 2 (Theorems 1-2)

import Mathlib

/-!
# Gauge fixing for a group action

Setting for I. M. Singer, *Some Remarks on the Gribov Ambiguity*,
Commun. Math. Phys. **60** (1978), 7–12.
-/

namespace Gribov

open scoped Topology

/-- The orbit space `A / G` of a group action, with the quotient topology. -/
abbrev OrbitSpace (G A : Type) [Group G] [MulAction G A] : Type :=
  Quotient (MulAction.orbitRel G A)

/-- A *gauge fixing* for the action of `G` on `A`: a continuous choice of exactly one point on
each orbit, i.e. a continuous section of the projection `A → A / G`. -/
def IsGaugeFixing (G A : Type) [Group G] [TopologicalSpace A] [MulAction G A]
    (s : OrbitSpace G A → A) : Prop :=
  Continuous s ∧ ∀ q : OrbitSpace G A, (Quotient.mk (MulAction.orbitRel G A) (s q)) = q

/-- `A` is a *principal `G`-space*: the action is free, and the division map — sending a pair of
points lying on a common orbit to a group element carrying the second to the first — can be chosen
continuously. This is the topological content of "`A → A / G` is a principal `G`-bundle". -/
def IsPrincipalAction (G A : Type) [Group G] [TopologicalSpace G] [TopologicalSpace A]
    [MulAction G A] : Prop :=
  (∀ (g : G) (a : A), g • a = a → g = 1) ∧
    ∃ d : {p : A × A // ∃ g : G, g • p.2 = p.1} → G,
      Continuous d ∧ ∀ p : {p : A × A // ∃ g : G, g • p.2 = p.1}, (d p) • p.1.2 = p.1.1

/-- `A` is weakly contractible: it is nonempty and all its homotopy groups vanish. -/
def IsWeaklyContractible (A : Type) [TopologicalSpace A] : Prop :=
  Nonempty A ∧ ∀ (j : ℕ) (a : A), Subsingleton (π_ j A a)

end Gribov


