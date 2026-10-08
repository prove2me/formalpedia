-- Prove2me | Definitions.Def_MatousekLP_DIntervals_SetSystem
-- name    : MatousekLP_DIntervals_SetSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:50:37.935026+00:00
-- url     : https://prove2.me/theorems/44252fe0-fabc-4d0d-854d-cdf17553fbfc
-- title:
--   §8.6 — transversals, matchings, and their fractional versions for a set system
-- statement:
--   Let $V$ be a finite set and $\mathcal F$ a system of subsets of $V$.
--
--   1. A set $X \subseteq V$ is a **transversal** of $\mathcal F$ if $F \cap X \ne \emptyset$ for every $F \in \mathcal F$. The **transversal number** $\tau(\mathcal F)$ is the minimum number of elements of a transversal.
--   2. A **matching** is a subsystem $\mathcal M \subseteq \mathcal F$ in which no two distinct sets intersect. The **matching number** $\nu(\mathcal F)$ is the maximum number of sets in a matching.
--   3. A **fractional transversal** is a feasible solution $x$ of the linear program
--   $$
--   \text{minimize } \sum_{v \in V} x_v \quad\text{subject to}\quad \sum_{v \in F} x_v \ge 1 \ \text{ for every } F \in \mathcal F,\qquad x \ge 0 .
--   $$
--   Its optimal value is the **fractional transversal number** $\tau^*(\mathcal F)$.
--   4. A **fractional matching** is a feasible solution $y = (y_F)_{F \in \mathcal F}$ of the linear program
--   $$
--   \text{maximize } \sum_{F \in \mathcal F} y_F \quad\text{subject to}\quad \sum_{F :\, v \in F} y_F \le 1 \ \text{ for every } v \in V,\qquad y \ge 0 .
--   $$
--   Its optimal value is the **fractional matching number** $\nu^*(\mathcal F)$.
--
--   Transversal and matching numbers are basic parameters of combinatorics; their fractional versions are LP relaxations of them, and the two linear programs are dual to each other.
--
--   **Formalization Note** $V$ is a `Fintype`, $\mathcal F$ a `Finset (Finset V)`. $\tau$ is an `sInf` over $\mathbb N$: when no transversal exists (which happens only if $\emptyset \in \mathcal F$) this returns the junk value $0$, so every statement about $\tau$ assumes the members of $\mathcal F$ nonempty. $\nu$ is the maximum over the finite family of matchings, which always contains $\mathcal M = \emptyset$. A fractional matching is a function on all subsets of $V$ that is nonnegative; only its values on members of $\mathcal F$ enter the constraints and the objective. $\tau^*$ and $\nu^*$ are not introduced as numbers; statements speak of optimal feasible solutions instead.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §8.6, p. 181 (transversal, τ(F), matching, ν(F)), p. 182 (fractional transversal, τ*(F), fractional matching, ν*(F))

import Mathlib

open Finset

namespace MatousekLP.DIntervals

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set `X ⊆ V` is a transversal of the set system `F` if `F ∩ X ≠ ∅` for every `F ∈ F`
(Matoušek–Gärtner, §8.6, p. 181). -/
def IsTransversal (F : Finset (Finset V)) (X : Finset V) : Prop :=
  ∀ S ∈ F, (S ∩ X).Nonempty

/-- The transversal number `τ(F)`: the minimum number of elements of a transversal of `F`
(p. 181). Written as `sInf` over `ℕ`; when no transversal exists (only if `∅ ∈ F`) the set is
empty and the value is the junk `0`, so every statement about `τ` assumes the members of `F`
nonempty, in which case `V` itself is a transversal and the infimum is an attained minimum. -/
noncomputable def transversalNumber (F : Finset (Finset V)) : ℕ :=
  sInf {k | ∃ X : Finset V, IsTransversal F X ∧ X.card = k}

/-- A matching of `F`: a subsystem `M ⊆ F` in which no two distinct sets intersect (p. 181). -/
def IsMatching (F M : Finset (Finset V)) : Prop :=
  M ⊆ F ∧ (M : Set (Finset V)).Pairwise Disjoint

open Classical in
/-- The matching number `ν(F)`: the maximum number of sets in a matching `M ⊆ F` (p. 181),
the supremum of `|M|` over the finite, nonempty (it contains `M = ∅`) family of matchings. -/
noncomputable def matchingNumber (F : Finset (Finset V)) : ℕ :=
  (F.powerset.filter (fun M => IsMatching F M)).sup Finset.card

/-- A fractional transversal of `F` (p. 182): a feasible solution `x ∈ ℝ^V` of the linear
program `min Σ_{v ∈ V} x_v` subject to `Σ_{v ∈ F} x_v ≥ 1` for every `F ∈ F`, `x ≥ 0`. -/
def IsFractionalTransversal (F : Finset (Finset V)) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ S ∈ F, 1 ≤ ∑ v ∈ S, x v

/-- A fractional matching for `F` (p. 182): a feasible solution `y = (y_F)_{F ∈ F}` of the linear
program `max Σ_{F ∈ F} y_F` subject to `Σ_{F : v ∈ F} y_F ≤ 1` for every `v ∈ V`, `y ≥ 0`.
`y` is a function on all finite subsets of `V`; only its values on members of `F` enter the
constraints and the objective. -/
def IsFractionalMatching (F : Finset (Finset V)) (y : Finset V → ℝ) : Prop :=
  (∀ S, 0 ≤ y S) ∧ ∀ v, ∑ S ∈ F.filter (fun S => v ∈ S), y S ≤ 1

end MatousekLP.DIntervals


