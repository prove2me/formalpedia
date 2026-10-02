-- Prove2me | Definitions.Def_AoP_PropertiesQuantities
-- name    : AoP_PropertiesQuantities
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:18:34.112838+00:00
-- url     : https://prove2.me/theorems/092a5b2c-155f-4fe9-90c1-94c2ac5c25a3
-- title:
--   Assumptions of Physics II.3: full characterization, natural orders, sparse/dense/complete orders
-- statement:
--   Definitions for Part II, Chapter 3 of *Assumptions of Physics* (Carcassi–Aidala, v3.0).
--
--   **Full characterization by a property (Definitions 3.1, 3.3).** A property is a continuous map $q:U\to Q$ from a verifiable set of possibilities to a topological space; the domain is *fully characterized* by it when $q:X\to Q$ is a homeomorphism. Only full characterization is used by the chapter's theorems, so it is defined directly as the existence of a homeomorphism $X\simeq Q$.
--
--   **Quantities (Definitions 3.4–3.6).** A quantity is a property whose value space is linearly ordered and carries the order topology; in Lean this is a type with `LinearOrder`, `TopologicalSpace` and `OrderTopology` instances.
--
--   **Natural order (Definition 3.7).** A linear order on $X$ whose order topology is the natural topology.
--
--   **Before-statements (Definition 3.12).** $\text{“}x<x_1\text{”}=\bigvee_{x<x_1}x$.
--
--   **Sparse, dense, dense subset, complete (Definitions 3.39–3.40, 3.47, 3.49, 3.50).** As in the book: every chain between two elements is finite; between any two elements $a<b$ there is an infinite chain; a subset meeting every $[q_1,q_2]$ with $q_1<q_2$; every non-empty bounded subset has a supremum (bounded above suffices and is used).
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Definitions 3.1–3.8, 3.12, 3.39, 3.40, 3.47, 3.49, 3.50

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

/-!
# Assumptions of Physics, Part II, Chapter 3: properties and quantities

Source: G. Carcassi, C. A. Aidala, *Assumptions of Physics*, Ver. 3.0 (December 31, 2025),
Part II, Chapter 3 "Properties and quantities", Sections 3.1, 3.2, 3.4, 3.5.

Builds on the Chapter 1 definitions (`Def_AoP_ExperimentalDomains`): the possibilities
`D.Possibility` of an experimental domain carry the natural topology.
-/

namespace AssumptionsOfPhysics

universe u v

/-- Definition 3.40 (with Definition 3.39): a (pre)ordered set is sparse if every chain between
two elements is finite, i.e. every closed interval `[a, b]` is finite. -/
def IsSparseOrder (Q : Type v) [Preorder Q] : Prop :=
  ∀ a b : Q, (Set.Icc a b).Finite

/-- Definition 3.47: an ordered set is dense if between any two elements `a < b` there is an
infinite chain, i.e. the interval `[a, b]` is infinite. -/
def IsDenseOrder (Q : Type v) [Preorder Q] : Prop :=
  ∀ a b : Q, a < b → (Set.Icc a b).Infinite

/-- Definition 3.49: `A ⊆ Q` is dense in `Q` if for all `q₁ < q₂` there is `q ∈ A` with
`q₁ ≤ q ≤ q₂`. -/
def IsDenseSubset {Q : Type v} [Preorder Q] (A : Set Q) : Prop :=
  ∀ q₁ q₂ : Q, q₁ < q₂ → ∃ q ∈ A, q₁ ≤ q ∧ q ≤ q₂

/-- Definition 3.50: a linearly ordered set is complete if every non-empty subset that is
bounded (above) has a supremum (a least upper bound). -/
def IsCompleteOrder (Q : Type v) [Preorder Q] : Prop :=
  ∀ A : Set Q, A.Nonempty → BddAbove A → ∃ s, IsLUB A s

namespace ExperimentalDomain

variable {Ω : Type u} (D : ExperimentalDomain Ω)

/-- Definition 3.3: an experimental domain is fully characterized by a property with values in
the topological space `Q` if there is a homeomorphism `q : X → Q` from the possibilities
(with the natural topology) to `Q`. -/
def IsFullyCharacterizedBy (Q : Type v) [TopologicalSpace Q] : Prop :=
  Nonempty (D.Possibility ≃ₜ Q)

/-- Definition 3.7: a linear order on the possibilities is a natural order if the order
topology it generates coincides with the natural topology. -/
def IsNaturalOrder (r : LinearOrder D.Possibility) : Prop :=
  letI := r
  Preorder.topology D.Possibility = D.naturalTopology

/-- Definition 3.12: for a linear order on the possibilities, the statement "`x < x₁`", i.e.
the disjunction of all possibilities strictly before `x₁`. -/
def beforeStmt (r : LinearOrder D.Possibility) (x₁ : D.Possibility) : Set Ω :=
  letI := r
  ⋃ x ∈ {x : D.Possibility | x < x₁}, x.val

end ExperimentalDomain

end AssumptionsOfPhysics


