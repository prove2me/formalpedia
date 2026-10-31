-- Prove2me | Definitions.Def_CondDRO_FinitePartition
-- name    : CondDRO_FinitePartition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:15.379992+00:00
-- url     : https://prove2.me/theorems/e6e2d80a-7590-4f4e-992d-553b27ec68c9
-- title:
--   Finite partition $\{\varpi_i\}_{i\in\mathcal I}$ of a measurable space into nonempty measurable atoms
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space and $\mathcal I$ an index set. A family of sets $\{\varpi_i\}_{i\in\mathcal I}$ is a **partition** of $\Omega$ if
--
--   1. each $\varpi_i$ belongs to $\mathcal F$ (is measurable),
--   2. each $\varpi_i$ is nonempty,
--   3. $\varpi_i\cap\varpi_j=\emptyset$ for $i\neq j$, and
--   4. $\Omega=\bigcup_{i\in\mathcal I}\varpi_i$.
--
--   The partition is **finite** if $\mathcal I$ is finite. A finite partition generates a finite sigma subalgebra $\mathcal G\subseteq\mathcal F$ whose atoms (elementary events) are the sets $\varpi_i$; a variable is $\mathcal G$-measurable exactly when it is constant on every $\varpi_i$.
--
--   This is the object on which both conditional functionals of Shapiro and Pichler are defined: the conditional distributionally robust functional $\mathcal R^\star_{|\mathcal G}$ (2.6) and the conditional risk measure $\mathcal R_{|\mathcal G}$ (2.7) take one value per atom $\varpi_i$.
--
--   **Formalization Note** The structure records the cells $\varpi_i$ and the four conditions above. Finiteness of $\mathcal I$ is not part of the structure: every statement that uses a finite partition assumes a `Fintype` instance on the index type.
-- source:
--   Shapiro & Pichler, Conditional Distributionally Robust Functionals, preprint (October 9, 2022), §1, p.3 (definition of a partition) and §2, p.4 ("Finite sigma subalgebra")

import Mathlib

namespace CondDRO

/-- **A partition of a measurable space** `Ω` indexed by `I` (Shapiro & Pichler, *Conditional
Distributionally Robust Functionals*, preprint (October 9, 2022), §1, p.3: "A family of sets
{ϖᵢ}_{i∈ℐ} is a partition of Ω if each ϖᵢ ∈ ℱ is nonempty such that Ω = ∪_{i∈ℐ} ϖᵢ and
ϖᵢ ∩ ϖⱼ = ∅ for i ≠ j ∈ ℐ"). The cells `cell i` are the atoms ϖᵢ of the finite sigma
subalgebra 𝒢 they generate (p.4).

**Formalization Note.** The paper's partition is *finite* when the index set ℐ is finite; this is
imposed by the instance `[Fintype I]` in every statement that uses a finite partition, not inside
the structure. -/
structure FinitePartition (Ω : Type*) [MeasurableSpace Ω] (I : Type*) where
  /-- The cell ϖᵢ. -/
  cell : I → Set Ω
  /-- Each cell belongs to the sigma algebra ℱ. -/
  measurableSet_cell : ∀ i, MeasurableSet (cell i)
  /-- Each cell is nonempty. -/
  nonempty_cell : ∀ i, (cell i).Nonempty
  /-- Distinct cells are disjoint. -/
  pairwise_disjoint : Pairwise (Function.onFun Disjoint cell)
  /-- The cells cover Ω. -/
  iUnion_cell : ⋃ i, cell i = Set.univ

end CondDRO


