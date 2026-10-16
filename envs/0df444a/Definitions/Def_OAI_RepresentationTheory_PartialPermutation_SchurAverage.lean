-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
-- name    : OAI_RepresentationTheory_PartialPermutation_SchurAverage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:51:42.134193+00:00
-- url     : https://prove2.me/theorems/cde25488-fd9c-4782-afec-a04721e61fa5
-- title:
--   Group average of an operator conjugated by a representation
-- statement:
--   Let $G$ be a finite group, let $V$ be a finite-dimensional complex vector space, and let $\rho\colon G\to\mathrm{GL}(V)$ be a complex representation of $G$ on $V$. For a linear operator $A\in\operatorname{End}_{\mathbb{C}}(V)$, the **conjugate average** of $A$ with respect to $\rho$ is the operator
--
--   $$
--   \mathcal{E}_\rho(A)\;=\;\frac{1}{|G|}\sum_{g\in G}\rho(g)\,A\,\rho(g^{-1})\;\in\;\operatorname{End}_{\mathbb{C}}(V).
--   $$
--
--   The map $A\mapsto\mathcal{E}_\rho(A)$ is the averaging (Reynolds) operator onto the $G$-equivariant endomorphisms of $V$: the operator $\mathcal{E}_\rho(A)$ commutes with every $\rho(h)$, operators that already commute with $\rho$ are left unchanged, and the trace is preserved. When $\rho$ is irreducible, Schur's lemma therefore identifies $\mathcal{E}_\rho(A)$ with the scalar operator $\frac{\operatorname{tr}A}{\dim V}\,I_V$; this is the standard device for computing traces and norms of operators built from an irreducible representation.
--
--   **Formalization Note** The operator is `conjugateAverage ρ A`, and the factor $1/|G|$ is the inverse of the cardinality of $G$ cast to $\mathbb{C}$. The definition sits in a section that assumes $V$ finite-dimensional and $\rho$ irreducible (`Representation.IsIrreducible`); the formula itself makes sense for any representation of a finite group.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SchurAverage.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SchurAverage.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation

namespace OAI

section

open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra

namespace PartialPermutation

section SchurAverage
variable {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

noncomputable def conjugateAverage (A : Module.End ℂ V) : Module.End ℂ V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g * A * ρ g⁻¹

end SchurAverage
end PartialPermutation

end

end OAI


