-- Prove2me | Definitions.Def_SteurerHDX_IsSimplicialComplex
-- name    : SteurerHDX_IsSimplicialComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:43.070889+00:00
-- url     : https://prove2.me/theorems/37674869-d566-48c8-9e6a-95bb65c65aa6
-- title:
--   Simplicial complex (downward-closed family of finite sets)
-- statement:
--   A **simplicial complex** on a ground set $V$ is a finite collection $\mathcal X$ of finite subsets of $V$ that is downward closed:
--   $$\tau\in\mathcal X,\ \sigma\subseteq\tau\ \Longrightarrow\ \sigma\in\mathcal X .$$
--   Its elements are the **faces**. Every complex considered in the mission is of this form.
--
--   **Formalization Note** A complex is a `Finset (Finset V)`; only the elements of $V$ that occur in faces matter.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.2, p.3

import Mathlib

namespace SteurerHDX

/-- **Simplicial complex.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.2, p.3: "A simplicial complex X on a finite
ground set V is a downward-closed collection of subsets of V, i.e., if τ ∈ X and σ ⊆ τ, then
σ ∈ X."

**Formalization Note.** A complex is a finite collection `X : Finset (Finset V)`; the ground set
is the type `V` (only the elements occurring in faces matter). -/
def IsSimplicialComplex {V : Type*} (X : Finset (Finset V)) : Prop :=
  ∀ τ ∈ X, ∀ σ : Finset V, σ ⊆ τ → σ ∈ X

end SteurerHDX


