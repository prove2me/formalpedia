-- Prove2me | Definitions.Def_PhyloCSP_IsMixtureOfBasic
-- name    : PhyloCSP_IsMixtureOfBasic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:25:09.676703+00:00
-- url     : https://prove2.me/theorems/61759c8f-7ed5-4b1c-b28d-ffb78380af65
-- title:
--   Finite mixtures of basic transformations
-- statement:
--   Given distributions $\rho_1,\dots,\rho_m$ and nonnegative weights $\lambda_1,\dots,\lambda_m$ summing to $1$, the mixture first chooses $i$ with probability $\lambda_i$ and then samples from $\rho_i$; a mixture of transformations chooses a transformation and applies it to the input tree.
--
--   A tree transformation $G$ **is a mixture of $m$ basic transformations with templates of at most $V$ vertices** if there are weights $\lambda_1,\dots,\lambda_m$ summing to $1$ and basic parameters $(B_i,p_i,\nu_i)$, each $B_i$ with at most $V$ vertices and each $\nu_i$ centrally symmetric, such that on every input $T$
--   $$
--   \Pr(G[T]=R)=\sum_{i=1}^m\lambda_i\,\Pr(\text{basic}_{B_i,p_i,\nu_i}[T]=R)\quad\text{for every relation }R,
--   $$
--   where the left side is $0$ for relations that are not trees. A finite mixture of basic transformations is a $G$ with this property for some $m$ and $V$.
--
--   **Formalization Note** $G$ is pinned exactly: its output law equals the mixture formula. The single-leaf template with all mass on its leaf is the identity transformation, so the property is satisfiable (checked).
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 2, p.7 (PDF p.9), mixtures; Definition 3.3, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_PhyloCSP_basicRawLaw
import Definitions.Def_PhyloCSP_TreeTransformation

set_option autoImplicit false

open scoped ENNReal

namespace PhyloCSP

open Template

/-- **Finite mixtures of basic transformations.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 2, p.7 (PDF p.9): "Let ρ1, . . . , ρm be probability
distributions on the same space, and let λ1, . . . , λm be nonnegative weights that sum to 1. …
We define a mixture of transformations in the same way: first choose a transformation, then apply
it to the input tree." Basic transformations: Definition 3.3, p.8 (PDF p.10).

`IsMixtureOfBasic G m maxV`: there are weights `λ₀, …, λ_{m-1}` summing to `1` and basic
parameters `(Bᵢ, pᵢ, νᵢ)` — a template with at most `maxV` vertices, a location law and a
centrally symmetric orientation law — such that on every input `T` the output law of `G` is
exactly `Σᵢ λᵢ · (law of the i-th basic transformation)`: it equals that mixture on every tree
relation, and the mixture puts no mass on any relation that is not a tree relation.

**Formalization Note.** `G` is pinned exactly, not approximated. A finite mixture of basic
transformations is `∃ m maxV, IsMixtureOfBasic G m maxV`. The orientation laws `νᵢ` are arbitrary
centrally symmetric laws on `{±1}^{E(Bᵢ)}` (coordinates not necessarily independent). -/
def IsMixtureOfBasic (G : TreeTransformation) (m maxV : ℕ) : Prop :=
  ∃ (w : Fin m → ℝ≥0∞) (B : Fin m → Template) (p : ∀ i, PMF (B i).Loc)
    (ν : ∀ i, PMF ((B i).Edge → Bool)),
    ∑ i, w i = 1 ∧ (∀ i, (B i).n ≤ maxV) ∧ (∀ i, IsCentrallySymmetric (ν i)) ∧
    ∀ (S : Finset ℕ) (T : Pattern ↥S) (R : ↥S → ↥S → ↥S → Bool),
      (∑ i, w i * basicRawLaw (B i) (p i) (ν i) T.1 R) =
        if h : IsTreeRel R then G.law S T ⟨R, h⟩ else 0

end PhyloCSP


