-- Prove2me | Definitions.Def_GaloisRep_GlobalUnramifiedAt
-- name    : GaloisRep_GlobalUnramifiedAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/ec7a7681-8067-5114-b53f-d07961424fac
-- title:
--   Unramifiedness at a rational prime for global Galois representations
-- statement:
--   For a field extension $L/K$ and a monoid $G$, this module defines when a monoid homomorphism $\rho \colon (L \simeq_{\mathrm{alg}[K]} L) \to G$ out of the group of $K$-algebra automorphisms of $L$ is unramified at a natural number $q$. The definition [`GlobalGaloisRep.IsUnramifiedAt`](../def/GaloisRep_GlobalUnramifiedAt.html#L9) reads: for every valuation subring $A$ of $L$ satisfying `A.LiesOverPrime q` — that is, with the image of $q$ in $L$ a non-unit of $A$, equivalently $q \in \mathfrak{m}_A$ — the subgroup `A.inertiaSubgroupIn K` is contained in the kernel of $\rho$. Here `A.inertiaSubgroupIn K` is the subgroup of $K$-automorphisms of $L$ obtained as the image of Mathlib's inertia subgroup of $A$ (a subgroup of the decomposition subgroup of $A$ over $K$) under the inclusion of that decomposition subgroup into the whole automorphism group; so its elements are the $K$-automorphisms preserving $A$ and inducing the identity on the residue field of $A$. The condition is thus a universally quantified statement over all places of $L$ above $q$, formulated with valuation subrings of $L$ rather than with completions or with a choice of embedding of a local Galois group.
--
--   The accompanying lemma [`GlobalGaloisRep.isUnramifiedAt_iff`](../def/GaloisRep_GlobalUnramifiedAt.html#L12) restates the definition in pointwise form: $\rho$ is unramified at $q$ if and only if for every valuation subring $A$ of $L$ lying over $q$ and every $\sigma$ in `A.inertiaSubgroupIn K` one has $\rho(\sigma) = 1$. Note that no hypothesis forces $q$ to be prime, nor $L/K$ to be normal or algebraic; these are conditions imposed by the users of the predicate.
--
--   **Relation to Mathlib.** Mathlib provides the decomposition and inertia subgroups of a valuation subring; the project adds [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21), the image of the inertia subgroup inside the full group of $K$-algebra automorphisms, and the predicates [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and [`GlobalGaloisRep.IsUnramifiedAt`](../def/GaloisRep_GlobalUnramifiedAt.html#L9), which Mathlib does not have. Galois representations here are bare `MonoidHom`s out of $L \simeq_{\mathrm{alg}[K]} L$, with no bundled representation type.
--
--   **Where it is used.** This is the language in which ramification hypotheses on global mod-$p$ representations are stated in the project, in particular the assertion that the mod-$p$ representation attached to the Frey curve is unramified outside $2p$, which is an input to level lowering. A parallel predicate for the $n$-torsion of a Weierstrass curve, [`WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt`](../def/FLTPrelim_Ramification.html#L35), and its specialisation [`FreyPackage.GaloisRepUnramifiedAt`](../def/FLTPrelim_Ramification.html#L46) to the Frey curve over $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, are defined in the imported ramification module in the same style.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_GlobalUnramifiedAt.lean

import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace GlobalGaloisRep

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsUnramifiedAt {G : Type*} [Monoid G] (ρ : (L ≃ₐ[K] L) →* G) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring L, A.LiesOverPrime q → A.inertiaSubgroupIn K ≤ ρ.ker

lemma isUnramifiedAt_iff {G : Type*} [Monoid G] {ρ : (L ≃ₐ[K] L) →* G} {q : ℕ} :
    IsUnramifiedAt ρ q ↔
      ∀ A : ValuationSubring L, A.LiesOverPrime q →
        ∀ σ : L ≃ₐ[K] L, σ ∈ A.inertiaSubgroupIn K → ρ σ = 1 :=
  Iff.rfl

end GlobalGaloisRep


