-- Prove2me | Definitions.Def_ModularCurve_ResidualRealization
-- name    : ModularCurve_ResidualRealization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/e2cd9420-da53-55d9-8b94-88ab082b5377
-- title:
--   Residual two-dimensional realizations and the Frobenius determinant condition
-- statement:
--   Two predicates are defined, both relative to a fixed extension of fields $K \subseteq L$ (so that $L \simeq_{\mathrm{alg}[K]} L$ plays the role of the Galois group), a natural number $p$, and an abelian group $J$ carrying a module structure over the project's abstract Hecke algebra `HeckeAlg` (the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$) together with a distributive action of $L \simeq_{\mathrm{alg}[K]} L$.
--
--   `IsResidualRealization p J k φ V π ρ` is a structure whose fields record that the data consisting of a $k$-vector space $V$, a bare function $\pi : J \to V$ and a monoid homomorphism $\rho$ from the Galois group to $\mathrm{GL}_k(V)$ realise the $p$-torsion of $J$, through the ring homomorphism $\varphi : \mathtt{HeckeAlg} \to k$, as a two-dimensional representation. The fields assert: $V$ is finite over $k$ and $\operatorname{finrank}_k V = 2$; $\pi(0) = 0$; $\pi$ is additive on the $p$-torsion, i.e. $\pi(x+y) = \pi(x) + \pi(y)$ whenever $p \cdot x = p \cdot y = 0$; $\pi(\sigma \cdot x) = \rho(\sigma)(\pi x)$ for $p \cdot x = 0$; $\pi(t \cdot x) = \varphi(t)\,\pi(x)$ for $t \in \mathtt{HeckeAlg}$ and $p \cdot x = 0$; and the image $\pi(\{x : p\cdot x = 0\})$ spans $V$ over $k$. Thus all compatibilities are imposed only on the subgroup $J[p]$, and $\pi$ is required to be spanning rather than injective: no isomorphism between $V$ and a subquotient of $J[p]$ is asserted, and $\rho$ is supplied as part of the data rather than constructed.
--
--   `CyclotomicDeterminant N p ρ` asserts, for every prime $\ell \nmid Np$, every valuation subring $A$ of $L$ with $\ell$ in its maximal ideal (`LiesOverPrime`), and every $\sigma$ acting on the residue field of $A$ as $x \mapsto x^\ell$ within the decomposition subgroup (`IsFrobeniusAt`), that $\det \rho(\sigma) = \ell$ in $k$. This is a condition at Frobenius elements only, stated through chosen valuation subrings rather than via a cyclotomic character.
--
--   **Relation to Mathlib.** Mathlib has no notion of a residual realization; both predicates are the project's own. They are built on Mathlib's `ValuationSubring`, ramification subgroups, `Module.finrank` and `LinearMap.det`, together with the project's `HeckeAlg`, [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51).
--
--   **Where it is used.** These predicates package the output of Eichler–Shimura theory in the form used later: from the $p$-torsion of a Jacobian with its Hecke and Galois actions one extracts a two-dimensional mod-$p$ representation attached to a system of Hecke eigenvalues, whose determinant at Frobenius is the cyclotomic one. They are the building blocks of the per-eigenform supply of residual representations used in the modularity and level-lowering steps of the Frey curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ResidualRealization.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.Determinant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ResidualRealization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

structure IsResidualRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, p • x = 0 → p • y = 0 → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), p • x = 0 → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), p • x = 0 → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | p • x = 0}) = ⊤

end ResidualRealization

section Determinant

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

def CyclotomicDeterminant (N p : ℕ) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V)) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        LinearMap.det (ρ σ).toLinearMap = (ℓ : k)

end Determinant

end ModularCurve

end


