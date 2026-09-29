-- Prove2me | Definitions.Def_ModularCurve_EigenformIdeal
-- name    : ModularCurve_EigenformIdeal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2182c6e0-629a-59cd-b0d3-24713a2ed475
-- title:
--   Eigenform ideals of the free Hecke algebra
-- statement:
--   Throughout, the Hecke algebra is taken to be the free commutative ring `HeckeAlg` $=\mathbb{Z}[T_\ell : \ell \text{ prime}]$ (a multivariate polynomial ring indexed by `Nat.Primes`, with $T_\ell$ = `heckeGen` $\ell$ the corresponding variable), and for a family of elements $a_\ell$ of a commutative ring `eigenIdeal a` is the kernel of the evaluation homomorphism $T_\ell \mapsto a_\ell$. The first definition, [`ModularCurve.IsEigenformIdeal N 𝔪`](../def/ModularCurve_EigenformIdeal.html#L10), asserts that an ideal $\mathfrak m \subseteq \mathbb{Z}[T_\ell]$ arises from a normalised weight-$2$ eigenform on $\Gamma_0(N)$ reduced to a finite field: there exist a cusp form $f$ of weight $2$ for `CongruenceSubgroup.Gamma0 N`, a proof that $f$ satisfies [`CuspForm.IsNormalizedEigenform`](../def/FLTPrelim_Modularity.html#L28) (a structure whose fields are identities among the $q$-expansion coefficients $a_n(f) =$ `qCoeff f n`: $a_1 = 1$, multiplicativity $a_{mn} = a_m a_n$ for coprime $m,n$, the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for $p \nmid N$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for $p \mid N$ — so the eigenform condition is formulated purely through coefficients, not through Hecke operators), a finite field $k$, a subring $\mathcal O \subseteq \mathbb{C}$ containing $a_\ell(f)$ for every prime $\ell$, and a ring homomorphism $\varphi : \mathcal O \to k$, such that $\mathfrak m$ is the eigenvalue ideal of the system $\ell \mapsto \varphi(a_\ell(f))$. The subring $\mathcal O$ and the map $\varphi$ are part of the existential data; no comparison between $\mathbb{Z}[T_\ell]$ and the Hecke algebra acting on $S_2(\Gamma_0(N))$ is asserted.
--
--   The remaining two declarations instantiate generic predicates with this notion of eigenform ideal. `EigenformSupportAt N p J`, for an abelian group $J$ with a `HeckeAlg`-module structure, says: every ideal $\mathfrak m$ which is an eigenform ideal of level $N$ and contains $p$ has nonzero $\mathfrak m$-torsion in $J$ (the submodule annihilated by all of $\mathfrak m$ is not $\bot$). `EichlerShimuraDataAt N p J`, for a field extension $L/K$ and $J$ carrying both a `HeckeAlg`-module structure and an action of $L \simeq_{\mathrm{alg}[K]} L$, is the bundled conjunction of three clauses: (i) for every prime $\ell \nmid Np$, every valuation subring $A$ of $L$ with $\ell$ a nonunit of $A$, every $\sigma$ in the inertia subgroup of $A$ over $K$ and every $p$-power-torsion $x \in J$, one has $\sigma \cdot x = x$; (ii) for such $\ell$ and $A$ and every $\sigma$ that is a Frobenius at $\ell$ for $A$ (in the decomposition group and inducing $x \mapsto x^\ell$ on the residue field), the Eichler–Shimura relation $\sigma^2 x - T_\ell \cdot (\sigma x) + \ell\, x = 0$ holds for all $p$-power-torsion $x$; (iii) `EigenformSupportAt N p J`. This is the reduced bundle: the determinant clause on Frobenius and the multiplicity-one conditions available in the same family of definitions are not among its fields.
--
--   **Relation to Mathlib.** Mathlib supplies the cusp forms, congruence subgroups and $q$-expansions used here, and the valuation-theoretic inertia and decomposition subgroups, but no Hecke operators on modular forms and no Hecke algebra: `HeckeAlg` is the project's free polynomial ring on symbols $T_\ell$, the eigenform condition is expressed by recursions among $q$-expansion coefficients, and [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16), [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21) and [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51) are the project's own wrappers.
--
--   **Where it is used.** These predicates package the input on the modular side of the argument: a Galois- and Hecke-module $J$ (in practice $p$-power torsion of a Jacobian) whose $\mathfrak m$-torsion for an eigenform ideal $\mathfrak m$ is nonzero and on which Frobenius elements away from $Np$ satisfy the Eichler–Shimura quadratic relation, which is what yields the mod $p$ representation attached to a weight-$2$ eigenform of level $\Gamma_0(N)$ used in the Frey curve, level-lowering and modularity steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_EigenformIdeal.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def IsEigenformIdeal (N : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
    (k : Type) (_ : Field k) (_ : Finite k) (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪) (φ : 𝒪 →+* k),
      𝔪 = eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)

abbrev EigenformSupportAt (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J] : Prop :=
  EigenformSupport p J (IsEigenformIdeal N)

abbrev EichlerShimuraDataAt {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] :
    Prop :=
  EichlerShimuraDataReduced (K := K) (L := L) N p J (IsEigenformIdeal N)

end ModularCurve


