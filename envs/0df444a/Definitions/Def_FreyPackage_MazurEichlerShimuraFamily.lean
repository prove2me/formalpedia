-- Prove2me | Definitions.Def_FreyPackage_MazurEichlerShimuraFamily
-- name    : FreyPackage_MazurEichlerShimuraFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/8b382710-8d9d-5dca-a727-9732dd43e82d
-- title:
--   Eichler–Shimura congruence relation and its Mazur-principle family
-- statement:
--   Two conditional predicates are introduced. For $M \ge 1$ and a natural number $p$, [`ModularCurve.EichlerShimuraRelationOn M p`](../def/FreyPackage_MazurEichlerShimuraFamily.html#L13) asserts: if `HeckeInputsAll M` holds — that is, for every prime $\ell$ the data `HeckeInputsAlong (AlgebraicClosure ℚ) M ℓ` (integrality of the two degeneracy maps $\alpha,\beta$ from the base-changed full modular function field of level $M$ into that of level $M\ell$, existence of principal divisors at level $M\ell$, finiteness along $\alpha$, the fundamental identity along $\beta$ and the pushforward norm formula along $\alpha$) is available, so that the Hecke correspondence operator on $J_0(M) = \mathrm{Pic}^0$ of the level-$M$ function field over $\overline{\mathbb Q}$ is the intended one rather than $0$; and if `HeckeOperatorsCommuteBar M` holds, i.e. the endomorphisms `heckeOperatorBar M ℓ` of `JZero M` commute pairwise — then, with `JZero M` regarded as a module over $\mathbb T = \mathbb Z[T_\ell : \ell \text{ prime}] =$ `MvPolynomial Nat.Primes ℤ` via `heckeModuleBar M` (evaluation of polynomials at the Hecke endomorphisms), the predicate `FrobeniusQuadraticConcrete M p` holds. The latter unfolds to: for every prime $\ell \nmid Mp$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ in its nonunits, every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ that is a Frobenius at $\ell$ for $A$, and every $x \in J_0(M)$ annihilated by some power of $p$,
--   $$\sigma^2 x - T_\ell(\sigma x) + \ell x = 0,$$
--   the Galois action being the arithmetic (coefficientwise) one on the Laurent-series model.
--
--   For a Frey package $P$ (nonzero integers $a,b,c$ with $a^p+b^p=c^p$, $p \ge 5$ prime, $\gcd(a,b)=1$, $a \equiv 3 \bmod 4$, $b \equiv 0 \bmod 2$) and $q \ge 1$, [`FreyPackage.MazurEichlerShimuraFamily P q`](../def/FreyPackage_MazurEichlerShimuraFamily.html#L24) asserts `EichlerShimuraRelationOn (N * q) P.p` for every level $N \ge 1$ with $q \nmid N$: the congruence relation at the Frey exponent $p$, uniformly over all levels divisible by $q$ exactly once in this sense.
--
--   **Relation to Mathlib.** Mathlib has no Hecke operators on Jacobians of modular curves and no Eichler–Shimura relation; the Hecke algebra (a polynomial ring on the set of primes), the Jacobian `JZero`, the Hecke module structure and the Frobenius-quadratic clause are all project notions, built on Mathlib's valuation subrings, inertia subgroups and Laurent series.
--
--   **Where it is used.** These predicates package the Eichler–Shimura congruence relation in the form required as one of the inputs to Mazur's principle for the Frey curve: the relation pins the characteristic polynomial of Frobenius at an auxiliary prime on the $p$-power torsion of $J_0(Nq)$, which together with multiplicity one rules out the toric contribution in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_MazurEichlerShimuraFamily.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_AttachmentConcrete
import Definitions.Def_ModularCurve_HeckeInputsAll

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def EichlerShimuraRelationOn (M p : ℕ) [NeZero M] : Prop :=
  HeckeInputsAll M → HeckeOperatorsCommuteBar M →
    letI := heckeModuleBar M
    FrobeniusQuadraticConcrete M p

end ModularCurve

namespace FreyPackage

open ModularCurve

def MazurEichlerShimuraFamily (P : FreyPackage) (q : ℕ) [NeZero q] : Prop :=
  ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → EichlerShimuraRelationOn (N * q) P.p

end FreyPackage

end


