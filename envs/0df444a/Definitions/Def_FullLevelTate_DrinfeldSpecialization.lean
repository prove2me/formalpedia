-- Prove2me | Definitions.Def_FullLevelTate_DrinfeldSpecialization
-- name    : FullLevelTate_DrinfeldSpecialization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/8cc5e27b-3d13-5d83-994c-033c15c0aa99
-- title:
--   Drinfeld specialisation data for a full-level Tate datum
-- statement:
--   Throughout, $q$ is a prime, $M'$ a natural number and $O'$ a commutative local ring; $D : \mathrm{Datum}\ q\ M'\ O'$ is a full-level Tate datum, that is, a finite free $O'$-module $D.V$ carrying a representation `gal` of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ by $O'$-endomorphisms which is adically continuous, a multiplicative action `gl2` of [`CuspidalType.GL2 q`](../def/CuspidalType_IsCuspidalOfType.html#L19), and a ring homomorphism `hecke` from $\mathbb{Z}[T_\ell : \ell \text{ prime}]$, the three actions commuting pairwise, together with unramifiedness of `gal` outside $q$, $M'$ and the residue characteristic and an Eichler–Shimura relation $\mathrm{Frob}_\ell^2 - T_\ell\,\mathrm{Frob}_\ell + \ell\,\langle\ell\rangle = 0$ at the remaining primes. Further context: a field $K$ which is an algebra over $O'$ and over $\mathbb{Q}_\lambda$ for a prime $\lambda$, and a field $k$ which is an algebra over $\mathbb{F}_{q^2}$ such that the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q k`](../def/DrinfeldCurve_CoordRing.html#L21) is a domain.
--
--   The single declaration is the structure [`FullLevelTate.Datum.DrinfeldSpecialization`](../def/FullLevelTate_DrinfeldSpecialization.html#L14), whose data are: a type `index`, which is finite; and a $K$-linear map `sp` from $K \otimes_{O'} D.V$ to [`DrinfeldCurve.tateProd q k lam K index`](../def/DrinfeldCurve_TateRep.html#L27), i.e. to the product over `index` of copies of $K \otimes_{\mathbb{Q}_\lambda} \bigl(\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda\bigr)$, where $T_\lambda$ is the $\lambda$-adic Tate module of the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the function field $\mathrm{Frac}(\mathrm{CoordRing}\ q\ k)$ of the Drinfeld curve over $k$ (divisors being finitely supported $\mathbb{Z}$-combinations of places, modulo principal divisors of degree zero).
--
--   Thus the structure is pure data: no compatibility of `sp` with the $\mathrm{GL}_2(\mathbb{F}_q)$-, Hecke- or Galois-actions, and no injectivity, is imposed as a field. Such properties are stated separately by the results that construct or consume a value of this structure.
--
--   **Relation to Mathlib.** Mathlib has no Drinfeld-curve Tate module or specialisation notion; the Drinfeld curve, its coordinate and function fields, the divisor class group [`AlgebraicCurve.Pic0`](../def/AlgebraicCurve_DivisorClassGroup.html#L223) and the rational Tate module used here are all project definitions, built on Mathlib's valuation subrings, fraction fields and tensor products.
--
--   **Where it is used.** The target of `sp` packages the $\lambda$-adic Tate module of the Jacobian of the Drinfeld (Deligne–Lusztig) curve for $\mathrm{GL}_2(\mathbb{F}_q)$, which is the vehicle for comparing the $\mathrm{GL}_2(\mathbb{F}_q)$-representation on the Tate module of the Jacobian of the full level-$q$ modular curve with cuspidal representations in characteristic $q$. It is used in the level-lowering part of the route, where ramification at $q$ of the Frey curve's mod-$\ell$ representation must be removed from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FullLevelTate_DrinfeldSpecialization.lean

import Definitions.Def_FullLevelTate_Datum
import Definitions.Def_DrinfeldCurve_TateRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FullLevelTate

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} {O' : Type} [CommRing O'] [IsLocalRing O']

structure Datum.DrinfeldSpecialization (D : Datum q M' O') (K : Type) [Field K] [Algebra O' K]
    (lam : ℕ) [Fact lam.Prime] [Algebra ℚ_[lam] K]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)] : Type 1 where

  index : Type
  [instFinite : Finite index]

  sp : K ⊗[O'] D.V →ₗ[K] DrinfeldCurve.tateProd q k lam K index

attribute [instance] Datum.DrinfeldSpecialization.instFinite

end FullLevelTate

end


