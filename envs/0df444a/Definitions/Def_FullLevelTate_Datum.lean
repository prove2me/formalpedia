-- Prove2me | Definitions.Def_FullLevelTate_Datum
-- name    : FullLevelTate_Datum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/4f465e76-29ce-5fdb-92bc-47351d853ab9
-- title:
--   Full-level-q Tate module data with Galois, GL2​ and Hecke actions
-- statement:
--   Fix a prime $q$, a natural number $M'$ and a commutative local ring $O'$ with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal O'`. The structure [`FullLevelTate.Datum q M' O'`](../def/FullLevelTate_Datum.html#L11) bundles: a carrier $V$ that is a finite free $O'$-module; a monoid homomorphism `gal` from $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$, realised as the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{End}_{O'}(V)$; a monoid homomorphism `gl2` from $\mathrm{GL}_2(\mathbb Z/q)$ to $\mathrm{End}_{O'}(V)$; and a ring homomorphism `hecke` from [`ModularCurve.HeckeAlg`](../def/HeckeGalois_EichlerShimura.html#L14), the polynomial ring $\mathbb Z[T_\ell : \ell \text{ prime}]$ with one variable `heckeGen ℓ` per rational prime, to $\mathrm{End}_{O'}(V)$. The field `gal_isAdicContinuous` asserts [`GaloisActionIsAdicContinuous`](../def/GaloisRep_Adic.html#L9): for every $n$ there is an intermediate field $L$ of $\bar{\mathbb Q}/\mathbb Q$, finite over $\mathbb Q$, such that every $\sigma$ fixing $L$ pointwise satisfies $\mathrm{gal}(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $v \in V$. Three further fields require the images of `gal`, `gl2` and `hecke` to commute pairwise (Galois with $\mathrm{GL}_2$, Hecke with Galois, Hecke with $\mathrm{GL}_2$). The field `unramified` says that for every prime $\ell \ne q$ with $\ell \nmid M'$ and $\ell \notin \mathfrak m$, every valuation subring $P$ of $\bar{\mathbb Q}$ with $\ell$ a non-unit of $P$, and every $\sigma$ in the image in $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$, one has $\mathrm{gal}(\sigma) = 1$. The field `eichlerShimura` says that for every prime $\ell$ coprime to $q$ with $\ell \nmid M'$ and $\ell \notin \mathfrak m$, every such $P$ above $\ell$, and every $\sigma$ lying in the decomposition group of $P$ and acting as $x \mapsto x^{\ell}$ on the residue field of $P$,
--   $$\mathrm{gal}(\sigma)^2 - \mathrm{hecke}(T_\ell)\,\mathrm{gal}(\sigma) + \ell\cdot \mathrm{gl2}(\langle \ell\rangle) = 0,$$
--   where $\langle \ell \rangle$ is the scalar matrix in $\mathrm{GL}_2(\mathbb Z/q)$ attached to the unit $\ell \bmod q$. No rank or non-degeneracy condition is imposed: the module $O'^0$ with trivial Galois and $\mathrm{GL}_2$ actions and all $T_\ell$ acting as $0$ is an instance of the structure, as an accompanying example records.
--
--   **Relation to Mathlib.** The $\mathrm{GL}_2$ factor is Mathlib's `Matrix.GeneralLinearGroup (Fin 2) (ZMod q)`; Mathlib has no notion of a Hecke algebra acting on Tate modules of modular curves, so [`ModularCurve.HeckeAlg`](../def/HeckeGalois_EichlerShimura.html#L14) (a free polynomial ring on the rational primes) and the $\mathfrak m$-adic continuity condition [`GaloisActionIsAdicContinuous`](../def/GaloisRep_Adic.html#L9) are the project's own.
--
--   **Where it is used.** The structure axiomatises the data carried by the $\lambda$-adic Tate module of the Jacobian of a modular curve of full level $q$ and auxiliary level $M'$, after extension of scalars to $O'$: a continuous Galois action, a commuting action of $\mathrm{GL}_2(\mathbb Z/q)$ coming from the full level structure at $q$, a commuting Hecke action, unramifiedness outside $qM'$ and the residue characteristic, and the Eichler–Shimura congruence relation at the good primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FullLevelTate_Datum.lean

import Definitions.Def_GaloisRep_Adic
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace FullLevelTate

structure Datum (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O'] :
    Type 1 where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module O' V]
  [instFree : Module.Free O' V]
  [instFinite : Module.Finite O' V]

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O' V

  gal_isAdicContinuous : GaloisActionIsAdicContinuous O' gal

  gl2 : CuspidalType.GL2 q →* Module.End O' V

  hecke : ModularCurve.HeckeAlg →+* Module.End O' V

  gal_comm_gl2 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
    gal σ * gl2 x = gl2 x * gal σ

  hecke_comm_gal : ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    hecke t * gal σ = gal σ * hecke t

  hecke_comm_gl2 : ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q),
    hecke t * gl2 x = gl2 x * hecke t

  unramified : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → ¬ ℓ ∣ M' → (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, gal σ = 1

  eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ.Coprime q), ¬ ℓ ∣ M' →
    (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
        gal σ * gal σ - hecke (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) * gal σ
          + (ℓ : O') • gl2 (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)) = 0

attribute [instance] Datum.instAddCommGroup Datum.instModule Datum.instFree Datum.instFinite

example (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O'] :
    Datum q M' O' where
  V := Fin 0 → O'
  gal := 1
  gal_isAdicContinuous := fun n =>
    ⟨⊥, inferInstance, fun σ _ v => by rw [MonoidHom.one_apply, Module.End.one_apply, sub_self]; exact zero_mem _⟩
  gl2 := 1
  hecke := (algebraMap O' (Module.End O' (Fin 0 → O'))).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom O') 0)
  gal_comm_gl2 := fun σ x => by rw [MonoidHom.one_apply, MonoidHom.one_apply]
  hecke_comm_gal := fun t σ => by rw [MonoidHom.one_apply, mul_one, one_mul]
  hecke_comm_gl2 := fun t x => by rw [MonoidHom.one_apply, mul_one, one_mul]
  unramified := fun _ _ _ _ _ _ _ _ _ => MonoidHom.one_apply _
  eichlerShimura := fun _ _ _ _ _ _ _ _ _ => LinearMap.ext fun v => Subsingleton.elim _ _

end FullLevelTate

end


