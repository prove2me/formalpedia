-- Prove2me | Definitions.Def_ModularCurve_JZeroTorsionHopfOrder
-- name    : ModularCurve_JZeroTorsionHopfOrder
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/4f378b78-8704-5bb2-b4e3-f49163a818e7
-- title:
--   Torsion Hopf orders over a subgroup family in J₀(p)
-- statement:
--   For primes $p$ and $q$, a valuation subring $A$ of $\overline{\mathbf Q}$ with $p$ lying in its set of nonunits (the predicate [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16)), and a family $V : \mathbf N \to$ (additive subgroups of $J_0(p)$, where `JZero p` is the degree-zero Picard group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbf Q}$ of the full modular function field of level $p$), the structure [`ModularCurve.JZeroTorsionHopfOrder`](../def/ModularCurve_JZeroTorsionHopfOrder.html#L15) packages the following data. First, a family $H_m$ ($m \in \mathbf N$) of commutative rings, each carrying a Hopf algebra structure over $\mathbf Z$, of finite type as a $\mathbf Z$-algebra and flat as a $\mathbf Z$-module, with the field `ff_finite` asserting that for every prime $\ell \neq p$ the base change of $H_m$ to [`GaloisRep.ratLocalizedAt ℓ`](../def/GaloisRep_Flat.html#L8) — the subring of $\mathbf Q$ of fractions whose denominator is coprime to $\ell$ — is a finite module over that subring. Second, for each $m$ a bijection `genericPoints m` from the convolution monoid `WithConv` of $\mathbf Z$-algebra maps $H_m \to \overline{\mathbf Q}$ onto $V_m$, carrying convolution products to sums (`genericConv`) and equivariant for $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ in the sense that if $g = \sigma \circ f$ pointwise then the point attached to $g$ is $\sigma$ applied to the point attached to $f$ (`genericGalois`). Third, a bijection `pFibrePoints m` from the convolution monoid of $\mathbf Z$-algebra maps $H_m \to A$ onto $\mathrm{jZeroToricTorsion}\,p\,A\,(q^m) \sqcap V_m$, again additive on convolution, where $\mathrm{jZeroToricTorsion}\,p\,A\,m$ is by definition the intersection of the subgroup `jZeroTorsion p m` with the image of `inertiaInvariantPoints p A` under multiplication by the natural number `eisensteinNumerator p`; the field `pFibreGenericCompat` requires that an $A$-point and a $\overline{\mathbf Q}$-point obtained from it by composing with $A \hookrightarrow \overline{\mathbf Q}$ have the same image in $J_0(p)$. Fourth, the convolution monoid of $T$-points is commutative for every commutative ring $T$ (`pointsComm`). Finally, surjective $\mathbf Z$-bialgebra maps $H_{m+1} \to H_m$ are given, such that, whenever $V_m \le V_{m+1}$, precomposition with $H_{m+1} \to H_m$ preserves the attached point of $J_0(p)$. Nothing is proved here; the structure records the data an inhabitant must supply.
--
--   **Relation to Mathlib.** Hopf algebras over a commutative ring, the convolution monoid `WithConv` on algebra maps out of a bialgebra, and bialgebra homomorphisms `→ₐc` are Mathlib notions; `jZeroToricTorsion`, `JZero` and [`GaloisRep.ratLocalizedAt`](../def/GaloisRep_Flat.html#L8) (the subring of $\mathbf Q$ with denominators coprime to a given prime) are the project's own, as is the present structure, which has no Mathlib counterpart.
--
--   **Where it is used.** The data describe, without reference to Néron models or fppf sheaves, the affine Hopf orders whose generic points cut out the prescribed subgroups $V_m$ of $J_0(p)$ and whose $A$-points cut out the toric $q^m$-torsion at $A$; they serve as the finite flat group-scheme input to the Eisenstein-ideal arguments for $J_0(p)$, and hence to the flatness conditions imposed on the Galois representations in the modularity-lifting part of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroTorsionHopfOrder.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

structure JZeroTorsionHopfOrder (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (V : ℕ → AddSubgroup (JZero p)) where
  H : ℕ → Type
  [instCommRing_H : ∀ m, CommRing (H m)]
  [instHopfAlgebra_H : ∀ m, HopfAlgebra ℤ (H m)]
  [instFiniteType_H : ∀ m, Algebra.FiniteType ℤ (H m)]
  [instFlat_H : ∀ m, Module.Flat ℤ (H m)]
  ff_finite : ∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))
  genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ) ≃ ↥(V m)

  genericConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    genericPoints m (f * g) = genericPoints m f + genericPoints m g

  genericGalois : ∀ m, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, g h = σ (f h)) →
    ((genericPoints m g : ↥(V m)) : JZero p)
      = σ • ((genericPoints m f : ↥(V m)) : JZero p)
  pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(jZeroToricTorsion p A (q ^ m) ⊓ V m)

  pFibreConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A),
    pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g

  pFibreGenericCompat : ∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A),
    ∀ ψ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, ψ h = A.subtype (φ h)) →
    ((pFibrePoints m φ : ↥(jZeroToricTorsion p A (q ^ m) ⊓ V m)) : JZero p)
      = ((genericPoints m ψ : ↥(V m)) : JZero p)

  pointsComm : ∀ (m : ℕ) (T : Type) [CommRing T], ∀ f g : WithConv (H m →ₐ[ℤ] T), f * g = g * f

  levelMap : ∀ m, H (m + 1) →ₐc[ℤ] H m
  levelMap_surjective : ∀ m, Function.Surjective (levelMap m)
  levelMap_genericPoints : ∀ (m : ℕ) (hle : V m ≤ V (m + 1)) (φ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ)),
    ((genericPoints (m + 1)
        (WithConv.toConv ((WithConv.ofConv φ).comp (levelMap m : H (m + 1) →ₐ[ℤ] H m))) : ↥(V (m + 1))) : JZero p)
      = ((genericPoints m φ : ↥(V m)) : JZero p)

attribute [instance] JZeroTorsionHopfOrder.instCommRing_H
  JZeroTorsionHopfOrder.instHopfAlgebra_H JZeroTorsionHopfOrder.instFiniteType_H
  JZeroTorsionHopfOrder.instFlat_H

end ModularCurve

end


