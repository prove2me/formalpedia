-- Prove2me | Definitions.Def_FieldTheory_RatFuncTower
-- name    : FieldTheory_RatFuncTower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/18380343-a5b3-5aff-b04b-e0b2cbf40900
-- title:
--   Rational function tower over Q​ with Galois action
-- statement:
--   This module sets up the tower $\mathbb{Q}[X]\to\overline{\mathbb{Q}}[X]\to\overline{\mathbb{Q}}(X)$ together with the coefficientwise action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on the top field. The field $\overline{\mathbb{Q}}(X)$ is taken to be [`RatFuncTower.K0`](../def/FieldTheory_RatFuncTower.html#L12), an abbreviation for the fraction ring of the polynomial ring over `AlgebraicClosure ℚ`, rather than Mathlib's `RatFunc` construction. The scoped instance [`RatFuncTower.algebraRatPoly`](../def/FieldTheory_RatFuncTower.html#L14) equips `K0` with the structure of an algebra over $\mathbb{Q}[X]$ whose structure map is the composite of the coefficientwise map $\mathbb{Q}[X]\to\overline{\mathbb{Q}}[X]$ induced by $\mathbb{Q}\hookrightarrow\overline{\mathbb{Q}}$ with the localisation map $\overline{\mathbb{Q}}[X]\to\overline{\mathbb{Q}}(X)$; being scoped, it is in force for consumers that open the namespace. The lemma [`RatFuncTower.algebraMap_ratPoly_apply`](../def/FieldTheory_RatFuncTower.html#L18) records this description of the structure map: for $p\in\mathbb{Q}[X]$, the image of $p$ in `K0` is the image of the polynomial obtained by applying $\mathbb{Q}\to\overline{\mathbb{Q}}$ to each coefficient of $p$.
--
--   For an automorphism $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$, [`RatFuncTower.galLift σ`](../def/FieldTheory_RatFuncTower.html#L23) is the automorphism $\hat\sigma$ of `K0` as a $\mathbb{Q}[X]$-algebra obtained by extending the coefficientwise automorphism of $\overline{\mathbb{Q}}[X]$ attached to $\sigma$ to fraction fields; concretely $\hat\sigma(p/q)=\sigma(p)/\sigma(q)$, with $\sigma$ applied to coefficients. That this extension is $\mathbb{Q}[X]$-linear amounts to the fact that $\sigma$ fixes $\mathbb{Q}$, so it fixes polynomials with rational coefficients. The lemma [`RatFuncTower.galLift_algebraMap`](../def/FieldTheory_RatFuncTower.html#L39) states the compatibility on the polynomial subring: for $p\in\overline{\mathbb{Q}}[X]$, $\hat\sigma$ applied to the image of $p$ in `K0` is the image of the coefficientwise transform of $p$ by $\sigma$.
--
--   **Relation to Mathlib.** The field here is `FractionRing (Polynomial (AlgebraicClosure ℚ))` rather than Mathlib's `RatFunc (AlgebraicClosure ℚ)`. The $\mathbb{Q}[X]$-algebra structure and the lift of a Galois automorphism are the project's own declarations, built from Mathlib's coefficientwise map on polynomials and from the transport of a ring isomorphism of domains to their fraction fields; no algebra instance $\mathbb{Q}[X]\to\overline{\mathbb{Q}}[X]$ is introduced, and the $\mathbb{Q}$-algebra structure on the field itself is Mathlib's.
--
--   **Where it is used.** The tower provides the generic fibre of a Weierstrass curve given over $\mathbb{Q}[X]$: its $\overline{\mathbb{Q}}(X)$-points carry the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ through $\sigma\mapsto\hat\sigma$, and specialising $X$ to a rational value relates them to the $\overline{\mathbb{Q}}$-points of the corresponding fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FieldTheory_RatFuncTower.lean

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace RatFuncTower

abbrev K0 : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

scoped instance algebraRatPoly : Algebra (Polynomial ℚ) K0 :=
  ((algebraMap (Polynomial (AlgebraicClosure ℚ)) K0).comp
    (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).toAlgebra

theorem algebraMap_ratPoly_apply (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) K0 p =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) K0
        (p.map (algebraMap ℚ (AlgebraicClosure ℚ))) := rfl

def galLift (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : K0 ≃ₐ[Polynomial ℚ] K0 :=
  AlgEquiv.ofRingEquiv
    (f := IsFractionRing.ringEquivOfRingEquiv
      (A := Polynomial (AlgebraicClosure ℚ)) (B := Polynomial (AlgebraicClosure ℚ))
      (K := K0) (L := K0) (Polynomial.mapAlgEquiv σ).toRingEquiv)
    (by
      intro p
      have hq : ∀ q : Polynomial (AlgebraicClosure ℚ),
          (Polynomial.mapAlgEquiv σ).toRingEquiv q =
            q.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) := fun q => rfl
      rw [algebraMap_ratPoly_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hq,
        Polynomial.map_map]
      congr 2
      ext x
      simp)

theorem galLift_algebraMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : Polynomial (AlgebraicClosure ℚ)) :
    galLift σ (algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 p) =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) K0
        (p.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
  simp [galLift]

end RatFuncTower

end


