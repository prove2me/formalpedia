-- Prove2me | Definitions.Def_AlgebraicCurve_CurveModel
-- name    : AlgebraicCurve_CurveModel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/db4c5e0d-403a-5ee4-8441-16d1a337efaf
-- title:
--   Curve models of a one-variable function field
-- statement:
--   Fix a field $K$ (in universe $u$) and a field $L$ (in universe $v$) with a $K$-algebra structure. The auxiliary map `baseToFunctionField` attaches to a morphism $c \colon C \to \operatorname{Spec} K$ from an integral scheme $C$ the ring homomorphism $K \to K(C)$ into the function field (the stalk at the generic point) obtained from the identification of $K$ with the global sections of $\operatorname{Spec} K$, the map on global sections induced by $c$, and the germ map at the generic point; `functionFieldAlgebra` turns this into the corresponding $K$-algebra structure on $K(C)$.
--
--   The structure `CurveModel K L` bundles: a scheme $C$; a morphism `toBase` $\colon C \to \operatorname{Spec} K$; instance fields asserting that $C$ is integral and that `toBase` is proper and smooth of relative dimension $1$; a ring isomorphism `ffEquiv` $\colon L \simeq K(C)$ which, by the field `ffEquiv_algebraMap`, carries $\operatorname{algebraMap}_{K,L}(a)$ to the image of $a$ under `baseToFunctionField toBase` for every $a \in K$; a map `placeOfPoint` from the closed points of $C$ to the places of $L/K$, required to be bijective; the condition `range_stalk_eq` that for each closed point $x$ the image of the stalk $\mathcal O_{C,x}$ in $L$, under the canonical map to $K(C)$ followed by `ffEquiv.symm`, is exactly the subring underlying the valuation subring of the place `placeOfPoint x`; and the condition `finset_subset_affineOpen` that every finite set of points of $C$ is contained in a single affine open. Here a place of $L/K$ is, by definition, a valuation subring of $L$ containing the image of $K$, different from $L$ itself, and a principal ideal ring (hence a discrete valuation ring).
--
--   The remaining declarations form the interface: `ffAlgEquiv` upgrades `ffEquiv` to a $K$-algebra isomorphism $L \simeq_K K(C)$, `placeEquiv` packages `placeOfPoint` as an equivalence between closed points of $C$ and places of $L/K$, and, when $K$ is algebraically closed, `pointEquivPlace` composes the identification of sections of `toBase` (morphisms $p \colon \operatorname{Spec} K \to C$ with $p$ followed by `toBase` the identity) with closed points to obtain an equivalence between such sections and places; two lemmas record the values of these equivalences.
--
--   **Relation to Mathlib.** The scheme-theoretic ingredients (`IsIntegral`, `IsProper`, `SmoothOfRelativeDimension`, `Scheme.functionField`, `closedPoints`, `pointEquivClosedPoint`) are Mathlib's; the notion of a place of $L/K$ as a bundled valuation subring, and the notion of a curve model tying it to a smooth proper curve, are the project's own.
--
--   **Where it is used.** Curve models provide the dictionary between the valuation-theoretic description of a one-variable function field — its places, divisors and divisor class group — and the geometry of a smooth proper curve over the base field, so that statements proved on one side may be used on the other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CurveModel.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve

def baseToFunctionField {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : K →+* C.functionField :=
  (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

structure CurveModel (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] where

  C : Scheme.{u}

  toBase : C ⟶ Spec (CommRingCat.of K)

  [isIntegral : IsIntegral C]

  [isProper : IsProper toBase]

  [smooth : SmoothOfRelativeDimension 1 toBase]

  ffEquiv : L ≃+* C.functionField

  ffEquiv_algebraMap : ∀ a : K, ffEquiv (algebraMap K L a) = baseToFunctionField toBase a

  placeOfPoint : closedPoints C → Place K L

  placeOfPoint_bijective : Function.Bijective placeOfPoint

  range_stalk_eq : ∀ x : closedPoints C,
    ((ffEquiv.symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (placeOfPoint x).toValuationSubring.toSubring

  finset_subset_affineOpen : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

attribute [instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

abbrev functionFieldAlgebra (M : CurveModel K L) : Algebra K M.C.functionField :=
  (baseToFunctionField M.toBase).toAlgebra

def ffAlgEquiv (M : CurveModel K L) :
    letI := M.functionFieldAlgebra
    L ≃ₐ[K] M.C.functionField :=
  letI := M.functionFieldAlgebra
  AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap

theorem ffAlgEquiv_apply (M : CurveModel K L) (f : L) : M.ffAlgEquiv f = M.ffEquiv f := rfl

def placeEquiv (M : CurveModel K L) : closedPoints M.C ≃ Place K L :=
  Equiv.ofBijective M.placeOfPoint M.placeOfPoint_bijective

theorem placeEquiv_apply (M : CurveModel K L) (x : closedPoints M.C) :
    M.placeEquiv x = M.placeOfPoint x := rfl

def pointEquivPlace [IsAlgClosed K] (M : CurveModel K L) :
    {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} ≃ Place K L :=
  (pointEquivClosedPoint M.toBase).trans M.placeEquiv

theorem pointEquivPlace_apply [IsAlgClosed K] (M : CurveModel K L)
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.pointEquivPlace p = M.placeOfPoint (pointEquivClosedPoint M.toBase p) := rfl

end CurveModel

end AlgebraicCurve

end


