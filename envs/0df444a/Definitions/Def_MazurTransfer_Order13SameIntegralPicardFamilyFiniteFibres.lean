-- Prove2me | Definitions.Def_MazurTransfer_Order13SameIntegralPicardFamilyFiniteFibres
-- name    : MazurTransfer_Order13SameIntegralPicardFamilyFiniteFibres
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:14:07.891979+00:00
-- url     : https://prove2.me/theorems/c827f6d8-f631-4783-96a3-4a79a55a8e14
-- title:
--   One actual integral Picard family has nineteen points over both canonical finite-field maps
-- statement:
--   Put $B=\mathbb Z[1/104]$ and use the specified localization maps $B\to\mathbf F_q$ for $q=3,5$. There exists one actual designated Picard representative $D/B$, with its representation of the algebraically trivial rigidified Picard subfunctor of the literal order-thirteen curve and its positive-infinity section, such that $D\to\operatorname{Spec}B$ is an abelian scheme in the original interface and $$\#D(\mathbf F_3)=\#D(\mathbf F_5)=19.$$ Both counts use points of this same designated scheme over the canonical base maps. More generally, for any commutative ring $R$, any actual Picard representation $D/R$ of this curve and any $R$-algebra structure on $\mathbf F_q$ with $q=3$ or $5$, its literal base-changed fibre and its corresponding original relative point type are finite of cardinality nineteen. These are the finite groups used for specialization through the one integral family.
-- source:
--   Original complete contracts and proof bodies from MazurTheorem Order13IntegralPicardFiniteFibreCardinality.lean, Order13IntegralPicardRelativeFiniteFieldPoints.lean and Order13SameIntegralPicardFamilyFiniteFibres.lean, Apache-2.0, Vas and contributors. Exactly four needed original declarations are retained: three structural existence/cardinality theorems and the canonicalFiniteFieldMap constructor. All bodies are unchanged; project imports alone become Proved public interfaces. The four complete original closed types and the original canonical finite-field map value are kernel-compared in separate original and public environments. Reuses the newly Proved actual integral abelian Picard family, actual literal-fibre representation bridge and original official Anthropic FLT scheme/Picard base-change APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Native, strict and full frontend checks pass using only standard axioms. The small structural existence theorem is embedded because it is cited by the original chosen designation constructor in Order13SameIntegralPicardRationalSchemeComparison. Named downstream consumers: this chosen integral designation, same-family rational torsion specialization and its arithmetic Picard group identification.

import Mathlib
import Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
import Definitions.Def_MazurTransfer_PicardDesignationBaseChangePointEquiv
import Definitions.Def_MazurTransfer_Order13IntegralBaseAndFieldMaps
import Theorems.Thm_MazurTransfer_order13_every_actual_represented_picard_point_cardinality_three_or_five
import Theorems.Thm_MazurTransfer_Order13ActualIntegralAbelianPicardFamily_actual_integral_abelian_picard_family
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every actual integral Picard representation has literal
mod-3 and mod-5 base-change fibres with exactly 19 rational points.
This is the same representing scheme's pullback, with its exact structural
map retained, rather than an independently chosen finite-field Picard.
Named downstream consumer: torsion specialization for this integral family.
Uses our Accepted every-representing-model cardinality theorem and original
FLT Picard base-change interfaces; all provenance and hypotheses retained.
-/


noncomputable section
universe u
namespace MazurTransfer.Order13IntegralPicardFiniteFibreCardinality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections Order13IntegralPicardLiteralFibreRepresentations

theorem actual_integral_picard_finite_fibre_cardinality
    (R : Type) [CommRing R] (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D)
    (q : ℕ) (hq : q=3 ∨ q=5) [Algebra R (ZMod q)] :
    Finite (SchemeHomOver (𝟙 (Spec (.of (ZMod q)))) (D.baseChange (ZMod q)).toBase) ∧
    Nat.card (SchemeHomOver (𝟙 (Spec (.of (ZMod q)))) (D.baseChange (ZMod q)).toBase) = 19 ∧
    Finite (Over.mk (𝟙 (Spec (.of (ZMod q)))) ⟶ Over.mk (D.baseChange (ZMod q)).toBase) ∧
    Nat.card (Over.mk (𝟙 (Spec (.of (ZMod q)))) ⟶ Over.mk (D.baseChange (ZMod q)).toBase) = 19 := by
  letI : Fact (Nat.Prime q) := ⟨by rcases hq with rfl | rfl <;> decide⟩
  obtain ⟨hS⟩ := literal_fibre_representation R (ZMod q) D h
  exact MazurTransfer.order13_every_actual_represented_picard_point_cardinality_three_or_five
    q hq (positiveInfinitySection (ZMod q)) (literalFibreDesignation R (ZMod q) D) hS

end MazurTransfer.Order13IntegralPicardFiniteFibreCardinality
#print axioms MazurTransfer.Order13IntegralPicardFiniteFibreCardinality.actual_integral_picard_finite_fibre_cardinality


/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original integral Picard scheme has exactly 19 points
above the base maps to F3 and F5. The point type is exactly that on which
its original relative group law operates.
Named downstream consumer: specialization of rational torsion into the
same integral family's finite-field groups.
-/


noncomputable section
namespace MazurTransfer.Order13IntegralPicardRelativeFiniteFieldPoints
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections

theorem actual_relative_finite_field_points_cardinality
    (R : Type) [CommRing R] (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D)
    (q : ℕ) (hq : q=3 ∨ q=5) [Algebra R (ZMod q)] :
    Finite (SchemeHomOver (specMap R (ZMod q)) D.toBase) ∧
    Nat.card (SchemeHomOver (specMap R (ZMod q)) D.toBase) = 19 := by
  obtain ⟨hf,hcard,_,_⟩ :=
    Order13IntegralPicardFiniteFibreCardinality.actual_integral_picard_finite_fibre_cardinality R D h q hq
  letI := hf
  let e := PicardDesignationBaseChangePointEquiv.pointEquiv R (ZMod q) D
  exact ⟨Finite.of_injective e e.injective, (Nat.card_congr e).trans hcard⟩

end MazurTransfer.Order13IntegralPicardRelativeFiniteFieldPoints
#print axioms MazurTransfer.Order13IntegralPicardRelativeFiniteFieldPoints.actual_relative_finite_field_points_cardinality


/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual Picard abelian scheme over Z[1/104] has exactly
19 relative points over each canonical scalar map to F3 and F5.
Named downstream consumer: specialization of rational torsion into these
same-family finite-field groups. No torsion injectivity is assumed here.
-/


noncomputable section
namespace MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections Order13IntegralBase

def canonicalFiniteFieldMap (q : ℕ) (hq : q=3 ∨ q=5) : BaseRing →+* ZMod q :=
  mapToRing (ZMod q) (by
    apply (ZMod.isUnit_iff_coprime 104 q).2
    rcases hq with rfl | rfl <;> decide)



theorem actual_same_integral_picard_family_finite_fibres :
    ∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (_ : RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)) D),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      ∀ (q : ℕ) (hq : q=3 ∨ q=5),
        letI : Algebra BaseRing (ZMod q) := (canonicalFiniteFieldMap q hq).toAlgebra
        Finite (SchemeHomOver (specMap BaseRing (ZMod q)) D.toBase) ∧
        Nat.card (SchemeHomOver (specMap BaseRing (ZMod q)) D.toBase) = 19 := by
  letI : IsDomain BaseRing := Localization.Away.isDomain (by norm_num : (104 : ℤ) ≠ 0)
  obtain ⟨D,h,_,_,hb,_⟩ :=
    Order13ActualIntegralAbelianPicardFamily.actual_integral_abelian_picard_family BaseRing unit104
  refine ⟨D,h,hb,?_⟩
  intro q hq
  letI : Algebra BaseRing (ZMod q) := (canonicalFiniteFieldMap q hq).toAlgebra
  exact Order13IntegralPicardRelativeFiniteFieldPoints.actual_relative_finite_field_points_cardinality
    BaseRing D h q hq

end MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
#print axioms MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres.actual_same_integral_picard_family_finite_fibres


