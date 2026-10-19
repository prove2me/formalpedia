-- Prove2me | Definitions.Def_MazurTransfer_PicardDesignationBaseChangePointEquiv
-- name    : MazurTransfer_PicardDesignationBaseChangePointEquiv
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:00:26.409188+00:00
-- url     : https://prove2.me/theorems/0e7df5cd-4c9e-4f08-9638-c3b36f2f5742
-- title:
--   Points of a designated Picard family and points of its actual base change
-- statement:
--   Let $R\to S$ be a homomorphism of commutative rings and let $D$ be a relative Picard designation over $R$. The specified construction gives an equivalence $$D(S)\simeq D_S(S),$$ where the left side consists of morphisms to the original designated scheme above the map $\operatorname{Spec}S\to\operatorname{Spec}R$, and the right side consists of points of the actual scheme base change above the identity of $\operatorname{Spec}S$. Both maps use the original pullback square. This transfers finite point counts to the exact point type carrying the integral family’s original relative group law.
-- source:
--   MazurTheorem PicardDesignationBaseChangePointEquiv.lean, Apache-2.0, Vas and contributors. Original single data constructor retained byte-for-byte, including all pullback maps and inverse proofs. The original source already passes native, strict and complete frontend checks at SHA256 8ee441662c8d82ddbcfe9bd81ea7aeacdafb834e87941fd81bae8b7694f303af. Its proof is reused without rerunning native verification. A metadata-only audit checks closure of its complete constructor type and value and validates import through the public Definition alias. Named downstream consumer: the actual integral family’s mod-3/mod-5 relative point cardinality 19 and original relative group law.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: points of the same Picard scheme over a new-ring base map
are equivalent to rational points of its actual scheme base change.
Named downstream consumer: finite point-cardinality 19 for the actual
integral family's mod-3/mod-5 points in the original relative group law.
-/
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

noncomputable section
universe u
namespace MazurTransfer.PicardDesignationBaseChangePointEquiv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}

def pointEquiv (D : RelativePic0Designation R c) :
    SchemeHomOver (specMap R S) D.toBase ≃
      SchemeHomOver (𝟙 (Spec (.of S))) (D.baseChange S).toBase where
  toFun p := ⟨pullback.lift p.val (𝟙 _) (by rw [Category.id_comp]; exact p.property), pullback.lift_snd _ _ _⟩
  invFun q := ⟨q.val ≫ pullback.fst D.toBase (specMap R S), by
    rw [Category.assoc,pullback.condition,← Category.assoc,q.property,Category.id_comp]⟩
  left_inv p := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv q := by
    apply Subtype.ext
    dsimp only
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd,q.property]

end MazurTransfer.PicardDesignationBaseChangePointEquiv
#print axioms MazurTransfer.PicardDesignationBaseChangePointEquiv.pointEquiv


