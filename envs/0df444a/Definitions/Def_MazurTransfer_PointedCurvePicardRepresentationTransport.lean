-- Prove2me | Definitions.Def_MazurTransfer_PointedCurvePicardRepresentationTransport
-- name    : MazurTransfer_PointedCurvePicardRepresentationTransport
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T07:45:31.774371+00:00
-- url     : https://prove2.me/theorems/944393b1-9e44-4db0-9f31-c557adddd16a
-- title:
--   Relative Picard representation transport along a pointed curve isomorphism
-- statement:
--   Let $C$ and $C^{\prime}$ be schemes over a commutative ring $R$, with specified sections, and let $e:C^{\prime}\simeq C$ be an isomorphism over $R$ respecting those sections. If a designated scheme $D$ represents the algebraically trivial rigidified relative Picard subfunctor for $C$, the construction gives a representation for $C^{\prime}$: $$\operatorname{Pic}^{0}_{C^{\prime}/R}\simeq D.$$ The designation retains exactly the same underlying scheme, structure morphism and zero section. The universal bundle is pulled back along $e$, and its universal property is transported by the explicit inverse line-bundle transports. This connects actual integral Picard fibres to the literal field curves.
-- source:
--   MazurTheorem CurveIsoPicardRepresentationTransport.lean, Apache-2.0, Vas and contributors. Both original data constructors relabelDesignation and transportRepresentation are retained with their complete bodies unchanged, using the public structural pullback and inverse transports and the separately Proved algebraic-equivalence preservation theorem. Both complete original closed types and both constructor values are kernel-compared. Reuses original official Anthropic FLT relative Picard APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: Order13IntegralPicardLiteralFibreRepresentations for the same integral family over rational, mod-3 and mod-5 fields.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a pointed curve isomorphism transports the original
algebraically trivial relative Picard representation while retaining the
same representing scheme, structural map and zero section.
Named downstream consumer: the literal rational/mod-3/mod-5 fibres of the
actual integral Picard family.
-/
import Definitions.Def_MazurTransfer_PointedCurveIsomorphismLineBundleTransportCore
import Theorems.Thm_MazurTransfer_CurveHomRigidifiedLineBundlePullback_pullbackRigidified_algEquivZero

noncomputable section
universe u
namespace MazurTransfer.CurveIsoPicardRepresentationTransport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open CurveHomRigidifiedLineBundlePullback CurveIsoRigidifiedLineBundleTransport
variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
variable {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
variable {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
variable {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
variable (e : C' ≅ C) (he : e.hom ≫ c = c') (hε : ε'.val ≫ e.hom = ε.val)

def relabelDesignation (D : RelativePic0Designation R c) : RelativePic0Designation R c' where
  P := D.P
  toBase := D.toBase
  zeroSection := D.zeroSection
  zeroSection_toBase := D.zeroSection_toBase

def transportRepresentation (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') (relabelDesignation (c' := c') D) where
  poincare := forward e he hε h.poincare
  poincare_mem := pullbackRigidified_algEquivZero e.hom he hε h.poincare h.poincare_mem
  univ := by
    intro T t M hM
    let N := backward e he hε M
    have hN : (algEquivZeroCut c ε).P t N :=
      pullbackRigidified_algEquivZero e.inv (inv_over e he) (inv_section e hε) M hM
    obtain ⟨g,⟨hg⟩,huni⟩ := h.univ t N hN
    refine ⟨g,⟨?_⟩,?_⟩
    · exact (forward_pullbackAlong_iso e he hε g h.poincare).symm ≪≫
        pullbackRigidified_congr e.hom he hε hg ≪≫ forward_backward_iso e he hε M
    · intro g' hgg
      obtain ⟨hgg⟩ := hgg
      apply huni g'
      exact ⟨(backward_forward_iso e he hε (h.poincare.pullbackAlong g')).symm ≪≫
        pullbackRigidified_congr e.inv (inv_over e he) (inv_section e hε)
          (forward_pullbackAlong_iso e he hε g' h.poincare) ≪≫
        pullbackRigidified_congr e.inv (inv_over e he) (inv_section e hε) hgg⟩
  zero := ⟨(forward_pullbackAlong_iso e he hε
      ⟨D.zeroSection,D.zeroSection_toBase⟩ h.poincare).symm ≪≫
    pullbackRigidified_congr e.hom he hε h.zero.some ≪≫
    pullbackRigidified_unit_iso e.hom he hε (𝟙 _)⟩

end MazurTransfer.CurveIsoPicardRepresentationTransport
#print axioms MazurTransfer.CurveIsoPicardRepresentationTransport.transportRepresentation


