-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.baseChange_negMor_comp_fst
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:37.751368+00:00
-- url     : https://prove2.me/submissions/278b0c57-668a-49a7-86e5-1648e950b76c

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

private theorem inverse_natural {k : Type} [Field k] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
    {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (g : T' ⟶ T) (hg : g ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp g hg (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp g hg x) := by
  letI := G.pointGroup t'
  apply eq_inv_of_mul_eq_one_left
  change G.mul t' (GoodReductionJacobian.schemeHomOverComp g hg (G.inv t x))
    (GoodReductionJacobian.schemeHomOverComp g hg x) = G.one t'
  rw [← G.mul_natural t t' g hg, G.inv_mul_cancel, G.one_natural]

/-- Inversion for a base-changed group law commutes with the projection. -/
theorem _root_.solution {k k' : Type} [Field k] [Field k']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f)
    (b : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    negMor (pullback.snd f b) (G.baseChange b) ≫ pullback.fst f b =
      pullback.fst f b ≫ negMor f G := by
  have h := congrArg Subtype.val
    (inverse_natural G f (pullback.snd f b ≫ b) (pullback.fst f b)
      pullback.condition (idPt f))
  simpa [negMor, RelativeGroupLaw.baseChange, RelativeGroupLaw.baseChangePointOfBase,
    RelativeGroupLaw.baseChangePointToBase, pullback.lift_fst, idPt, GoodReductionJacobian.schemeHomOverComp] using h.symm

end AlgebraicGeometry.Polarisation
