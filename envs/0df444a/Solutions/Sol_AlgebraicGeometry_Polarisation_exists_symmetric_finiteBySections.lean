-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_symmetric_finiteBySections
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:38.978344+00:00
-- url     : https://prove2.me/submissions/cec45f09-2884-45ef-bfe3-68c5893eb5a0

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
import Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_tensor_pullback_negMor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_pullback_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

private theorem inv_natural {k : Type} [Field k] {A : Scheme.{0}}
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

private theorem negMor_comp_self {k : Type} [Field k] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) :
    negMor f G ≫ negMor f G = 𝟙 A := by
  let n : SchemeHomOver f f := G.inv f (idPt f)
  have hn : GoodReductionJacobian.schemeHomOverComp n.1 n.2 (idPt f) = n := by
    apply Subtype.ext
    simp [GoodReductionJacobian.schemeHomOverComp, idPt]
  have h : GoodReductionJacobian.schemeHomOverComp n.1 n.2 n = idPt f := by
    change GoodReductionJacobian.schemeHomOverComp n.1 n.2 (G.inv f (idPt f)) = _
    rw [inv_natural G f f n.1 n.2, hn]
    letI := G.pointGroup f
    exact inv_inv (idPt f)
  simpa [GoodReductionJacobian.schemeHomOverComp, idPt, n, negMor] using congrArg Subtype.val h

/-- Symmetrization preserves a finite presentation by sections. -/
theorem _root_.solution {k : Type} [Field k] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of k)) (G : RelativeGroupLaw k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfinite : M.FiniteBySections f) :
    ∃ L : A.Modules, Scheme.Modules.IsInvertible L ∧ L.FiniteBySections f ∧
      IsSymmetric f G L := by
  let e : A ≅ A := ⟨negMor f G, negMor f G, negMor_comp_self G, negMor_comp_self G⟩
  haveI : IsIso (negMor f G) := e.isIso_hom
  have hneg : ((Scheme.Modules.pullback (negMor f G)).obj M).FiniteBySections f := by
    simpa only [negMor_over] using hfinite.pullback_of_isFinite (negMor f G)
  exact ⟨M ⊗ (Scheme.Modules.pullback (negMor f G)).obj M,
    hM.tensor_monoidalV2 (hM.pullback _), hfinite.tensor_monoidalV2 hneg,
    isSymmetric_tensor_pullback_negMor f G M⟩

end AlgebraicGeometry.Polarisation
