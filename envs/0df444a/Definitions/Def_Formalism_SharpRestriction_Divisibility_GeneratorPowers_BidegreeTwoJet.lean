-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BidegreeTwoJet
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_BidegreeTwoJet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:09.319825+00:00
-- url     : https://prove2.me/theorems/3f002244-95af-494a-a9fa-e128fc0bd623
-- title:
--   Bidegree Two Jet
-- statement:
--   Definitions and structural lemmas for Bidegree Two Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/BidegreeTwoJet.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpBijectiveUniformisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace BidegreeTwoJet
section Jets
variable {V : Type} [CommRing V] {G' G : Over (Sp V)} [GrpObj G'] [GrpObj G] {n d : ℕ}
def zV (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) : jOG (𝟙 (Sp V)) d m n ⟶ G' :=
  pG.lim.lift (Fan.mk _ fun i => homAt (𝟙 (Sp V)) (jetCopy (S := V) d m i) ≫ xT m)
lemma jet_square (I : Ideal V) (e m : ℕ) :
    spMap (jetCoef (Ideal.Quotient.mk (I ^ (e + 1))) (Fin n × Fin d) m) ≫ spMap (algebraMap V (Jet V (Fin n × Fin d) m)) =
      spMap (algebraMap (V ⧸ I ^ (e + 1)) (Jet (V ⧸ I ^ (e + 1)) (Fin n × Fin d) m)) ≫ thick V I e := by
  simp only [spMap, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp only [RingHom.comp_apply]
  rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, jetCoef, Ideal.Quotient.lift_mk]
  simp [MvPolynomial.algebraMap_eq]
def zE (I : Ideal V) (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (e m : ℕ) :
    Sp (Jet (V ⧸ I ^ (e + 1)) (Fin n × Fin d) m) ⟶ (thickObj V I e G').left :=
  pullback.lift (spMap (jetCoef (Ideal.Quotient.mk (I ^ (e + 1))) (Fin n × Fin d) m) ≫ (zV pG xT m).left)
    (spMap (algebraMap (V ⧸ I ^ (e + 1)) _)) (by
      rw [Category.assoc, Over.w (zV pG xT m)]
      simpa using jet_square (n := n) (d := d) I e m)
end Jets
def jetVal {A : Type} [CommRing A] {X : Scheme.{0}} (h : Sp A ⟶ X) (W : X.Opens) (hW : h ⁻¹ᵁ W = ⊤) (φ : Γ(X, W)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((h.appLE W ⊤ hW.ge).hom φ)
section Coord
variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D' : DegData V I}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' G : Over (Sp V)} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  {n d : ℕ}
def coordSet (U' : Unif I D' A' G') (pG : IsPowGrp G' G n) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (e m : ℕ) :
    Set (Jet (V ⧸ I ^ (e + 1)) (Fin n × Fin d) m) :=
  {x | ∃ (W : D'.toPre.P.A.left.Opens) (hW : (zE I pG xT e m ≫ (U'.gt e).pG.left) ⁻¹ᵁ W = ⊤)
      (φ : Γ(D'.toPre.P.A.left, W)), x = jetVal _ W hW φ} ∪
  {x | ∃ (χ : D'.toPre.X) (j : Fin 4 → D'.toPre.P.L.ι)
      (hj : zE I pG xT e m ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG χ) j = ⊤),
      x = jetVal _ _ hj (((U'.gt e).t χ).s j).val}
end Coord
open IsLocalRing in

def UnifChartTieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (n : ℕ)
    (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (e m : ℕ),
    Algebra.adjoin (T.V ⧸ maximalIdeal T.V ^ (e + 1)) (coordSet U' pG C.xT e m) = ⊤
end BidegreeTwoJet
end Formalism.MainNotions.ModuliIntegralCharts.H1


