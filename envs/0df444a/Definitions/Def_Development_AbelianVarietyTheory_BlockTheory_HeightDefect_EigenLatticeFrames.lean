-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_EigenLatticeFrames
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_EigenLatticeFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:17.506358+00:00
-- url     : https://prove2.me/theorems/31a6b3b1-5403-4fe0-8f9d-6534d1597955
-- title:
--   Eigen Lattice Frames
-- statement:
--   Definitions and structural lemmas for Eigen Lattice Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/EigenLatticeFrames.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def IsEigenLatticeBasis (Dw : Datum H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V))
    (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)) : Prop :=
  (∀ i, IsTan (ub i)) ∧ (∀ i, IsEigV c io G τ (ub i)) ∧
    ∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w
def IsEigenBasisAt (Xo : Moduli Dw l) (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X)
    (τ : E →+* ℂ) (u : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) : Prop :=
  (∀ i, IsTanAt x (u i)) ∧ (∀ i, IsEigAt c τ (u i)) ∧
    ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x u a w
def IsGenericFibre {Xo : Moduli Dw l} {T : CDVR} {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X}
    (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (w : epsOver T.V T.V ⟶ G.G) (v : Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m₁.φ = v ∧
    u' ≫ m₂.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ w.left
def IntegralUpToTriangular (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (yt : Sp T.V ⟶ Y.X) (yF : Sp T.Fr ⟶ Xo.XF c),
      yF ≫ pullback.snd _ _ = spMap io → spMap (algebraMap T.V T.Fr) ≫ yt = yF ≫ Y.j →
      letI := io.toAlgebra
      ∀ y : FrPt Xo c T.Fr, y.x = yF ≫ pullback.fst _ _ →
        ∃ (y₀ : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀.1 y
def EigenLatticesFree (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr),
    letI := io.toAlgebra
    ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = sOf c T.Fr →
    ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (τ : E →+* ℂ),
      (∃ ub, IsEigenLatticeBasis Dw c T io G τ ub) ∧
      ∀ u, IsEigenBasisAt Xo c x τ u →
        ∃ (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
          (v : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
          IsEigenLatticeBasis Dw c T io G τ ub ∧ (∀ i, IsGenericFibre m₁ m₂ (ub i) (v i)) ∧
          ∀ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x v cf (u i)
def FieldPointsFromTest (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
def IntegralFramesAt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  IntegralUpToTriangular Xo c ∧ EigenLatticesFree Xo c ∧ FieldPointsFromTest Xo c
def IntegralFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), IntegralFramesAt Xo c
end GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames


