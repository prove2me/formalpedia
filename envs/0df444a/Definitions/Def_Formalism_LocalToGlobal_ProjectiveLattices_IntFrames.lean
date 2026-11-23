-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:46.678946+00:00
-- url     : https://prove2.me/theorems/886aa580-d2aa-402f-8cd3-5632cca19dd0
-- title:
--   Int Frames
-- statement:
--   Definitions and structural lemmas for Int Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntFrames.lean

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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def IntFramesSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    (letI := io.toAlgebra; ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1)
def GenFibreSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt),
      ∃ (t' : SAB H (Sp T.Fr)) (_m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
        (_m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), True
def LieFreeSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X)
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    letI := io.toAlgebra
    ∀ u₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left),
    (∀ τ i, IsTanAt x (u₀ τ i)) → (∀ τ i, IsEigAt c τ (u₀ τ i)) →
    (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u₀ τ) a w) →
    ∃ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
        (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
          ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
        ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u τ i ∧
          u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ∧
      (∀ τ i, IsTanAt x (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧
      (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u τ) a w) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u τ i)
def ThetaFrameSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp T.Fr))
      (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      letI := io.toAlgebra
      ∀ s₀ : LB.Sec (PPx (z ≫ pullback.fst _ _)),
      (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i, s'.f i = scal (z ≫ pullback.fst _ _) a i * s₀.f i) →
      ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx (z ≫ pullback.fst _ _))),
        (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
          σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
        (∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
          (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
          RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
          ∀ g : t'.G.left ⟶ Gx (z ≫ pullback.fst _ _),
            g ≫ (snd (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = m1.φ →
            g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = t'.G.hom →
            ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx (z ≫ pullback.fst _ _)).U (fun _ => j PUnit.unit)),
              s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
        (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i,
          s'.f i = scal (z ≫ pullback.fst _ _) a i * s.f i) ∧
        ∃ a : T.Frˣ, ∀ i, s.f i = scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i
def SpreadSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
end Formalism.L2.Pj


