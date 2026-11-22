-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:59:51.721569+00:00
-- url     : https://prove2.me/theorems/feabe5b9-631c-4f87-aaed-3f55778fc698
-- title:
--   Rigid Arc
-- statement:
--   Definitions and structural lemmas for Rigid Arc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigidArc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
def ArcIn.restrict {k : Type} [CommRing k] [IsDomain k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)
    {O : Type} [CommRing O] (β : O →+* c.F) : ArcIn D l β k (bF.comp β) :=
  { a with geom := fun F _ _ _ r z => a.geom F (β r) (β z) }
def ArcWit.Agree {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
    {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (ψ : W.t.G ≅ W'.t.G) : Prop :=
  IsMonHom ψ.hom ∧ (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
  (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
    g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
    g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) ∧
  ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G) (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
    wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
      (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) ∧
    ∀ (n : ℕ) (ψn : (Out.thickObj (PowerSeries k) (Ideal.span {PowerSeries.X}) n W.t.G).left ⟶
        (Out.thickObj (PowerSeries k) (Ideal.span {PowerSeries.X}) n W'.t.G).left),
      ψn = ((Over.pullback (Out.thick (PowerSeries k) (Ideal.span {PowerSeries.X}) n)).map ψ.hom).left →
      ((W.P.U.gt n).pG.left ≫ W.φ = ψn ≫ (W'.P.U.gt n).pG.left ≫ W'.φ) ∧
      ∀ (A : Type) [CommRing A] [IsLocalRing A]
        (v : Sp A ⟶ (Out.thickObj (PowerSeries k) (Ideal.span {PowerSeries.X}) n W.t.G).left),
        (∀ (x : a.D₀.X) (pt₀ : Fin 4 → (Sp A ⟶ a.D₀.P.A.left)) (t₀ : LB.Gen (LB.LinComb a.D₀.P.L pt₀ Out.Oinvε)),
          t₀.IsGen → GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) v) t₀ →
          GenRelR W'.w (LB.pullGen _ _ _ ((W'.P.U.gt n).t (W'.e x)) (v ≫ ψn)) t₀) ∧
        ∀ (j₀ : a.D₀.P.L.ι) (jM : W.P.D.toPre.P.L.ι) (jM' : W'.P.D.toPre.P.L.ι) (jL : W.P.U.LG.L.ι)
          (jL' : W'.P.U.LG.L.ι),
          ⊤ ≤ (v ≫ (W.P.U.gt n).pG.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) →
          ⊤ ≤ (v ≫ ψn ≫ (W'.P.U.gt n).pG.left) ⁻¹ᵁ
            (LB.div (a.D₀.P.L.pull W'.φ) W'.P.D.toPre.P.L).U (fun _ => j₀, jM') →
          ⊤ ≤ (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) ⁻¹ᵁ
            (LB.div (W'.P.U.LG.L.pull ψ.hom.left) W.P.U.LG.L).U (fun _ => jL', jL) →
          valR (v ≫ (W.P.U.gt n).pG.left) _ (W.w.s (fun _ => j₀, jM)).val *
              valR v _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL)).val =
            valR (v ≫ ψn ≫ (W'.P.U.gt n).pG.left) _ (W'.w.s (fun _ => j₀, jM')).val *
              valR (v ≫ ψn) _ ((W'.P.U.w n).s (fun _ => jM', fun _ => jL')).val *
              valR (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) _ (wL.s (fun _ => jL', jL)).val
def RigidArc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β')
    (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
    y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ' →
    y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y' ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y = y' ∧ ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


