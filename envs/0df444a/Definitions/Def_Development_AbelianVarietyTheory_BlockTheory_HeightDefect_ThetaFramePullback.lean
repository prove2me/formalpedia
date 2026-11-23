-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_ThetaFramePullback
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_ThetaFramePullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:38.012751+00:00
-- url     : https://prove2.me/theorems/02cb1120-c5d8-4a9b-9021-56453861dc21
-- title:
--   Theta Frame Pullback
-- statement:
--   Definitions and structural lemmas for Theta Frame Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/ThetaFramePullback.lean

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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaFramePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Notions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def IsGenOver {V : Type} [CommRing V] (G : SAB H (Sp V)) (θ : LB.Sec G.PP.L) : Prop :=
  ∀ σ : LB.Sec G.PP.L, ∃! a : V, ∀ i,
    σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ V a)) * θ.f i
variable {Xo : Moduli Dw l}
def IsGenAt {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) : Prop :=
  ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s.f i
def GenMatch {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    (m₁ : SABMap t' Xo.univ.t x) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx x)) : Prop :=
  ∃ (w₁ : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w₂ : LB.Iso t'.PP.L (G.PP.L.pull m₂.φ))
    (σ : LB.Sec t'.PP.L) (s₁ : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ₂ : LB.Sec (G.PP.L.pull m₂.φ)),
    RigIso m₁ w₁ ∧ RigIso m₂ w₂ ∧ IsoMaps w₁ σ s₁ ∧ IsoMaps w₂ σ θ₂ ∧ PullSec m₂.φ θ θ₂ ∧
    ∀ g : t'.G.left ⟶ Gx x, g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m₁.φ →
      g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s₁.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))
variable {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def GenericIn (Y : Model Xo c β) {T : CDVR} (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c)
    (x : Sp T.Fr ⟶ Xo.X) : Prop :=
  xF ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ ξ ∧ xF ≫ pullback.fst _ _ = x
def Tied (Y : Model Xo c β) {T : CDVR} {ξ : Sp T.V ⟶ Y.X} (xF : Sp T.Fr ⟶ Xo.XF c) {x : Sp T.Fr ⟶ Xo.X}
    {G : SAB H (Sp T.V)} (mG : SABMap G Y.t ξ) {t' : SAB H (Sp T.Fr)} (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : Prop :=
  ∃ n : t'.G.left ⟶ Y.oF.t.G.left, n ≫ Y.oF.t.G.hom = t'.G.hom ≫ xF ∧ n ≫ Y.m0.toSABMap.φ = m₁.φ ∧
    n ≫ Y.m.φ = m₂.φ ≫ mG.φ
def IsPushGenOn {X : Scheme.{0}} (G : Over X) (L : LB G.left) (V : X.Opens)
    (θ₀ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop :=
  θ₀ ∈ secOn L (G.hom ⁻¹ᵁ V) ∧
    ∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Γ(X, W), ∀ i,
      s i = (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom a *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ₀ i)
def IsPullOf {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (V : S.Opens)
    (θ₀ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ V ⊓ t.PP.L.U i)) (θ : LB.Sec t'.PP.L) : Prop :=
  ∃ (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (θ₁ : LB.Sec (t.PP.L.pull m.φ)), RigIso m w ∧ IsoMaps w θ θ₁ ∧
    ∀ j (h : (t.PP.L.pull m.φ).U j ≤ m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ V ⊓ t.PP.L.U (j PUnit.unit))),
      θ₁.f j = (m.φ.appLE _ _ h).hom (θ₀ (j PUnit.unit))
end Notions
def GenericFibre : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (mG : SABMap G Y.t ξ),
      (∃ t' : SAB H (Sp T.Fr), Nonempty (SABMap t' G (spMap (algebraMap T.V T.Fr)))) ∧
      ∀ (t' : SAB H (Sp T.Fr)) (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))),
        ∃ m₁ : SABMap t' Xo.univ.t x, Tied Y xF mG m₁ m₂
def ThetaFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (_ : SABMap G Y.t ξ),
      ∃ θ : LB.Sec G.PP.L, IsGenOver G θ ∧
        ∀ (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
          (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))),
          ∃ s : LB.Sec (PPx x), GenMatch m₁ m₂ θ s ∧ IsGenAt x s ∧
            ∀ s₀ : LB.Sec (PPx x), IsGenAt x s₀ →
              ∃ u : T.Frˣ, ∀ i, s.f i = scal x (u : T.Fr) i * s₀.f i
def PullsBack : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L →
    ∀ (T : CDVR) (ξ : Sp T.V ⟶ Y.X) (xF : Sp T.Fr ⟶ Xo.XF c) (x : Sp T.Fr ⟶ Xo.X), GenericIn Y ξ xF x →
    ∀ (G : SAB H (Sp T.V)) (mG : SABMap G Y.t ξ) (V : Y.X.Opens)
      (θ₀ : ∀ i, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ V ⊓ Y.t.PP.L.U i)),
      ⊤ ≤ ξ ⁻¹ᵁ V → IsPushGenOn Y.t.G Y.t.PP.L V θ₀ →
      (∃ θ, IsPullOf mG V θ₀ θ) ∧ ∀ θ, IsPullOf mG V θ₀ θ → IsGenOver G θ
def Claim : Prop := ThetaFrame ∧ GenericFibre
section Basic₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
example {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : IsGenAt y.x y.s := y.gen
example (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (h : Integral T io y) :
    letI := io.toAlgebra
    ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t y.x)
      (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L),
      IsGenOver G θ ∧ GenMatch m₁ m₂ θ y.s := by
  obtain ⟨G, t', m₁, m₂, -, θ, h₁, h₂⟩ := h
  exact ⟨G, t', m₁, m₂, θ, h₁, h₂⟩
example {X : Scheme.{0}} (G : Over X) (L : LB G.left) (h : PushInvertible G L) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ θ₀, IsPushGenOn G L V θ₀ := by
  obtain ⟨V, hV, θ, h₁, h₂, -⟩ := h x
  exact ⟨V, hV, θ, h₁, h₂⟩
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaFramePullback


