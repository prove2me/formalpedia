-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:02.891273+00:00
-- url     : https://prove2.me/theorems/80d5a988-1b93-494e-accf-1130f00fbd5c
-- title:
--   Is Lev Move
-- statement:
--   Definitions and structural lemmas for Is Lev Move, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsLevMove.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
def CubIso {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec Xo.univ.t.G) (fun _ => 1)) Xo.univ.t.PP.rig
      (ν.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε) Xo.univ.t.cub.t
      (ν.cm.thetaPull Xo.univ.t.PP.L Xo.univ.t.cub.t)
def IsLevMove (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ρ ≫ Xo.s = Xo.s ∧
    (∀ a, (Xo.univ.eta (gM a)).left ≫ ν.φ = ρ ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo.univ.etaA (gA a)).left ≫ ν.φ = ρ ≫ (Xo.univ.etaA a).left)
def FrMove {S : Type} [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (y y' : FrPt Xo c S) : Prop :=
  y'.x = y.x ≫ ρ ∧
    (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧
    ∃ (pm : Gx y.x ⟶ Gx y'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
      pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
      pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ ∧
      CubIso ν w ∧
      ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx y.x).Opens),
        W = (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) →
        ∀ (h₀ : W ≤ (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
              ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)))
          (h₁ : W ≤ pm ⁻¹ᵁ (PPx y'.x).U (fun _ => i)) (h₂ : W ≤ (PPx y.x).U (fun _ => j)),
        (pm.appLE ((PPx y'.x).U (fun _ => i)) W h₁).hom (y'.s.f (fun _ => i)) =
          ((snd (Over.mk y.x) Xo.univ.t.G).left.appLE
              ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) W h₀).hom
              (Units.val (w.s ((fun _ => i), j))) *
            ((Gx y.x).presheaf.map (homOfLE h₂).op).hom (y.s.f (fun _ => j))
def levR (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : Prop :=
  ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), IsIso ρ ∧ IsLevMove ρ ν g.1 g.2 ∧ FrMove ρ ν y y'
def levActR {G : Type} (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (gm : G) {S : Type} [CommRing S]
    [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  levR (Xo := Xo) (c := c) (lev gm) y y'
end Formalism.L2.Pj


