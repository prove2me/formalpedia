-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:48.310701+00:00
-- url     : https://prove2.me/theorems/11033178-2db9-47b1-89a7-b5d2cff1e52d
-- title:
--   Hk Rel Fr Of Transport Iff
-- statement:
--   Definitions and structural lemmas for Hk Rel Fr Of Transport Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
section Swap
variable {Ω : Type} [CommRing Ω]
def swap (x : Sp Ω ⟶ Xo.X) : Gx x ≅ pullback Xo.univ.t.G.hom x := pullbackSymmetry x Xo.univ.t.G.hom
@[reassoc] theorem swap_hom_fst (x : Sp Ω ⟶ Xo.X) :
    (swap x).hom ≫ pullback.fst _ _ = (snd (Over.mk x) Xo.univ.t.G).left := pullbackSymmetry_hom_comp_fst _ _
@[reassoc] theorem swap_hom_snd (x : Sp Ω ⟶ Xo.X) :
    (swap x).hom ≫ pullback.snd _ _ = (fst (Over.mk x) Xo.univ.t.G).left := pullbackSymmetry_hom_comp_snd _ _
@[reassoc] theorem swap_inv_fst (x : Sp Ω ⟶ Xo.X) :
    (swap x).inv ≫ (fst (Over.mk x) Xo.univ.t.G).left = pullback.snd _ _ := by
  rw [← swap_hom_snd, Iso.inv_hom_id_assoc]
@[reassoc] theorem swap_inv_snd (x : Sp Ω ⟶ Xo.X) :
    (swap x).inv ≫ (snd (Over.mk x) Xo.univ.t.G).left = pullback.fst _ _ := by
  rw [← swap_hom_fst, Iso.inv_hom_id_assoc]
def conj (x x' : Sp Ω ⟶ Xo.X) :
    (pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') ≃ (Gx x ⟶ Gx x') where
  toFun ψ := (swap x).hom ≫ ψ ≫ (swap x').inv
  invFun ψ := (swap x).inv ≫ ψ ≫ (swap x').hom
  left_inv ψ := by simp
  right_inv ψ := by simp
@[reassoc] theorem lift_l_fst {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (fst X Y).left = a.left := by rw [← Over.comp_left, lift_fst]
@[reassoc] theorem lift_l_snd {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (snd X Y).left = b.left := by rw [← Over.comp_left, lift_snd]
@[reassoc] theorem toFib_fst (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} (t : T ⟶ Sp Ω)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : toFib x t a ≫ (fst (Over.mk x) Xo.univ.t.G).left = t :=
  lift_l_fst _ _
@[reassoc] theorem toFib_snd (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} (t : T ⟶ Sp Ω)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) : toFib x t a ≫ (snd (Over.mk x) Xo.univ.t.G).left = a.left :=
  lift_l_snd _ _
@[reassoc] theorem snd_hom (x : Sp Ω ⟶ Xo.X) : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom =
    (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
  (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
def res (x : Sp Ω ⟶ Xo.X) {T T' : Scheme.{0}} {t : T ⟶ Sp Ω} {t' : T' ⟶ Sp Ω} (q : T' ⟶ T) (hq : q ≫ t = t') :
    (Over.mk (t' ≫ x) : Over Xo.X) ⟶ Over.mk (t ≫ x) :=
  Over.homMk q (by simp [← hq])
def sec' (x : Sp Ω ⟶ Xo.X) {T : Scheme.{0}} {t : T ⟶ Sp Ω} (q : Sp Ω ⟶ T) (hq : q ≫ t = 𝟙 _) :
    (Over.mk x : Over Xo.X) ⟶ Over.mk (t ≫ x) :=
  Over.homMk q (by simp [reassoc_of% hq])
end Swap
section Hom
variable {Ω : Type} [CommRing Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
end Hom
section Geom
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'}
end Geom
section Level
end Level
variable {c : Coeff l} {𝔓 : Ideal (𝓞 E)} {p : ℕ}
def ofTransport (tr : Transport Xo c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω)
    (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) : Prop :=
  tr Ω y.x z.x (conj y.x z.x ψ) y.s z.s
end GlobalTheory.HeckeFrCompare


