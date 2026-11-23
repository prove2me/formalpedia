-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:24.898323+00:00
-- url     : https://prove2.me/theorems/0e657462-0354-4387-83c2-31756167e5db
-- title:
--   Hecke Fr
-- statement:
--   Definitions and structural lemmas for Hecke Fr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/HeckeFr.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeStabSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
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
def hkKer (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) :
    Type :=
  {C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y.x) Dw 𝔓 p i C}
def IsHkIsog {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) (y y'' : Sp Ω ⟶ Xo.X)
    (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)) : Prop :=
  y'' ≫ Xo.s = y ≫ Xo.s ∧ ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
    (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
    Function.Surjective ψp ∧ ψp.ker = C ∧
    (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (u : Ωˣ), n.Coprime p →
      ReciprocityTheory.ChartRestriction.G.Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn u) →
      ReciprocityTheory.ChartRestriction.G.Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (u ^ (p ^ 2)))) ∧
    ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
      ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
      ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a
def IsLieImageH {Ω : Type} [Field Ω] (p : ℕ) {y y'' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (v v' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber Ω) ⟶ pullback Xo.univ.t.G.hom y,
    w ≫ pullback.fst _ _ = v ∧ w ≫ pullback.snd _ _ = spMap (algebraMap Ω (DualNumber Ω)) ∧
      v' = spMap (epsMul ((p : Ω)⁻¹)) ≫ w ≫ ψ ≫ pullback.fst _ _
def HkPt (p : ℕ) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (sTr : ∀ (y z : FrPt Xo c Ω), (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (y : FrPt Xo c Ω) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)) (z : FrPt Xo c Ω) : Prop :=
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)),
    IsHkIsog p y.x z.x C ψ ψp ∧ (∀ τ j, IsLieImageH p ψ (y.u τ j) (z.u τ j)) ∧ sTr y z ψ
def hkRelFr (𝔓 : Ideal (𝓞 E)) (p i : ℕ)
    (sTr : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω),
      (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) 𝔓 p i Ω y)
    (z : FrPt Xo c Ω) : Prop :=
  HkPt p (sTr Ω) y C.1 z
end Formalism.L2.Pj


