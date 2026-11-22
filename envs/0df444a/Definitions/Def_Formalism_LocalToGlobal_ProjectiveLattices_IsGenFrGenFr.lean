-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:43.751799+00:00
-- url     : https://prove2.me/theorems/2ffec22b-c18a-43e0-bb8f-bf770d56c8f0
-- title:
--   Is Gen Fr Gen Fr
-- statement:
--   Definitions and structural lemmas for Is Gen Fr Gen Fr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsGenFrGenFr.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
abbrev Comp : Type := irreducibleComponents (Xo.XF c)
variable {Xo c}
def genPt (Z : Comp Xo c) : Xo.XF c := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).genericPoint
abbrev kap (Z : Comp Xo c) : Type := (Xo.XF c).residueField (genPt Z)
abbrev strK : Xo.XF c ⟶ Sp c.F := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
def genSp (Z : Comp Xo c) : Spec ((Xo.XF c).residueField (genPt Z)) ⟶ Xo.XF c :=
  (Xo.XF c).fromSpecResidueField (genPt Z)
instance algKap (Z : Comp Xo c) : Algebra c.F (kap Z) :=
  (Spec.preimage (genSp Z ≫ strK)).hom.toAlgebra
def xGen (Z : Comp Xo c) : Sp (kap Z) ⟶ Xo.X :=
  genSp Z ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
abbrev FlagVar (Dw : Datum H) : Type := Σ τ : E →+* ℂ, {p : Fin (Dw.mult τ) × Fin (Dw.mult τ) // p.1 < p.2}
abbrev Om (Z : Comp Xo c) : Type := FractionRing (MvPolynomial (FlagVar Dw) (kap Z))
def genCoef (Z : Comp Xo c) (τ : E →+* ℂ) (i j : Fin (Dw.mult τ)) : Om Z :=
  if h : i < j then algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X ⟨τ, ⟨(i, j), h⟩⟩)
  else if i = j then 1 else 0
def IsGenFr (Z : Comp Xo c) (y : FrPt Xo c (Om Z)) : Prop :=
  y.x = spMap (algebraMap (kap Z) (Om Z)) ≫ xGen Z ∧
    ∃ y₀ : FrPt Xo c (kap Z), y₀.x = xGen Z ∧
      ∀ τ i, IsCombAt y.x (fun j => spMap (dualMap (algebraMap (kap Z) (Om Z))) ≫ y₀.u τ j)
        (genCoef Z τ i) (y.u τ i)
variable (Xo c) in

def GenFrEx : Prop := ∀ Z : Comp Xo c, ∃ y : FrPt Xo c (Om Z), IsGenFr Z y
def genFr (h : GenFrEx Xo c) (Z : Comp Xo c) : FrPt Xo c (Om Z) := (h Z).choose
def evC (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : Om Z := evR Xo c f (genFr h Z)
variable (Xo c) in

def GenFromTest (h : GenFrEx Xo c) : Prop := ∀ Z : Comp Xo c,
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)
end Formalism.L2.Pj


