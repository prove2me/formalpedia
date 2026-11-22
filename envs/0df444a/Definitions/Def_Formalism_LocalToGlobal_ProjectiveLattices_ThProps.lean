-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ThProps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:30.527319+00:00
-- url     : https://prove2.me/theorems/b44df759-fdc1-4b29-80e1-7d7353bd9d90
-- title:
--   Th Props
-- statement:
--   Definitions and structural lemmas for Th Props, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ThProps.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
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
namespace Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def ThValTot (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∃! v, ThValAt Xo c nab y x P v
def LastPos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, InPsi H τ → 0 < Dw.mult τ → 0 < a (τ, Dw.mult τ - 1)
def ThInCusp (nab : NabV Xo c)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a →
    ∀ f ∈ thGen Xo c nab a n, f ∈ cusp a n
def DF (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)
def ThNe0 (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 0 < n → Dw.p + Dw.q ≤ n → DF Dw a + 2 ≤ l.M →
    (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) → ∃ f ∈ thGen Xo c nab a n, f ≠ 0
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

def NabZero (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ)
    (F : LB.Sec (ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))),
    ReciprocityTheory.ChartRestriction.G.Out.IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F 1
      (ReciprocityTheory.ChartRestriction.G.Out.rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) k)
      (toΓ S (nab y k F 0))
end Formalism.L2.Pj


