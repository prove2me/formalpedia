-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:08.131067+00:00
-- url     : https://prove2.me/theorems/81dd90d1-8fec-40e9-8957-41721b8efbcb
-- title:
--   Ax HSup
-- statement:
--   Definitions and structural lemmas for Ax HSup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable (Xo c) in

def supR (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : Rul Xo c) : ℝ :=
  supAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f
variable (Xo c) in

def SupBdd (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    Prop :=
  ∀ σ, BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f
variable (Xo c) in

def PTNe : Prop := ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), (PT (Ω := Om Z) σ).Nonempty
def ValAtCx (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ‖P (evC h Z f)‖ = cabs (evR Xo c f (yP Z P))
def NZSome (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∃ Z, evC h Z f ≠ 0
section Pf
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}
end Pf
end Formalism.L2.Pj


