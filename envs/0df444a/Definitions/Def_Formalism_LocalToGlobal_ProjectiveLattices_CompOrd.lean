-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:45.920717+00:00
-- url     : https://prove2.me/theorems/ad7e97cd-470a-4b1a-be7c-65a4fd207189
-- title:
--   Comp Ord
-- statement:
--   Definitions and structural lemmas for Comp Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompOrd.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
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
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def exZ (Dw : Datum H) (G : WTZ E) : Ix Dw → ℤ
  | none => G.2
  | some x => G.1 (x.1, x.2)
def frW (δ : Ix Dw → ℤ) (G : WTZ E) : ℤ := ∑ i, exZ Dw G i * δ i
variable {Z : Comp Xo c}
def ordC (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) (x : AC Z) : ℤ :=
  WithTop.untopD 0 (v (x.coeff G)) + frW δ G
abbrev sgOf (P : Om Z →+* ℂ) : c.F →+* ℂ := P.comp (algebraMap c.F (Om Z))
def PAlg (P : Om Z →+* ℂ) : Om Z →ₐ[c.F] CAt (sgOf P) :=
  { P with commutes' := fun _ => rfl }
def CBase (h : GenFrEx Xo c) (Z : Comp Xo c) (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ P, FrMap (PAlg P) (genFr h Z) (yP P)
def nrmC (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ) : ℝ :=
  ‖P (x.coeff G)‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)
variable (Xo c) in

def FnNe (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop := ∀ σ y i, fn σ y i ≠ 0
section nrm
variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
end nrm
variable (Xo c) in

def FnConj (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ Z (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ),
    nrmC fn (yP Z) G x ((starRingEnd ℂ).comp P) = nrmC fn (yP Z) G x P
end Formalism.L2.Pj


