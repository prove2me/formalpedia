-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:07.912831+00:00
-- url     : https://prove2.me/theorems/54ac2c7f-7f34-5046-8006-fbd1946e130f
-- title:
--   Gen Fr Pf B
-- statement:
--   Definitions and structural lemmas for Gen Fr Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def gfpEig {L : Type} [Field L] [Algebra c.F L] {x : Sp L ⟶ Xo.X} {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
    (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) : Submodule L (Fin n → L) :=
  eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a))
section BC
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
variable [Algebra c.F L]
end BC
end Formalism.L2.Pj


