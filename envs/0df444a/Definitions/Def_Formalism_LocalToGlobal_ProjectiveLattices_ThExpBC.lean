-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:28.835095+00:00
-- url     : https://prove2.me/theorems/0ca94dcf-e8c7-4bc3-a021-e59d70a30516
-- title:
--   Th Exp BC
-- statement:
--   Definitions and structural lemmas for Th Exp BC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ThExpBC.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def ExpBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S')
    (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' →
    ∀ (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) (e : ∀ m, ExpFr y x m), IsExpChart y x → IsExpGauge y x e →
    ∃ (x' : ∀ m, jO y' (dL Dw) m 1 ⟶ Xo.univ.t.G) (e' : ∀ m, ExpFr y' x' m),
      IsExpChart y' x' ∧ IsExpGauge y' x' e' ∧
      ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom →
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y'.x))) (g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
        IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' →
        IsExpGerm y x e k F g → IsExpGerm y' x' e' k F' (MvPowerSeries.map ψ.toRingHom g)
end Formalism.L2.Pj


