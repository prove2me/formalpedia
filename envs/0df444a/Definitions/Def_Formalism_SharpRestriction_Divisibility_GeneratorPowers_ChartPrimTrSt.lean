-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartPrimTrSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:56.247945+00:00
-- url     : https://prove2.me/theorems/204cdbdb-11e4-49b4-aed9-d49841d60506
-- title:
--   Chart Prim Tr St
-- statement:
--   Definitions and structural lemmas for Chart Prim Tr St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartPrimTrSt.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartTransportSt
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def ChartPrimTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (wPT : PrimTyG I.G),
    IsPrimG I.G wPT →
    letI := io.toAlgebra
    ∃ wP : PrimTy H Xo, IsPrim wP ∧
      ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
        (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
          LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
        ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
          LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)
end Formalism.MainNotions.ModuliIntegralCharts.H1


