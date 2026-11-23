-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniq
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:00.714346+00:00
-- url     : https://prove2.me/theorems/c923874c-a106-4f3f-92a4-67d826b67328
-- title:
--   Gauge Uniq
-- statement:
--   Definitions and structural lemmas for Gauge Uniq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniq.lean

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
def GaugeUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
    (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G), IsExpChart y x →
    ∀ e e' : ∀ m, ExpFr y x m, IsExpGauge y x e → IsExpGauge y x e' →
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
        (f f' : MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
        IsExpGerm y x e k F f → IsExpGerm y x e' k F f' →
          f' = f * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)
end Formalism.MainNotions.ModuliIntegralCharts.H1


