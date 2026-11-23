-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:17.904311+00:00
-- url     : https://prove2.me/theorems/f969fe14-4d32-4974-9b0d-f9f9fd74e320
-- title:
--   Gauge Uniq C
-- statement:
--   Definitions and structural lemmas for Gauge Uniq C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GaugeUniqC.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
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
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
namespace GaugeR
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
@[reducible] def barStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive a := by
    apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  star_mul a b := by
    show H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, mul_comm]
  star_add a b := map_add H.bar a b
variable {H : Host E} {Dw : Datum H} {l : Level H}
def chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ : E →+* ℂ) : 𝓞 E →+* S :=
  (algebraMap c.F S).comp (embK c σ)
def nu (Dw : Datum H) : Lt1 Dw ≃ Fin 1 × Fin (dL Dw) where
  toFun ℓ := ((0 : Fin 1), ltIdx Dw ℓ)
  invFun p := (ltIdx Dw).symm p.2
  left_inv ℓ := by simp
  right_inv p := Prod.ext (Subsingleton.elim _ _) (by simp)
def sc (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → S :=
  fun p => algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)
end GaugeR
end Formalism.MainNotions.ModuliIntegralCharts.H1


