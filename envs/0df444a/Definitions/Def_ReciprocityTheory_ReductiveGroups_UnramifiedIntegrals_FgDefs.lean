-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:20:51.434429+00:00
-- url     : https://prove2.me/theorems/eb0c31e6-3496-446b-9426-64883f2aba45
-- title:
--   Fg Defs
-- statement:
--   Definitions and structural lemmas for Fg Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgDefs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Theorems.Thm_Formalism_LT_InvIntP_Low_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
section Abstract
variable {K : Type} [NormedField K]
structure LawD (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) : Prop where
  lam0 : constantCoeff lam = 0
  lam1 : coeff 1 lam = 1
  Φ0 : MvPowerSeries.constantCoeff Φ = 0
  Φint : IntegralMv Φ
  log : lam.subst Φ = atX lam + atY lam
structure HD (σ : K →+* K) (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K)
    (a : K) : Prop extends LawD lam Φ where
  A0 : constantCoeff A = 0
  Aint : IntegralPS A
  Alog : lam.subst A = C a * lam
  a_ne : ‖σ a - a‖ = 1
  a_sq : σ (σ a) = a
structure QCls (l : ℕ) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K) (b : K)
    (D : PowerSeries K) : Prop where
  D0 : constantCoeff D = 0
  dInt : IntegralPS (derivative K D)
  add : DivByMv (l : K) (D.subst Φ - atX D - atY D)
  eig : DivBy (l : K) (D.subst A - C b * D)
structure HomCls (l : ℕ) (Φ₁ : MvPowerSeries (Fin 2) K) (A₁ : PowerSeries K)
    (Φ₂ : MvPowerSeries (Fin 2) K) (A₂ : PowerSeries K) (g : PowerSeries K) : Prop where
  g0 : constantCoeff g = 0
  gInt : IntegralPS g
  add : DivByMv (l : K) (g.subst Φ₁ - Φ₂.subst ![atX g, atY g])
  eig : DivBy (l : K) (g.subst A₁ - A₂.subst g)
def desc (l : ℕ) (D : PowerSeries K) : PowerSeries K := PowerSeries.mk fun m => coeff (l * m) D
def d2 (Φ : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) Φ
end Abstract
open Classical in

def lgS {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  if h : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X then h.choose else 0
end ReciprocityTheory.ChartRestriction.L1


