-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:46.272096+00:00
-- url     : https://prove2.me/theorems/39043340-7993-4b85-a34b-8b930a54ec52
-- title:
--   Action Converges Ladic Cauchy And Star
-- statement:
--   Definitions and structural lemmas for Action Converges Ladic Cauchy And Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_two
import Theorems.Thm_GlobalTheory_GaugeAdjoint_constantCoeff_ev
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_two
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.ActionLimit
open MvPowerSeries GlobalTheory.GaugeAdjoint
section Bound
variable {C : Type} [Field C] {V : VF C} {σ τ : Type}
def Low (V : VF C) (D : ℕ) (w : ℝ) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ : τ →₀ ℕ, μ.degree ≤ D → V.Ge w (coeff μ g)
def Cong (V : VF C) (D : ℕ) (w : ℝ) (g h : MvPowerSeries τ C) : Prop :=
  Low V D 0 g ∧ Low V D 0 h ∧ Low V D w (g - h)
end Bound
section Log
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)
theorem log_act_add (a b : O) :
    comp1 Y.lg (Y.B.A.act (a + b)) = comp1 Y.lg (Y.B.A.act a) + comp1 Y.lg (Y.B.A.act b) := by
  funext i
  have hab := const_two (Y.B.A.const a) (Y.B.A.const b)
  have h := congrArg (ev (n := 1) ![Y.B.A.act a, Y.B.A.act b]) (Y.lg_add i)
  have hF : ∀ j, constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j) = 0 := fun j => by
    rw [addOf, constantCoeff_ev (const_two (const_pt 0) (const_pt 1)), Y.B.G.const]
  have e0 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (pt C dd (0 : Fin 2) j)) = Y.B.A.act a :=
    funext fun j => ev_pt hab 0 j
  have e1 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (pt C dd (1 : Fin 2) j)) = Y.B.A.act b :=
    funext fun j => ev_pt hab 1 j
  have e2 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b]
      (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j)) = Y.B.A.act (a + b) := by
    funext j
    rw [addOf, ev_ev_two (const_pt 0) (const_pt 1) hab, e0, e1, Y.B.A.add_act]
    rfl
  have hadd : ∀ f g : PS C 2 dd, ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (f + g) =
      ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] f + ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] g :=
    fun f g => subst_add (hasSubst_pts hab) f g
  rw [hadd, ev_ev_one hF hab, ev_ev_one (const_pt 0) hab, ev_ev_one (const_pt 1) hab, e0, e1, e2] at h
  exact h
noncomputable def logAct : O →+ Pt C 1 dd :=
  AddMonoidHom.mk' (fun a => comp1 Y.lg (Y.B.A.act a)) (log_act_add Y)
end Log
end GlobalTheory.ActionLimit


