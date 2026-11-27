-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:32.343367+00:00
-- url     : https://prove2.me/theorems/b01e8a36-dfba-48de-b4ff-a7660532708d
-- title:
--   Adjoint End Pair Mem Gauged Curve Logarithms
-- statement:
--   Definitions and structural lemmas for Adjoint End Pair Mem Gauged Curve Logarithms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithms.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
noncomputable section
namespace GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
section Ord
variable {σ τ : Type}
def ordGe (C : Type) [Field C] (w : τ → ℕ) (n : ℕ) : Submodule C (MvPowerSeries τ C) where
  carrier := {F | ∀ e : τ →₀ ℕ, Finsupp.weight w e < n → coeff e F = 0}
  add_mem' := fun {a b} ha hb e he => by rw [map_add, ha e he, hb e he, add_zero]
  zero_mem' := fun e _ => map_zero _
  smul_mem' := fun c a ha e he => by rw [coeff_smul, ha e he, mul_zero]
end Ord
section Int
variable {V : VF C} {σ τ : Type}
end Int
section Lin
variable {κ : Type} [Fintype κ]
def wz (κ : Type) : Fin 2 × κ → ℕ := fun p => p.1.val
def e0 (κ : Type) : κ ↪ Fin 2 × κ := ⟨fun x => ((0 : Fin 2), x), fun _ _ h => congrArg Prod.snd h⟩
def em (i : κ) (μ : κ →₀ ℕ) : Fin 2 × κ →₀ ℕ := μ.embDomain (e0 κ) + Finsupp.single ((1 : Fin 2), i) 1
def dz (i : κ) : MvPowerSeries (Fin 2 × κ) C →ₗ[C] MvPowerSeries κ C where
  toFun F := fun μ => coeff (em i μ) F
  map_add' F G := by funext μ; exact map_add (coeff (em i μ)) F G
  map_smul' c F := by funext μ; exact map_smul (coeff (em i μ)) c F
end Lin
section Chart
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}
end Chart
end GlobalTheory.RowLaw.CvEnd


