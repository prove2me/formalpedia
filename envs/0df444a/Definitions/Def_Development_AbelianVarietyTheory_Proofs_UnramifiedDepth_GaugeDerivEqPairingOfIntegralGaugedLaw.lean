-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:05.026808+00:00
-- url     : https://prove2.me/theorems/a58c519b-bd6e-55c9-bd9f-c034f0936299
-- title:
--   Gauge Deriv Eq Pairing Of Integral Gauged Law
-- statement:
--   Definitions and structural lemmas for Gauge Deriv Eq Pairing Of Integral Gauged Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
namespace GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
def tder [Fintype σ] (p w : σ → MvPowerSeries τ C) (f : MvPowerSeries σ C) : MvPowerSeries τ C :=
  ∑ s, subst p (pderiv C s f) * w s
section
variable [Fintype σ] {p : σ → MvPowerSeries τ C} (hp : ∀ s, constantCoeff (p s) = 0) (w : σ → MvPowerSeries τ C)
include hp
end
end GlobalTheory.RowLaw.GaugeDeriv
end
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
namespace GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
def pr (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun p => if p.1 = 0 then a p.2 else b p.2
def tr (a b c : κ → MvPowerSeries τ C) : Fin 3 × κ → MvPowerSeries τ C :=
  fun p => ![a, b, c] p.1 p.2
def invF (Y : RawChart C d I κ) (v : κ → C) (y : κ → MvPowerSeries τ C) : κ → MvPowerSeries τ C :=
  fun i => tder (fun x => subst y (Y.lg x)) (fun x => MvPowerSeries.C (v x)) (Y.ex i)
section
variable (R : RLaw Y V)
include R
end
end GlobalTheory.RowLaw.GaugeDeriv
end
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
namespace GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
section
variable (R : RLaw Y V)
include R
variable {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
  (hai : ∀ i, IntS V (a i)) (hbi : ∀ i, IntS V (b i))
include ha hb hai hbi
variable {v : κ → C} (hv : ∀ i, V.Ge 0 (v i))
include hv
end
end GlobalTheory.RowLaw.GaugeDeriv
end
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
namespace GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
section
variable {I₁ J₁ : Type} [Fintype I₁] [Fintype J₁] {G : Cart V d I₁ J₁} (S : Sys G) {t : I₁ → MvPowerSeries I₁ C}
  (ht : S.IsT t)
include ht
end
end GlobalTheory.RowLaw.GaugeDeriv
end
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
namespace GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
end GlobalTheory.RowLaw.GaugeDeriv
namespace GlobalTheory.RowLaw
open GaugeDeriv
end GlobalTheory.RowLaw


