-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:30.70793+00:00
-- url     : https://prove2.me/theorems/e24682c0-da97-42f0-ab4e-711acdf2c9b5
-- title:
--   Ps Word
-- statement:
--   Definitions and structural lemmas for Ps Word, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/KTypeLemma/PsWord.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
def mmul (A B : 𝕄) : 𝕄 := Matrix.of A * Matrix.of B
def PhiQ (μ : Fin n → ℤ) : 𝕄 → ℂ := fun y => PhiM μ y
def Om : Set WW := {q | q.2 ∈ OmegaSet n}
def Fw (μ : Fin n → ℤ) (D : List MM) (q : WW) : ℂ :=
  lWord (D.map fun Z => mmul (mmul q.1.1 Z) q.1.2) (PhiM μ) q.2
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
def psi (k : KG ε) (z : 𝕄) : WW := ((toMK k⁻¹, toMK k), mmul (mmul (toMK k⁻¹) z) (toMK k))
def dpsi (k : KG ε) : 𝕄 →L[ℂ] WW :=
  (0 : 𝕄 →L[ℂ] 𝕄 × 𝕄).prod (Ps1.conjCLM (toMK k⁻¹) (toMK k))
def cc (T : KType ε Λ) : ℂ := (Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)
def G (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) (z : 𝕄) (k : KG ε) : T.V →L[ℂ] T.V :=
  Fw μ D (psi k z) • (T.op k * projW T * T.op k⁻¹)
def G' (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) (z : 𝕄) (k : KG ε) :
    𝕄 →L[ℂ] (T.V →L[ℂ] T.V) :=
  ((fderiv ℂ (Fw μ D) (psi k z)).comp (dpsi k)).smulRight (T.op k * projW T * T.op k⁻¹)
end PsW
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK


