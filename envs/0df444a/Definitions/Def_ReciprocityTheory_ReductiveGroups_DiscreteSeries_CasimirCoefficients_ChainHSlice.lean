-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:41.380804+00:00
-- url     : https://prove2.me/theorems/f59f6eea-d3a1-5427-9fbf-fe22ab7a30c5
-- title:
--   Chain HSlice
-- statement:
--   Definitions and structural lemmas for Chain HSlice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ChainHSlice.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
section Chains
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def opL (c : ℂ) (X : 𝕄) (F : 𝕄 → E) : 𝕄 → E := fun z => c • F z + Lhol X F z
def chainL {m : ℕ} (s : Fin m → ℂ × 𝕄) (F : 𝕄 → E) : 𝕄 → E :=
  (List.ofFn fun i => opL (s i).1 (s i).2).foldr (fun t h => t h) F
def sσ (u : ℂ) (σ : Equiv.Perm (Fin n)) : Fin n → ℂ × 𝕄 :=
  fun i => (if σ i = i then u - ((i : ℕ) : ℂ) else 0, -(Matrix.single (σ i) i 1))
end Chains
def opH (c : ℂ) (X : 𝕄) (g : 𝕋 → ℂ) : 𝕋 → ℂ := fun p => c • g p + GPs.DH X g p
def chainH {m : ℕ} (s : Fin m → ℂ × 𝕄) (g : 𝕋 → ℂ) : 𝕋 → ℂ :=
  (List.ofFn fun i => opH (s i).1 (s i).2).foldr (fun t h => t h) g
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
end CapPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
end ReciprocityTheory.ChartRestriction.DS.S7


