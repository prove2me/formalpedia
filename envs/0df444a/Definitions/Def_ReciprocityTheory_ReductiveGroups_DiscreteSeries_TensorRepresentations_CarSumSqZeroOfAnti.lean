-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:19.818518+00:00
-- url     : https://prove2.me/theorems/46664764-b1ee-4fde-bbbd-86c8f9707dda
-- title:
--   Car Sum Sq Zero Of Anti
-- statement:
--   Definitions and structural lemmas for Car Sum Sq Zero Of Anti, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CarSumSqZeroOfAnti.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
def IsCAR (cp cm : Fin n → Fin n → Module.End ℂ W) : Prop :=
  ∀ i a j b : Fin n, cp i a * cp j b + cp j b * cp i a = 0 ∧ cm i a * cm j b + cm j b * cm i a = 0 ∧
    cm i a * cp j b + cp j b * cm i a = if i = j ∧ a = b then 1 else 0
def CommutesCAR (E cp cm : Fin n → Fin n → Module.End ℂ W) : Prop :=
  ∀ a b i j : Fin n, E a b * cp i j = cp i j * E a b ∧ E a b * cm i j = cm i j * E a b
def plusIdx (ε : Fin n → Bool) : Finset (Fin n) := univ.filter fun a => ε a = true
def minusIdx (ε : Fin n → Bool) : Finset (Fin n) := univ.filter fun a => ε a = false
def sgE (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) : Module.End ℂ W :=
  if ε a = true ∧ ε b = true then ∑ x ∈ minusIdx ε, cp a x * cm b x
  else if ε a = false ∧ ε b = false then -∑ i ∈ plusIdx ε, cp i b * cm i a
  else 0
def diagE (ε : Fin n → Bool) (E cp cm : Fin n → Fin n → Module.End ℂ W) (a b : Fin n) : Module.End ℂ W :=
  E a b + sgE ε cp cm a b
def dOp (ε : Fin n → Bool) (E cp : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E a i * cp i a
def dOp' (ε : Fin n → Bool) (E cm : Fin n → Fin n → Module.End ℂ W) : Module.End ℂ W :=
  -∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * cm i a
def rhoHol (ε : Fin n → Bool) : Fin n → ℝ := fun a => if ε a then (qOf ε : ℝ) / 2 else -(pOf ε : ℝ) / 2
end ReciprocityTheory.ChartRestriction.DS


