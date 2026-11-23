-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:34.924832+00:00
-- url     : https://prove2.me/theorems/3b294f7c-ace6-4241-9fd0-ff15e86fd84c
-- title:
--   Cas Val K
-- statement:
--   Definitions and structural lemmas for Cas Val K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/CasValK.lean

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
variable {n : ℕ}
section Alg
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def layer (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    ℕ → Submodule ℂ M
  | 0 => V
  | k + 1 => layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
end Alg
def IsNCSum (ε : Fin n → Bool) (k : ℕ) (ν : Fin n → ℝ) : Prop :=
  ∃ γ : Fin k → Fin n × Fin n, (∀ i, ε (γ i).1 ≠ ε (γ i).2) ∧ ν = ∑ i, root (γ i).1 (γ i).2
def casValK (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + rhoC ε) - nsq (rhoC ε)
end ReciprocityTheory.ChartRestriction.DS


