-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
-- name    : GroundTheory_PAdicHodge_FieldOfNormsTower
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:21.317719+00:00
-- url     : https://prove2.me/theorems/14515250-b35c-429c-89ae-9a48141e1cae
-- title:
--   Field Of Norms Tower
-- statement:
--   Definitions and structural lemmas for Field Of Norms Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FieldOfNormsTower.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
section Nrm
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
def nrm (x : Ω) : ℝ :=
  letI := normedField K
  spectralNorm K Ω x
variable {K}
variable [ValuativeRel Ω] [ValuativeExtension K Ω]
variable [TopologicalSpace Ω] [IsValuativeTopology Ω]
end Nrm
section Estimates
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {p : ℕ}
end Estimates
section Tower
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
structure NormTower where

  E : ℕ → IntermediateField K Ω
  mono : Monotone E
  finiteDimensional : ∀ n, FiniteDimensional K (E n)

  T : ℕ → Finset Gal(Ω/K)
  fix : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E n, σ x = x
  prod_mem : ∀ n, ∀ y ∈ E (n + 1), (∏ σ ∈ T n, σ y) ∈ E n

  k : ℕ → ℕ
  card_alt : ∀ n, (T n).card = p ^ k n
  frequently_ne_zero : ∀ n, ∃ m, n ≤ m ∧ k m ≠ 0

  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  step : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E (n + 1), nrm K (σ x - x) ≤ c * nrm K x
  prime : p.Prime
  nrm_p_lt_one : nrm K (p : Ω) < 1

  value : ℕ → ℝ
  value_pos : ∀ n, 0 < value n
  value_lt_one : ∀ n, value n < 1
  exists_value : ∀ n, ∃ π ∈ E n, nrm K π = value n
  value_zpow : ∀ n, ∀ y ∈ E n, y ≠ 0 → ∃ j : ℤ, nrm K y = value n ^ j
  value_succ : ∀ n, value (n + 1) ^ (p ^ k n) = value n
namespace NormTower
variable {K Ω p} (t : NormTower K Ω p)
def N (n : ℕ) (y : Ω) : Ω :=
  ∏ σ ∈ t.T n, σ y
def ρ : ℝ :=
  max t.c (nrm K (p : Ω))
end NormTower
end Tower
end GroundTheory.PAdicHodge


