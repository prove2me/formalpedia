-- Prove2me | Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
-- name    : LeanPool_CencovPetz_MonotoneMetric
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:24:43.386447+00:00
-- url     : https://prove2.me/theorems/fe8602f8-baa2-4710-9628-9eda682230c5
-- title:
--   Monotone Metric
-- statement:
--   Definitions and structural lemmas for Monotone Metric, from Adam Benenson; LeanPool contributors's pinned Finite Čencov–Petz uniqueness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/MonotoneMetric.lean

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_comm
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pushforward_le_of_markovMorphism

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.CencovPetz
open scoped BigOperators
universe u
structure MonotoneMetricFamily : Type _ where
  /-- The bilinear form at `p : Simplex α`. -/
  g :
    ∀ {α : Type u} [Fintype α], Simplex α → LinearMap.BilinForm ℝ (tangentSpace (α := α))
  /-- Symmetry of the bilinear form. -/
  symm :
    ∀ {α : Type u} [Fintype α] (p : Simplex α) (u v : tangentSpace (α := α)),
      g (α := α) p u v = g (α := α) p v u
  /-- Positive definiteness on tangent vectors. -/
  pos :
    ∀ {α : Type u} [Fintype α] (p : Simplex α) (u : tangentSpace (α := α)),
      u ≠ 0 → 0 < g (α := α) p u u
  /-- Monotonicity under Markov morphisms. -/
  monotone :
    ∀ {α β : Type u} [Fintype α] [Fintype β] (κ : MarkovMorphism α β) (p : Simplex α)
        (u : tangentSpace (α := α)),
      g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
        g (α := α) p u u
noncomputable def fisherMetricFamily : MonotoneMetricFamily where
  g := fun {α} _ => fisherBilin
  symm := by
    intro α _ p u v
    exact fisherBilin.comm (p := p) u v
  pos := by
    intro α _ p u hu
    exact fisherBilin.pos (p := p) u hu
  monotone := by
    intro α β _ _ κ p u
    exact fisherBilin_pushforward_le_of_markovMorphism (κ := κ) p u
end LeanPool.CencovPetz


