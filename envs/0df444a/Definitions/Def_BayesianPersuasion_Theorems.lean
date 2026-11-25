-- Prove2me | Definitions.Def_BayesianPersuasion_Theorems
-- name    : BayesianPersuasion_Theorems
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:03:42.173751+00:00
-- url     : https://prove2.me/theorems/e4779081-3fe6-40db-afdd-b2a0bb5dac47
-- title:
--   Theorems
-- statement:
--   Definitions and structural lemmas for Theorems, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; portions adapted from Daniel Lyng Econlib (Apache-2.0; see pinned LICENSE and source headers)'s pinned Optimal information and concavification in Bayesian persuasion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Theorems.lean

module
public import Definitions.Def_BayesianPersuasion_Attainment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe uΩ uA
open Set Finset
namespace BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω] [Nonempty Ω]
variable [MetricSpace A] [CompactSpace A] [Nonempty A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
namespace Proof
end Proof
end BayesianPersuasion


