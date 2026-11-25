-- Prove2me | Definitions.Def_BayesianPersuasion_Primitives
-- name    : BayesianPersuasion_Primitives
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:54:46.022192+00:00
-- url     : https://prove2.me/theorems/af368a35-ec3f-4b83-8bb8-4225d95ddc1e
-- title:
--   Primitives
-- statement:
--   Definitions and structural lemmas for Primitives, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; portions adapted from Daniel Lyng Econlib (Apache-2.0; see pinned LICENSE and source headers)'s pinned Optimal information and concavification in Bayesian persuasion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Primitives.lean

module
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Order.Compact
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe uΩ uA
open Set Finset
namespace BayesianPersuasion
variable (Ω : Type uΩ) [Fintype Ω]
abbrev Belief := {p : Ω → ℝ // (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1}
variable {Ω} {A : Type uA}
def expected (u : A → Ω → ℝ) (p : Belief Ω) (a : A) : ℝ :=
  ∑ ω, p.val ω * u a ω
def BestReply (u : A → Ω → ℝ) (p : Belief Ω) (a : A) : Prop :=
  ∀ b, expected u p b ≤ expected u p a
def SenderPreferred (u v : A → Ω → ℝ) (p : Belief Ω) (a : A) : Prop :=
  BestReply u p a ∧ ∀ b, BestReply u p b → expected v p b ≤ expected v p a
noncomputable def senderPayoff (u v : A → Ω → ℝ) (p : Belief Ω) : ℝ :=
  sSup (expected v p '' {a | BestReply u p a})
namespace Proof
variable [TopologicalSpace A]
variable [CompactSpace A] [Nonempty A]
end Proof
end BayesianPersuasion


