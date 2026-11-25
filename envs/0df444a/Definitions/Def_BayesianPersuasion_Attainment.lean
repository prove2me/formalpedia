-- Prove2me | Definitions.Def_BayesianPersuasion_Attainment
-- name    : BayesianPersuasion_Attainment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:00:37.910223+00:00
-- url     : https://prove2.me/theorems/f3e6b306-3fbb-5f6f-9d0f-bc912e41da60
-- title:
--   Attainment
-- statement:
--   Definitions and structural lemmas for Attainment, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; portions adapted from Daniel Lyng Econlib (Apache-2.0; see pinned LICENSE and source headers)'s pinned Optimal information and concavification in Bayesian persuasion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Attainment.lean

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe uΩ uA
open Set Finset
namespace BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
def probabilitySimplex (Ω : Type uΩ) [Fintype Ω] : Set (Ω → ℝ) :=
  {p | (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1}
def bestReplyPayoffs (u v : A → Ω → ℝ) : Set ((Ω → ℝ) × ℝ) :=
  (fun x : Belief Ω × A => (x.1.val, expected v x.1 x.2)) ''
    {x | BestReply u x.1 x.2}
noncomputable def concavification (u v : A → Ω → ℝ) (q : Ω → ℝ) : ℝ :=
  sSup {z | (q, z) ∈ convexHull ℝ (bestReplyPayoffs u v)}
noncomputable def splitValue (u v : A → Ω → ℝ) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) : ℝ := ∑ s, w.val s * senderPayoff u v (b s)
noncomputable def signalValue (u v : A → Ω → ℝ) (p : Belief Ω) {n : ℕ}
    (π : Signal Ω n) : ℝ :=
  ∑ s, signalMass p π s * senderPayoff u v (signalPosterior p π s)
namespace Proof
variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv
end Proof
end BayesianPersuasion


