-- Prove2me | Definitions.Def_BayesianPersuasion_Examples
-- name    : BayesianPersuasion_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:06:05.816102+00:00
-- url     : https://prove2.me/theorems/fbf4028b-34eb-4f14-a41b-a427a1eafd0b
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; portions adapted from Daniel Lyng Econlib (Apache-2.0; see pinned LICENSE and source headers)'s pinned Optimal information and concavification in Bayesian persuasion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean

module
public import Definitions.Def_BayesianPersuasion_Theorems
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BayesianPersuasion.Examples
open Set Finset
noncomputable def bernoulli (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : Belief (Fin 2) :=
  ⟨fun i => if i = 0 then 1 - t else t, by
    constructor
    · intro i; fin_cases i <;> simp <;> linarith [ht.1, ht.2]
    · simp [Fin.sum_univ_two]⟩
noncomputable local instance _p2m_local_instance_545c504162_17 : MetricSpace (Fin 2) :=
  MetricSpace.induced (fun i : Fin 2 => (i.val : ℝ))
    (by intro i j h; apply Fin.ext; change (i.val : ℝ) = (j.val : ℝ) at h; exact_mod_cast h) inferInstance
def judge (a ω : Fin 2) : ℝ := if a = ω then 1 else 0
def prosecutor (a _ω : Fin 2) : ℝ := if a = 1 then 1 else 0
noncomputable def prior : Belief (Fin 2) := bernoulli (3 / 10) (by norm_num)
noncomputable def innocent : Belief (Fin 2) := bernoulli 0 (by norm_num)
noncomputable def indifferent : Belief (Fin 2) := bernoulli (1 / 2) (by norm_num)
noncomputable def weights : Belief (Fin 2) := bernoulli (3 / 5) (by norm_num)
noncomputable def beliefs (s : Fin 2) : Belief (Fin 2) := if s = 0 then innocent else indifferent
noncomputable def quadraticReceiver (a : Icc (0 : ℝ) 1) (ω : Fin 2) : ℝ :=
  -(a.val - (ω.val : ℝ)) ^ 2
def linearSender (a : Icc (0 : ℝ) 1) (_ω : Fin 2) : ℝ := a.val
end BayesianPersuasion.Examples


