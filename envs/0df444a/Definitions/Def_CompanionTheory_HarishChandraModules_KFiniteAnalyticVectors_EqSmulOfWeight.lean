-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:31:34.86922+00:00
-- url     : https://prove2.me/theorems/c5e6b449-13f0-4b70-9127-8db339bf69a5
-- title:
--   Eq Smul Of Weight
-- statement:
--   Definitions and structural lemmas for Eq Smul Of Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
namespace CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
def Lower (l : List (Fin n × Fin n)) : Prop := ∀ p ∈ l, p.2 < p.1
def word (F : Fin n → Fin n → Module.End ℂ U) (l : List (Fin n × Fin n)) : Module.End ℂ U :=
  (l.map fun p => F p.1 p.2).prod
def lowSpan (F : Fin n → Fin n → Module.End ℂ U) (w : U) : Submodule ℂ U :=
  Submodule.span ℂ {x | ∃ l, Lower l ∧ x = word F l w}
variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}
def wt (ν : Fin n → ℂ) : List (Fin n × Fin n) → Fin n → ℂ
  | [] => ν
  | p :: l => wt ν l + (Pi.single p.1 1 - Pi.single p.2 1)
def hgt (μ : Fin n → ℂ) : ℂ := ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * μ c
def hOp (F : Fin n → Fin n → Module.End ℂ U) : Module.End ℂ U :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • F c c
end CompanionTheory.D.gk.HwAlg


