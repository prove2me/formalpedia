-- Prove2me | Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
-- name    : NewtonianLipschitz_ConditionalFiniteSource
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:47:08.1275+00:00
-- url     : https://prove2.me/theorems/82542d82-aacc-44b5-8457-1efbfad302cc
-- title:
--   Conditional Finite Source
-- statement:
--   Definitions and structural lemmas for Conditional Finite Source, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_FiniteSources
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
abbrev oneSourceGlobalCandidateBound : Prop :=
  ∀ (c : NewtonianPointSource) (x y : Vec3) (d : ℝ),
    0 < d → d ≤ ‖x‖ → d ≤ ‖y‖ →
      ‖c.accelerationField x - c.accelerationField y‖ ≤
        ((1 / d ^ 3) *
          (c.gravitationalParameter * candidateMaximum)) * ‖x - y‖
end NewtonianLipschitz


