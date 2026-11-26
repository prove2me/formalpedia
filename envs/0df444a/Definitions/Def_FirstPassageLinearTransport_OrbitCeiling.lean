-- Prove2me | Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
-- name    : FirstPassageLinearTransport_OrbitCeiling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:17:40.981058+00:00
-- url     : https://prove2.me/theorems/7d6ff967-a9fc-496c-8d7e-f49b1fba773f
-- title:
--   Orbit Ceiling
-- statement:
--   Definitions and structural lemmas for Orbit Ceiling, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
noncomputable def multiplicativeHitResidues (M : ℕ) (u : ℝ) :
    Finset (Fin (2 ^ M)) := by
  classical
  exact Finset.univ.filter fun x =>
    crossesMultiplicativeFrom u M 1 (boolParityCode M x)
noncomputable def multiplicativeHitResidueEquiv (M : ℕ) (u : ℝ) :
    {x : Fin (2 ^ M) //
      crossesMultiplicativeFrom u M 1 (boolParityCode M x)} ≃
      {v : Fin M → Bool // crossesMultiplicativeFrom u M 1 v} :=
  (boolParityEquiv M).subtypeEquiv (fun x => by
    rw [boolParityEquiv_apply])
noncomputable def shellMultiplicativeHit (M : ℕ) (u : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    crossesMultiplicativeFrom u M 1 (boolParityWord M n)
end
end FirstPassageLinearTransport


