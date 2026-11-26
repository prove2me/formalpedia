-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Density
-- name    : FirstPassageLinearTransport_Density
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:56:13.686327+00:00
-- url     : https://prove2.me/theorems/1d7ebb3b-d7b1-463a-9f0f-5b5e787b6e8a
-- title:
--   Density
-- statement:
--   Definitions and structural lemmas for Density, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Density.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
noncomputable def shellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => n ∉ S)
noncomputable def prefixBad (S : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (fun n => n ∉ S)
end
end FirstPassageLinearTransport


