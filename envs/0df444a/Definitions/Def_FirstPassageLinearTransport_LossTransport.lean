-- Prove2me | Definitions.Def_FirstPassageLinearTransport_LossTransport
-- name    : FirstPassageLinearTransport_LossTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:59:54.711467+00:00
-- url     : https://prove2.me/theorems/7c42be4a-0a0e-5f95-ab76-abf94d4b6313
-- title:
--   Loss Transport
-- statement:
--   Definitions and structural lemmas for Loss Transport, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/LossTransport.lean

import Definitions.Def_FirstPassageLinearTransport_Transport
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
def reverseLossTotal (n h : ℕ) : ℚ :=
  ∑ i ∈ Finset.range h, reverseLoss n i
def scaledReverseLoss (Y n h : ℕ) : ℚ :=
  (Y : ℚ) * reverseLossTotal n h
noncomputable def lossFilteredTaggedFiber
    (M Y h y : ℕ) (D : ℚ) : Finset ℕ := by
  classical
  exact (taggedFiber M Y h y).filter fun n => scaledReverseLoss Y n h ≤ D
noncomputable def lossFilteredTransportedSources
    (M Y H : ℕ) (B : Finset ℕ) (D : ℚ) : Finset ℕ := by
  classical
  exact (Finset.range H).biUnion fun t =>
    B.biUnion fun y => lossFilteredTaggedFiber M Y (t + 1) y D
end
end FirstPassageLinearTransport


