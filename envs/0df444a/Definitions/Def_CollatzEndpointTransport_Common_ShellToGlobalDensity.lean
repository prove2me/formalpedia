-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
-- name    : CollatzEndpointTransport_Common_ShellToGlobalDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:08:33.750865+00:00
-- url     : https://prove2.me/theorems/f6148671-a465-5171-96ee-6fc1b7533240
-- title:
--   Shell To Global Density
-- statement:
--   Definitions and structural lemmas for Shell To Global Density, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace QuantitativeDensity
open scoped Real
noncomputable section
def dyadicShell (M : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ M) (2 ^ (M + 1))
def shellBad (S : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter (fun n => n ∉ S)
end
end QuantitativeDensity
end CollatzEndpointTransport


