-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
-- name    : CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:51:36.358797+00:00
-- url     : https://prove2.me/theorems/cc12b878-345a-4db4-8332-184545efc87f
-- title:
--   Fixed Total Endpoint Bridge
-- statement:
--   Definitions and structural lemmas for Fixed Total Endpoint Bridge, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointBridge.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def sourceShellStart {M : ℕ} (x : SourceCode M) : ℕ :=
  2 ^ M + (sourceCodeEquivResidue M x : ℕ)
def sourceEndpoint {M : ℕ} (x : SourceCode M) : ℕ :=
  (Terras.T^[M]) (sourceShellStart x)
def sourceResidueEndpoint {M : ℕ} (x : SourceCode M) : ℕ :=
  (Terras.T^[M]) (sourceCodeEquivResidue M x : ℕ)
end
end FixedTotal
end CollatzEndpointTransport


