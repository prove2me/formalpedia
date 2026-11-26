-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
-- name    : CollatzEndpointTransport_Common_TerrasPrefixEvents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:22:49.783804+00:00
-- url     : https://prove2.me/theorems/a0fb3f2f-fc83-5ba0-a28f-8d1d95831977
-- title:
--   Terras Prefix Events
-- statement:
--   Definitions and structural lemmas for Terras Prefix Events, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasPrefixEvents.lean

import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
noncomputable def parityLowerCutoff (t : ℝ) (H : ℕ) : ℕ :=
  ⌊(1 / 2 - t) * H⌋₊
noncomputable def shellLowerPrefixBad
    (M H : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n => oddCount H n ≤ parityLowerCutoff t H)
noncomputable def shellUpperPrefixBad
    (M H : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n => H - parityLowerCutoff t H ≤ oddCount H n)
noncomputable def shellParityPrefixBadAt
    (M H : ℕ) (t : ℝ) : Finset ℕ :=
  shellLowerPrefixBad M H t ∪ shellUpperPrefixBad M H t
end Terras
end CollatzEndpointTransport


