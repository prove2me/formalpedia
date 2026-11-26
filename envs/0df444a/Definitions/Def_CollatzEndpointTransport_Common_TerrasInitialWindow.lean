-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
-- name    : CollatzEndpointTransport_Common_TerrasInitialWindow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:19:50.733696+00:00
-- url     : https://prove2.me/theorems/c25165be-dbdf-5c07-9654-c0cd44dcd4e1
-- title:
--   Terras Initial Window
-- statement:
--   Definitions and structural lemmas for Terras Initial Window, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasInitialWindow.lean

import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
open scoped Real
def PrefixTwoSidedRegular (n k0 M : ℕ) (eta : ℝ) : Prop :=
  ∀ H : ℕ, k0 ≤ H → H ≤ M →
    |(oddCount H n : ℝ) - (H : ℝ) / 2| ≤ eta * H
noncomputable def shellInitialWindowBad (M : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
    (fun n =>
      ∃ k : ℕ, k ≤ M ∧
        (((T^[k]) n : ℝ) <
            centralOrbitScale k * (n : ℝ) ^ (1 - t) ∨
          centralOrbitScale k * (n : ℝ) ^ (1 + t) <
            ((T^[k]) n : ℝ)))
end Terras
end CollatzEndpointTransport


