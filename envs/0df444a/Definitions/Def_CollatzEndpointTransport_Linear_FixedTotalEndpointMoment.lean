-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
-- name    : CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:52:38.766517+00:00
-- url     : https://prove2.me/theorems/c7044b7d-3d09-4004-a640-3915fc214330
-- title:
--   Fixed Total Endpoint Moment
-- statement:
--   Definitions and structural lemmas for Fixed Total Endpoint Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalEndpointMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
local instance endpointCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def mapFiber
    {α β : Type*} [DecidableEq β]
    (W : Finset α) (f : α → β) (b : β) : Finset α :=
  W.filter fun x => f x = b
def mapFiberCardAt
    {α β : Type*} [DecidableEq β]
    (W : Finset α) (f : α → β) (x : α) : ℕ :=
  (mapFiber W f (f x)).card
def cohortEndpoint
    {M : ℕ} (u : Fin M) (c : Composition (M - (u : ℕ))) : ℕ :=
  sourceEndpoint (Sum.inr ⟨u, c⟩ : SourceCode M)
def cohortNumeratorResidue
    {N s : ℕ} (c : Composition N) : Fin (3 ^ s) :=
  ⟨syracuseNumerator c % 3 ^ s,
    Nat.mod_lt _ (pow_pos (by norm_num : 0 < (3 : ℕ)) s)⟩
def cohortCriticalNumerator
    (M : ℕ) (u : Fin M) (s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
    ∑ c ∈ fixedSet (M - (u : ℕ)) s,
      Real.sqrt
        (mapFiberCardAt
          (fixedSet (M - (u : ℕ)) s)
          (cohortEndpoint u) c)
end
end FixedTotal
end CollatzEndpointTransport


