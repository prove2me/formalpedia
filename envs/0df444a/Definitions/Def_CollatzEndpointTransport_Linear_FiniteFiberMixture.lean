-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
-- name    : CollatzEndpointTransport_Linear_FiniteFiberMixture
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:53:37.916797+00:00
-- url     : https://prove2.me/theorems/b2330bdb-15c1-4558-a54a-cd6ce109b3a2
-- title:
--   Finite Fiber Mixture
-- statement:
--   Definitions and structural lemmas for Finite Fiber Mixture, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FiniteFiberMixture.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def mixedFiberCard
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    (b : β) : ℕ :=
  ∑ i ∈ U, (mapFiber (W i) (f i) b).card
def mixedTargetSet
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β) :
    Finset β :=
  U.biUnion fun i => (W i).image (f i)
end
end FixedTotal
end CollatzEndpointTransport


