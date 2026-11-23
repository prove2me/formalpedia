-- Prove2me | Definitions.Def_Kaplanski4_Kaplanski
-- name    : Kaplanski4_Kaplanski
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:12:53.037567+00:00
-- url     : https://prove2.me/theorems/1606f4c9-fd60-480d-a9a4-d1d25feeea42
-- title:
--   Kaplanski
-- statement:
--   Definitions and structural lemmas for Kaplanski, from riccardobrasca/kaplanski4 contributors (see pinned LICENSE and source headers)'s pinned Kaplansky criterion for unique factorization development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
set_option autoImplicit false
variable {R : Type*}
section Kaplanski
open Set Ideal Submonoid
def kaplanskySet [Semiring R] (S : Subsemigroup R) := {I : Ideal R | Disjoint (I : Set R) S}
section semiring
variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}
end semiring
section IsDomain
variable [CommSemiring R] [IsDomain R]
end IsDomain
end Kaplanski
section PowerSeries
variable [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
open PowerSeries Set Ideal
end PowerSeries


