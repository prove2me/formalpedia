-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
-- name    : CollatzEndpointTransport_Linear_FixedTotalComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:20:05.732562+00:00
-- url     : https://prove2.me/theorems/13b09388-9559-42cb-814a-9d38b0a42465
-- title:
--   Fixed Total Composition
-- statement:
--   Definitions and structural lemmas for Fixed Total Composition, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat
def syracuseNumeratorList : List ℕ → ℕ
  | [] => 0
  | k :: ks =>
      3 ^ ks.length + 2 ^ k * syracuseNumeratorList ks
def syracuseNumerator {N : ℕ} (c : Composition N) : ℕ :=
  syracuseNumeratorList c.blocks
def FixedComposition (N s : ℕ) :=
  {c : Composition N // c.length = s}
noncomputable instance fixedCompositionFintype (N s : ℕ) :
    Fintype (FixedComposition N s) :=
  Fintype.ofFinset
    ((Finset.univ : Finset (Composition N)).filter
      (fun c => c.length = s))
    (by
      intro c
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
noncomputable instance fixedCompositionDecidableEq (N s : ℕ) :
    DecidableEq (FixedComposition N s) :=
  Classical.decEq _
def fixedNumerator
    {N s : ℕ} (c : FixedComposition N s) : ℕ :=
  syracuseNumerator c.1
def fixedNumeratorResidue
    {N s : ℕ} (c : FixedComposition N s) : Fin (3 ^ s) :=
  ⟨fixedNumerator c % 3 ^ s,
    Nat.mod_lt _ (pow_pos (by norm_num : 0 < (3 : ℕ)) s)⟩
end FixedTotal
end CollatzEndpointTransport


