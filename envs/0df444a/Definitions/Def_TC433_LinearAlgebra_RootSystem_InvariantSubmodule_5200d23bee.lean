-- Prove2me | Definitions.Def_TC433_LinearAlgebra_RootSystem_InvariantSubmodule_5200d23bee
-- name    : TC433_LinearAlgebra_RootSystem_InvariantSubmodule_5200d23bee
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:31:58.256509+00:00
-- url     : https://prove2.me/theorems/d8d888a1-dc43-45bf-952c-352281db621e
-- title:
--   TauCeti: LinearAlgebra / RootSystem / InvariantSubmodule
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.RootSystem.InvariantSubmodule for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/RootSystem/InvariantSubmodule.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Reflection-invariant submodules of a root pairing

A submodule of the root space invariant under the reflection at `v` absorbs, from any root it
already contains, every root whose pairing with `v` is nonzero. Reflecting `u` in `v` stays inside
the submodule, and subtracting leaves a multiple of the root at `v` whose coefficient is exactly
that pairing.

This is stated for a bare `RootPairing`: no base, no crystallographic structure, no finiteness and
no assumption on the characteristic. Consumers that propagate membership along a Dynkin edge supply
the nonvanishing of the pairing from adjacency at the call site.

## Main results

* `RootPairing.root_mem_of_pairing_ne_zero`: membership of a root in a reflection-invariant
  submodule propagates along a nonzero pairing.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

section

variable {K M N ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] {P : RootPairing ι K M N}

/-- **Membership of a root in a reflection-invariant submodule propagates along a nonzero
pairing.** If `q` is invariant under the reflection at `v`, the pairing of `u` with `v` is nonzero,
and the root at `u` lies in `q`, then so does the root at `v`. -/
theorem _root_.RootPairing.root_mem_of_pairing_ne_zero {q : Submodule K M} {u v : ι}
    (hinvv : q ∈ Module.End.invtSubmodule (P.reflection v))
    (hpair : P.pairing u v ≠ 0) (hu : P.root u ∈ q) : P.root v ∈ q := by
  -- Reflecting `u` in `v` keeps us inside `q`; subtracting leaves a multiple of `root v`, and the
  -- multiplier is invertible by hypothesis.
  have hrefl : P.reflection v (P.root u) ∈ q :=
    (Module.End.mem_invtSubmodule _).mp hinvv hu
  have hsmul : P.pairing u v • P.root v ∈ q := by
    simpa only [P.reflection_apply_root, sub_sub_cancel] using q.sub_mem hu hrefl
  exact (q.smul_mem_iff hpair).mp hsmul

end

end TauCeti


