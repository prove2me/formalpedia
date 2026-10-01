-- Prove2me | Definitions.Def_ChapterBrstReducedTransfer
-- name    : ChapterBrstReducedTransfer
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:28:36.558974+00:00
-- url     : https://prove2.me/theorems/e3b52222-ff03-4f40-b156-ca022aa7b7f5
-- title:
--   Chapter BrstReducedTransfer
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBrstReducedTransfer.lean`): generated def bundle for ChapterBrstReducedTransfer. See BookProof/ChapterBrstReducedTransfer.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBrstReducedTransfer.lean

import Definitions.Def_ChapterStoneGenerator
import Definitions.Def_ChapterStoneResolvent
import Mathlib


/-!
# The BRST-reduced transfer: the unitary evolution descends to BRST cohomology

`CONSOLIDATED_PLAN.md` §10.6.2 item 4 asks, besides the concrete gauge-fixed field-space
Hamiltonian and its BRST charge, for the **BRST-reduced transfer** of the half-density
unitary `U`: the evolution *must map the physical subspace to itself* and must descend to
the physical states modulo the exact (gauge) ones, which is the caveat recorded in §10.3.
This module proves exactly that, for an arbitrary bounded nilpotent BRST charge `Ω` and an
arbitrary strongly-commuting unitary group — in particular for the group `e^{-itT}` that
the project's Stone theorem produces from an unbounded self-adjoint Hamiltonian.

## What is proved

Write `physicalStates Ω = ker Ω` (the BRST-closed states) and
`exactStates Ω = closure (range Ω)` (the BRST-exact, i.e. pure-gauge, states; the closure
is what makes the quotient a topological object).  Nilpotency `Ω² = 0` gives
`exactStates_le_physicalStates`, so the **BRST cohomology**
`Cohomology Ω = physicalStates Ω ⧸ exactStates Ω` is defined.

* `physicalStates_invariant` / `exactStates_invariant` — a bounded operator commuting with
  `Ω` maps closed states to closed states and exact states to exact states.  The second
  needs the closure argument: continuity carries `range Ω` into `closure (range Ω)`.
* `reducedMap` — the induced ℂ-linear map on cohomology, with `reducedMap_mk` describing it
  on classes.
* For a one-parameter family `U` commuting with `Ω`: **`transfer`**, with
  `transfer_zero`, `transfer_comp` (the group law `transfer s ∘ transfer t = transfer (s+t)`)
  and `transfer_bijective` — so the reduced transfer is a one-parameter group of linear
  automorphisms of the cohomology.
* **`infDist_exactStates_eq`** — when the `U t` are isometries, the distance to the exact
  states, i.e. the quotient (BRST) norm of the class, is preserved:
  `infDist (U t x) (exactStates Ω) = infDist x (exactStates Ω)`.  The reduced transfer is
  therefore norm-preserving on cohomology, not merely well defined.
* The Stone instance `stoneTransfer` with `stoneTransfer_zero`, `stoneTransfer_comp`,
  `stoneTransfer_bijective` and `infDist_exactStates_stoneU_eq`: the unitary group of an
  unbounded self-adjoint Hamiltonian commuting with `Ω` descends to a one-parameter group
  of norm-preserving automorphisms of the BRST cohomology.

## Honest boundary

`Ω` is a *bounded* nilpotent operator and is assumed to commute with the group (the correct
unbounded form of `[H, Ω] = 0`); the concrete 3D gauge-fixed field-space Hamiltonian and its
ghost-sector BRST charge of §10.6.2 item 4 are not constructed here — this module supplies
the reduction statement that such a construction must feed.
-/

namespace BookProof.BrstReducedTransfer

open BookProof BookProof.ChapterStoneResolvent

section General

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

/-- The BRST-closed (physical) states: the kernel of the BRST charge. -/
def physicalStates : Submodule ℂ H := LinearMap.ker (Om : H →ₗ[ℂ] H)

/-- The BRST-exact (pure gauge) states: the closure of the range of the BRST charge.  The
closure is what makes the quotient by them a well-behaved topological object. -/
def exactStates : Submodule ℂ H := (LinearMap.range (Om : H →ₗ[ℂ] H)).topologicalClosure



theorem mem_exactStates_of_apply (y : H) : Om y ∈ exactStates Om :=
  Submodule.le_topologicalClosure _ ⟨y, rfl⟩

theorem isClosed_exactStates : IsClosed (exactStates Om : Set H) :=
  Submodule.isClosed_topologicalClosure _



variable {Om}

/-- A bounded operator commuting with the BRST charge preserves the physical subspace. -/
theorem physicalStates_invariant {f : H →L[ℂ] H} (h : ∀ y, f (Om y) = Om (f y)) :
    ∀ x ∈ physicalStates Om, f x ∈ physicalStates Om := by
  intro x hx
  have hx' : Om x = 0 := hx
  change Om (f x) = 0
  rw [← h x, hx', map_zero]

/-- A bounded operator commuting with the BRST charge preserves the exact (gauge) states.
Continuity is what carries the range into its closure. -/
theorem exactStates_invariant {f : H →L[ℂ] H} (h : ∀ y, f (Om y) = Om (f y)) :
    ∀ x ∈ exactStates Om, f x ∈ exactStates Om := by
  intro x hx
  have hcl : IsClosed (f ⁻¹' (exactStates Om : Set H)) :=
    (isClosed_exactStates Om).preimage f.continuous
  have hsub : closure (LinearMap.range (Om : H →ₗ[ℂ] H) : Set H)
      ⊆ f ⁻¹' (exactStates Om : Set H) := by
    refine closure_minimal ?_ hcl
    rintro z ⟨y, rfl⟩
    have : f (Om y) ∈ exactStates Om := by
      rw [h y]; exact mem_exactStates_of_apply Om (f y)
    exact this
  exact hsub hx

variable (Om)

/-- The exact states, seen inside the physical subspace. -/
def trivialSub : Submodule ℂ (physicalStates Om) :=
  (exactStates Om).comap (physicalStates Om).subtype

/-- **BRST cohomology**: physical (closed) states modulo exact (pure gauge) ones. -/
abbrev Cohomology := physicalStates Om ⧸ trivialSub Om

/-- The map induced on BRST cohomology by an operator preserving the closed and the exact
states. -/
def reducedMap (f : H →L[ℂ] H) (hp : ∀ x ∈ physicalStates Om, f x ∈ physicalStates Om)
    (he : ∀ x ∈ exactStates Om, f x ∈ exactStates Om) :
    Cohomology Om →ₗ[ℂ] Cohomology Om :=
  Submodule.mapQ _ _ ((f : H →ₗ[ℂ] H).restrict hp) fun _ hx => he _ hx



section Group

variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))

/-- **The BRST-reduced transfer.**  A one-parameter family commuting with the BRST charge
descends to BRST cohomology. -/
def transfer (t : ℝ) : Cohomology Om →ₗ[ℂ] Cohomology Om :=
  reducedMap Om (U t) (physicalStates_invariant (hcomm t)) (exactStates_invariant (hcomm t))













end Group

end General

section Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H) (Om : H →L[ℂ] H)
variable (hcomm : ∀ (t : ℝ) (y : H), T.stoneU t (Om y) = Om (T.stoneU t y))

/-- **The BRST-reduced transfer of the exact unitary group.**  The group `e^{-itT}` of an
unbounded self-adjoint Hamiltonian commuting with the BRST charge descends to BRST
cohomology. -/
noncomputable def stoneTransfer (t : ℝ) : Cohomology Om →ₗ[ℂ] Cohomology Om :=
  transfer Om (fun s => T.stoneU s) hcomm t













end Stone

end BookProof.BrstReducedTransfer


