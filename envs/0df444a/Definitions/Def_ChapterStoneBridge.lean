-- Prove2me | Definitions.Def_ChapterStoneBridge
-- name    : ChapterStoneBridge
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:38:05.372703+00:00
-- url     : https://prove2.me/theorems/6dc3c123-6b7a-4b54-9216-ac1e516e7679
-- title:
--   `BookProof.ChapterStoneResolvent`–`BookProof.ChapterStoneTheorem` prove Stone's theorem in full generality, but they con ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StoneBridge`, source chapter `BookProof/ChapterStoneBridge.lean`).
--
--   `BookProof.ChapterStoneResolvent`–`BookProof.ChapterStoneTheorem` prove Stone's theorem in full generality, but they consume the *bundled* structure `UnboundedSelfAdjoint` (a dense domain, the operator, symmetry, and equality of the adjoint domain with the domain). The essential-self-adjointness / Hashimoto-selection threads (Navier–Stokes, Yang–Mills) instead produce the predicates `BookProof.EsaClosure.IsSelfAdjointExtension` and `BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension` for an operator `A : Dom →ₗ[ℂ] F`.
--
--   This module is the missing packaging step, plus the resulting flow statement:
--
--   * `dense_domain_of_isSelfAdjointExtension` — a self-adjoint extension of a densely defined operator has a dense domain; * `isSelfAdjointOn_of_isSelfAdjointExtension` — the adjoint domain of such an extension is *equal* to its domain (both inclusions are conjuncts of the predicate, one via symmetry and one via the representation clause); * `unboundedSelfAdjointOf` — the bundled `UnboundedSelfAdjoint` structure built from `IsSelfAdjointExtension`, with `unboundedSelfAdjointOf_domain` / `unboundedSelfAdjointOf_op`; * `IsStoneFlow` — the flow package: `U 0 = 1`, the group law, isometry of each `U t`, and the Schrödinger equation `d/dt U t x = -i A (U t x)` on the domain; * `isStoneFlow_stoneU` — Stone's group `e^{-itA}` is such a flow; * `exists_stone_flow_of_selfAdjointExtension`, `exists_stone_flow_of_positive` and `exists_stone_flow_of_esa` — the three entry points: from a selected self-adjoint extension, from a positive (Friedrichs) one, and directly from essential self-adjointness of a symmetric core operator.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneBridge.lean

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterStoneResolvent

import Mathlib

/-!
# The Stone bridge: from a selected self-adjoint extension to the unitary flow

`BookProof.ChapterStoneResolvent`–`BookProof.ChapterStoneTheorem` prove Stone's
theorem in full generality, but they consume the *bundled* structure
`UnboundedSelfAdjoint` (a dense domain, the operator, symmetry, and equality of
the adjoint domain with the domain).  The essential-self-adjointness /
Hashimoto-selection threads (Navier–Stokes, Yang–Mills) instead produce the
predicates `BookProof.EsaClosure.IsSelfAdjointExtension` and
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension` for an operator
`A : Dom →ₗ[ℂ] F`.

This module is the missing packaging step, plus the resulting flow statement:

* `dense_domain_of_isSelfAdjointExtension` — a self-adjoint extension of a
  densely defined operator has a dense domain;
* `isSelfAdjointOn_of_isSelfAdjointExtension` — the adjoint domain of such an
  extension is *equal* to its domain (both inclusions are conjuncts of the
  predicate, one via symmetry and one via the representation clause);
* `unboundedSelfAdjointOf` — the bundled `UnboundedSelfAdjoint` structure built
  from `IsSelfAdjointExtension`, with `unboundedSelfAdjointOf_domain` /
  `unboundedSelfAdjointOf_op`;
* `IsStoneFlow` — the flow package: `U 0 = 1`, the group law, isometry of each
  `U t`, and the Schrödinger equation `d/dt U t x = -i A (U t x)` on the domain;
* `isStoneFlow_stoneU` — Stone's group `e^{-itA}` is such a flow;
* `exists_stone_flow_of_selfAdjointExtension`, `exists_stone_flow_of_positive`
  and `exists_stone_flow_of_esa` — the three entry points: from a selected
  self-adjoint extension, from a positive (Friedrichs) one, and directly from
  essential self-adjointness of a symmetric core operator.

Everything is `sorry`-free and `axiom`-free.
-/

open Filter Topology
open scoped InnerProductSpace
open BookProof.EsaClosure BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

namespace BookProof.StoneBridge


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Packaging a selected extension -/

/-- The domain of a self-adjoint extension contains the original domain. -/
theorem le_of_isSelfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsSelfAdjointExtension Hc A) : (D : Set F) ⊆ (Dom : Set F) :=
  fun x hx => (h.1 ⟨x, hx⟩).choose

/-- **A self-adjoint extension of a densely defined operator is densely
defined.** -/
theorem dense_domain_of_isSelfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) : Dense ((Dom : Submodule ℂ F) : Set F) :=
  hdense.mono (le_of_isSelfAdjointExtension h)

/-- **The adjoint domain of a self-adjoint extension is exactly its domain.**
The inclusion `Dom ⊆ adjointDomain` is symmetry; the reverse inclusion is the
representation clause of `IsSelfAdjointExtension`. -/
theorem isSelfAdjointOn_of_isSelfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsSelfAdjointExtension Hc A) : IsSelfAdjointOn Dom A := by
  apply Set.Subset.antisymm
  · rintro phi ⟨eta, heta⟩
    exact (h.2.2 phi eta fun v => heta v).choose
  · intro phi hphi
    exact ⟨A ⟨phi, hphi⟩, fun psi => h.2.1 psi ⟨phi, hphi⟩⟩

/-- **The bundled unbounded self-adjoint operator** determined by a selected
self-adjoint extension of a densely defined operator. -/
noncomputable def unboundedSelfAdjointOf {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) : UnboundedSelfAdjoint F where
  domain := Dom
  op := A
  denseDomain := dense_domain_of_isSelfAdjointExtension hdense h
  symmetric := h.2.1
  selfAdjoint := isSelfAdjointOn_of_isSelfAdjointExtension h





/-! ## The flow package -/

/-- **A Stone flow for `T`**: a one-parameter family `U` of operators with
`U 0 = 1`, the group law, every `U t` isometric, and solving the Schrödinger
equation `d/dt (U t x) = -i T (U t x)` on the domain of `T` (in particular the
orbit of a domain vector stays in the domain). -/
def IsStoneFlow (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)) : Prop :=
  U 0 = 1 ∧ (∀ s t, U (s + t) = U s * U t) ∧ (∀ t x, ‖U t x‖ = ‖x‖) ∧
    ∀ (x : F) (_hx : x ∈ T.domain) (t : ℝ), ∃ h : U t x ∈ T.domain,
      HasDerivAt (fun s : ℝ => U s x) ((-Complex.I) • T.op ⟨U t x, h⟩) t

variable [CompleteSpace F]









end BookProof.StoneBridge


