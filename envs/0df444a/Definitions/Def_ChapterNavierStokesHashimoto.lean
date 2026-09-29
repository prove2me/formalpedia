-- Prove2me | Definitions.Def_ChapterNavierStokesHashimoto
-- name    : ChapterNavierStokesHashimoto
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:35:13.766714+00:00
-- url     : https://prove2.me/theorems/e3f674ab-fd20-4029-a624-e150760bbc91
-- title:
--   `BookProof.ChapterNavierStokesThreeComponent` closes the abstract sequence-space chain of the Eulerian Navier–Stokes rou ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesHashimoto`, source chapter `BookProof/ChapterNavierStokesHashimoto.lean`).
--
--   `BookProof.ChapterNavierStokesThreeComponent` closes the abstract sequence-space chain of the Eulerian Navier–Stokes route: the coupled three-component fiber Hamiltonian
--
--   `H = ∑_i ½(π_i V_i + V_i π_i)`, `V_i(u) = ∑_k A_{ik} u_k + c_i`,
--
--   written in the Hermite basis of the three velocity modes, is **essentially self-adjoint on the finite-mode core** of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, for an arbitrary real velocity-gradient matrix `A` and an arbitrary real constant vector `c` (`velH_essentiallySelfAdjointOn_core`).
--
--   The Yang–Mills route had a companion statement that the Navier–Stokes route did not: the Hashimoto/SIRK *selection* theorem (`BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs`, instantiated by `ym_hermite_hashimoto_selects`), which says that the operator the shift-invert rational Krylov algorithm computes with is the honest self-adjoint one. This module supplies it for Navier–Stokes.
--
--   The Yang–Mills instantiation went through *positivity* (the Friedrichs extension of the positive sum of squares `½Σπ² + ½ΣB²`). The Navier–Stokes Hamiltonian is **not** positive — the strain, vorticity and constant hoppings carry arbitrary signs — so the route here is the other one, and it is the one essential self-adjointness was proved for: by `BookProof.EsaClosure.exists_isSelfAdjointExtension_of_esa` the closure of the core operator is self-adjoint, by `BookProof.EsaClosure.isSelfAdjointExtension_unique_of_esa` it is the *only* self-adjoint operator the core determines, and at any non-real shift the resolvents exist and are bounded with no positivity at all.
--
--   * `velCore` — the coupled Navier–Stokes fiber Hamiltonian restricted to the finite-mode core, with `velCore_symmetricOn` and `velCore_esa`; * `ns_selfAdjoint_extension` — the core operator has a self-adjoint extension (its closure), for every real `A` and `c`; * `ns_selfAdjoint_extension_unique` — and only one; * `ns_hashimoto_selects` — **the headline**: for an arbitrary sequence of non-real shifts `γ_j`, the shift-inverted resolvents `X_j = (γ_j − A)⁻¹` of the Navier–Stokes generator exist, are bounded by `1/|Im γ_j|`, share the domain of `A`, satisfy the resolvent identity, commute, satisfy the SIRK relation of Hashimoto–Nodera, have strongly convergent Galerkin truncations, and **each of them determines `A` completely**; * `ns_shiftInvert_selects` — the single-shift form; * `exists_velHilbertBasis` — the statement is not vacuous: `ℓ²(Vel)` does carry an `ℕ`-indexed Hilbert basis.
--
--   Unchanged from the rest of the Navier–Stokes thread (Contention D5): the setting is the abstract sequence space `ℓ²(Vel)` carrying the Hermite matrix of the fiber Hamiltonian; the differential realization on `L²(du₁du₂du₃)` is not built here, and **nothing here claims global regularity for the classical Navier–Stokes equation**. What is claimed is exactly the operator statement: the algorithm's shift-invert data determine one self-adjoint operator, the closure of the essentially self-adjoint core Hamiltonian.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesHashimoto.lean

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesEsa
import Mathlib

import Mathlib

/-!
# The Hashimoto/SIRK shift-invert limit selects the Navier–Stokes generator

`BookProof.ChapterNavierStokesThreeComponent` closes the abstract
sequence-space chain of the Eulerian Navier–Stokes route: the coupled
three-component fiber Hamiltonian

`H = ∑_i ½(π_i V_i + V_i π_i)`,  `V_i(u) = ∑_k A_{ik} u_k + c_i`,

written in the Hermite basis of the three velocity modes, is **essentially
self-adjoint on the finite-mode core** of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, for an
arbitrary real velocity-gradient matrix `A` and an arbitrary real constant
vector `c` (`velH_essentiallySelfAdjointOn_core`).

The Yang–Mills route had a companion statement that the Navier–Stokes route did
not: the Hashimoto/SIRK *selection* theorem
(`BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs`,
instantiated by `ym_hermite_hashimoto_selects`), which says that the operator
the shift-invert rational Krylov algorithm computes with is the honest
self-adjoint one.  This module supplies it for Navier–Stokes.

The Yang–Mills instantiation went through *positivity* (the Friedrichs
extension of the positive sum of squares `½Σπ² + ½ΣB²`).  The Navier–Stokes
Hamiltonian is **not** positive — the strain, vorticity and constant hoppings
carry arbitrary signs — so the route here is the other one, and it is the one
essential self-adjointness was proved for: by
`BookProof.EsaClosure.exists_isSelfAdjointExtension_of_esa` the closure of the
core operator is self-adjoint, by
`BookProof.EsaClosure.isSelfAdjointExtension_unique_of_esa` it is the *only*
self-adjoint operator the core determines, and at any non-real shift the
resolvents exist and are bounded with no positivity at all.

## What is proved

* `velCore` — the coupled Navier–Stokes fiber Hamiltonian restricted to the
  finite-mode core, with `velCore_symmetricOn` and `velCore_esa`;
* `ns_selfAdjoint_extension` — the core operator has a self-adjoint extension
  (its closure), for every real `A` and `c`;
* `ns_selfAdjoint_extension_unique` — and only one;
* `ns_hashimoto_selects` — **the headline**: for an arbitrary sequence of
  non-real shifts `γ_j`, the shift-inverted resolvents `X_j = (γ_j − A)⁻¹` of
  the Navier–Stokes generator exist, are bounded by `1/|Im γ_j|`, share the
  domain of `A`, satisfy the resolvent identity, commute, satisfy the SIRK
  relation of Hashimoto–Nodera, have strongly convergent Galerkin truncations,
  and **each of them determines `A` completely**;
* `ns_shiftInvert_selects` — the single-shift form;
* `exists_velHilbertBasis` — the statement is not vacuous: `ℓ²(Vel)` does carry
  an `ℕ`-indexed Hilbert basis.

## Honest boundary

Unchanged from the rest of the Navier–Stokes thread (Contention D5): the
setting is the abstract sequence space `ℓ²(Vel)` carrying the Hermite matrix of
the fiber Hamiltonian; the differential realization on `L²(du₁du₂du₃)` is not
built here, and **nothing here claims global regularity for the classical
Navier–Stokes equation**.  What is claimed is exactly the operator statement:
the algorithm's shift-invert data determine one self-adjoint operator, the
closure of the essentially self-adjoint core Hamiltonian.
-/

open Filter Topology

namespace BookProof.NavierStokesFlow

namespace NSHashimoto

open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

/-- The coupled three-component Navier–Stokes fiber Hamiltonian, restricted to
the finite-mode core of `ℓ²(Vel)`. -/
noncomputable def velCore : lpFiniteModes Vel →ₗ[ℂ] L2I Vel :=
  (velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))))







/-! ## The self-adjoint Navier–Stokes generator -/





/-! ## The Hashimoto/SIRK selection -/





/-! ## Non-vacuity -/





end NSHashimoto

end BookProof.NavierStokesFlow


