-- Prove2me | Definitions.Def_ChapterSqSumOuterSingleTime
-- name    : ChapterSqSumOuterSingleTime
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T20:41:37.025589+00:00
-- url     : https://prove2.me/theorems/83cdb4a6-93a0-4409-95fb-e5e12ae7c9ff
-- title:
--   Chapter SqSumOuterSingleTime
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSqSumOuterSingleTime.lean`): generated def bundle for ChapterSqSumOuterSingleTime. See BookProof/ChapterSqSumOuterSingleTime.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumOuterSingleTime.lean

import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterFiniteSectionSingleTime
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# Outer-Fock kinetic-plus-squares families: one shift, one finite time

`BookProof.ChapterSqSumOuterFamily` builds, for a uniform kinetic-plus-squares family
`F` of sector Hamiltonians `H_n = ½ Σ_I κ_I π_I² + ½ Σ_r L_r²`, the Hamiltonian
`F.outerHam` on the finite-particle core of the outer Fock space `⊕ₙ L²(ℝ^{dim n})`, and
proves it symmetric (`outerHam_symmetricOn`) and **essentially self-adjoint already on that
core** (`outerHam_esa`).  What it stops short of is the evolution statement: the propagator
of the selected generator, and a family of computable truncations converging to it.

This module supplies both, for *every* such family, along the route of
`BookProof.ChapterQgTimeIndependentFlow` (quantum gravity) and
`BookProof.ChapterFiniteSectionSingleTime` (mode Hamiltonians), with the **particle-number
truncation** in the role of the mode cutoff.

## The truncation

`F.trunc N` is the same family with the squared forms switched off above particle number
`N`: `vv n = F.vv n` for `n ≤ N` and `vv n = 0` beyond.  The Schur constants are unchanged
(a zero row has zero ℓ¹ norm), so `F.trunc N` is again a `SqFamily`, and everything proved
for a family applies to it — in particular it is essentially self-adjoint on the same core.
Above the cutoff the truncated Hamiltonian is the free kinetic term `½ Σ_I κ_I π_I²`: the
*interaction and constraint* terms are what the cutoff removes, exactly as the quantum
gravity mode truncation switches off the vielbein self-interaction and the
scalaron–vielbein coupling outside a finite window.

## What is proved

* `SqFamily.trunc`, `SqFamily.truncHam`, `trunc_secHam_eq_of_le`,
  `truncHam_eventuallyEq` — the truncated family, its Hamiltonian on the *same*
  finite-particle core, and the fact that on any fixed finite-particle state the truncated
  Hamiltonian *equals* the exact one from some cutoff on.
* `truncHam_symmetricOn`, `truncHam_esa`, `truncHam_tendsto` — the truncated Hamiltonian is
  symmetric and essentially self-adjoint on the core, and converges there to the exact one:
  the hypotheses of the Reed–Simon VIII.25(a) criterion
  `strongResolventConvergence_of_core`.
* **`outerFamily_timeIndependent_singleTime`** — the package: a self-adjoint realization
  `T` of `F.outerHam` and self-adjoint realizations `S N` of the truncations, such that the
  propagator `U(t,s) = e^{−i(t−s)H}` of the one fixed generator is unitary, satisfies
  Chapman–Kolmogorov, is invariant under a common shift of both times and uniquely solves
  the Schrödinger equation; at **every** nonzero shift the Hashimoto shift-invert operators
  of the truncations converge strongly; and hence at **every single finite time** the
  truncated propagators converge to the exact one.

No time stepping, no step size, no Dyson series and no time ordering occurs anywhere.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SqSumOuterFamily

open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime
open BookProof.QgTimeIndependent BookProof.QgTruncationResolvent
open BookProof.DirectSumEsa BookProof.HermiteProductCore

noncomputable section

namespace SqFamily

/-! ## 1. The particle-number truncation -/

/-- **The particle-number truncation** of a uniform family: the squared forms are switched
off above particle number `N`, so that above the cutoff only the free kinetic term
`½ Σ_I κ_I π_I²` remains.  The Schur constants are unchanged. -/
def trunc (F : SqFamily) (N : ℕ) : SqFamily where
  dim := F.dim
  R := F.R
  finR := F.finR
  kap := F.kap
  vv := fun n r I => if n ≤ N then F.vv n r I else 0
  km := F.km
  a := F.a
  b := F.b
  km_nonneg := F.km_nonneg
  a_nonneg := F.a_nonneg
  b_nonneg := F.b_nonneg
  kap_le := F.kap_le
  row_le := by
    intro n r
    by_cases h : n ≤ N
    · simpa [h] using F.row_le n r
    · simpa [h] using F.a_nonneg
  col_le := by
    intro n I
    by_cases h : n ≤ N
    · simpa [h] using F.col_le n I
    · simpa [h] using F.b_nonneg

@[simp] theorem trunc_dim (F : SqFamily) (N : ℕ) : (F.trunc N).dim = F.dim := rfl



/-- **The truncated Hamiltonian**, on the *same* finite-particle core as the exact one. -/
def truncHam (F : SqFamily) (N : ℕ) : outerCore F.dim →ₗ[ℂ] outerFock F.dim :=
  dsOp (fun n => (F.trunc N).secHam n)

@[simp] theorem truncHam_coe (F : SqFamily) (N : ℕ) (x : outerCore F.dim) (n : ℕ) :
    ((truncHam F N x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n
      = (F.trunc N).secHam n
          ((⟨((x : outerFock F.dim) : ∀ n : ℕ, L2d (F.dim n)) n, x.2.2 n⟩ :
            ↥(polyGaussCore (d := F.dim n))) : polyGaussCore (d := F.dim n)) :=
  rfl











/-! ## 2. The package: one shift, one finite time -/



end SqFamily

end

end BookProof.SqSumOuterFamily


