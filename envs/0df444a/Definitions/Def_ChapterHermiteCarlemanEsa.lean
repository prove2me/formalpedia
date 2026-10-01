-- Prove2me | Definitions.Def_ChapterHermiteCarlemanEsa
-- name    : ChapterHermiteCarlemanEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-30T21:32:46.484978+00:00
-- url     : https://prove2.me/theorems/d643af24-4621-4c3b-b83d-246263d65702
-- title:
--   Chapter HermiteCarlemanEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteCarleman`, source chapter `BookProof/ChapterHermiteCarlemanEsa.lean`): Chapter HermiteCarlemanEsa
--
--   Generated def bundle for ChapterHermiteCarlemanEsa. See BookProof/ChapterHermiteCarlemanEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteCarlemanEsa.lean

import Mathlib

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterStoneBridge

/-!
# A Carleman criterion on the product Hermite basis, and the full diagonal quadratic
family with an arbitrary first-order term

`BookProof.ChapterHermiteRelativeBound` proves that the inhomogeneous quadratic
Hamiltonian

`H = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`
when the quadratic part is **elliptic** (`cᵢ ≥ c₀ > 0`), by a relative bound; the
shifted-core modules (`ChapterShiftedQuadraticEsa`,
`ChapterShiftedQuadraticMatrixEsa`, `ChapterShiftedQuadraticDegenerate`) remove the sign
and the invertibility conditions by completing the square, but need a *classical
equilibrium* — which does not exist in a direction where the quadratic part vanishes and
both `bᵢ` and `b'ᵢ` are present — and they pay for it by moving to a translated,
modulated core.  `ChapterQuadratureEsa` settles the opposite extreme, `c = 0`, on the
plain core.

This module removes **all** of those restrictions at once, by a different route: a
*Carleman-type criterion* for the coefficient recursion on the multi-index lattice.

## What is proved

* `LadderRec`, `ladder_eq_zero` — **the instrument.**  Let `u : (Fin d →₀ ℕ) → ℂ` be a
  square-summable family (only Bessel's inequality `∑_{a ∈ F} ‖u a‖² ≤ B` on finite sets
  is used) satisfying, for every multi-index `α`, the nearest-neighbour recursion

  `lam α u_α + ∑ᵢ (conj(wᵢ)√(αᵢ+1) u_{α+eᵢ} + wᵢ√αᵢ u_{α−eᵢ}) = z u_α`

  with a **real** diagonal `lam` and constant amplitudes `w`, at a point `z` off the real
  axis.  Then `u = 0`.  The proof is the classical Wronskian/flux argument of Carleman,
  run on cubes `{α : ∀ i, αᵢ ≤ N}` instead of intervals: the interior contributions are
  pairwise conjugate, so the imaginary part of the recursion telescopes to the flux
  through the boundary faces (`flux_identity`), which is bounded by `√(N+1)` times the
  `ℓ²`-mass carried by those faces (`flux_bound`).  The faces are disjoint, so that mass
  is summable, while `∑ 1/√(N+1) = ∞` — a contradiction unless the mass vanishes.

* `mixOp_hermiteCore` — the ladder form of `H` on the product Hermite basis: the
  quadratic part is diagonal with the real symbol `∑ᵢ cᵢ(αᵢ + ½)`, and the first-order
  part raises the `i`-th excitation number with amplitude `wᵢ = bᵢ + ib'ᵢ/2` and lowers
  it with `conj wᵢ`.

* `mixOp_deficiencyTrivialAt`, `mixOp_essentiallySelfAdjoint` — **the headline.**  For
  **arbitrary** real weights `c` (any signs, zeros allowed) and **arbitrary** real
  coefficients `b, b'`, the operator `H_c + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially
  self-adjoint on the plain Gauss–polynomial core of `L²(ℝᵈ)`.  No ellipticity, no sign
  condition, no classical equilibrium, and no change of core.

* `mixOp_stone_flow` — the resulting complete unitary Schrödinger flow, by Stone's
  theorem.

* `wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint` — the Minkowski corollary:
  `□ + V` with `V(t,x) = (t² − ‖x‖²)/4` plus an arbitrary constant external field and an
  arbitrary constant boost, on the plain core.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteCarleman

open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. The multi-index cube and its faces -/

/-- The cube `{α : ∀ i, αᵢ ≤ N}` of multi-indices, as a finite set. -/
def cube (d N : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1)).image Finsupp.equivFunOnFinite.symm



/-- The interior of the cube in the `i`-th direction: the multi-indices which can still
be raised in that direction without leaving the cube. -/
def inn (d N : ℕ) (i : Fin d) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => a i < N)

/-- The `i`-th boundary face of the cube. -/
def face (d N : ℕ) (i : Fin d) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => a i = N)









/-! ## 2. The Carleman criterion on the multi-index lattice -/

/-- The raising contribution to the flux at the multi-index `a` in the direction `i`. -/
def rterm (u : (Fin d →₀ ℕ) → ℂ) (amp : Fin d → ℂ) (i : Fin d) (a : Fin d →₀ ℕ) : ℂ :=
  (starRingEnd ℂ) (amp i) * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)
    * (starRingEnd ℂ) (u a) * u (a + Finsupp.single i 1)

/-- The lowering contribution to the flux at the multi-index `a` in the direction `i`. -/
def lterm (u : (Fin d →₀ ℕ) → ℂ) (amp : Fin d → ℂ) (i : Fin d) (a : Fin d →₀ ℕ) : ℂ :=
  amp i * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ)
    * (starRingEnd ℂ) (u a) * u (a - Finsupp.single i 1)

variable {u : (Fin d →₀ ℕ) → ℂ} {lam : (Fin d →₀ ℕ) → ℝ} {amp : Fin d → ℂ} {z : ℂ}





/-- The nearest-neighbour recursion satisfied by the Hermite coefficients of a deficiency
vector: a real diagonal `lam`, raising amplitude `conj (amp i) √(αᵢ+1)` and lowering
amplitude `amp i √αᵢ`, at the (non-real) point `z`. -/
def LadderRec (u : (Fin d →₀ ℕ) → ℂ) (lam : (Fin d →₀ ℕ) → ℝ) (amp : Fin d → ℂ) (z : ℂ) :
    Prop :=
  ∀ a : Fin d →₀ ℕ,
    ((lam a : ℝ) : ℂ) * u a
      + ∑ i, ((starRingEnd ℂ) (amp i) * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)
                * u (a + Finsupp.single i 1)
            + amp i * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) * u (a - Finsupp.single i 1))
      = z * u a















/-! ## 3. The inhomogeneous quadratic Hamiltonian on the Hermite core -/

/-- The inhomogeneous quadratic Hamiltonian `H_c + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` on the
Gauss–polynomial core. -/
def mixOp (c b b' : Fin d → ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  quadOp c + foOp b b'













end

end BookProof.HermiteCarleman


