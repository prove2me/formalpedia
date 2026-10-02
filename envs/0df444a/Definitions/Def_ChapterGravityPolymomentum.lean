-- Prove2me | Definitions.Def_ChapterGravityPolymomentum
-- name    : ChapterGravityPolymomentum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:18:45.249888+00:00
-- url     : https://prove2.me/theorems/78a9a578-ce7c-4c78-8f0e-75eb46e6e9e3
-- title:
--   Chapter GravityPolymomentum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityPolymomentum.lean`): generated def bundle for ChapterGravityPolymomentum. See BookProof/ChapterGravityPolymomentum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityPolymomentum.lean

import Definitions.Def_ChapterGravityProjector
import Mathlib


/-!
# Chapter "Diffeomorphisms and gravity": the projected polymomenta and the
Legendre transform of the Einstein–Cartan Hamiltonian

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  After varying the teleparallel Lagrangian density in
the vielbein velocities the manuscript obtains the **polymomentum**

`p^{ab} = e ( S^{ab} − (4/3) T η^{ab} − 𝒯^{ab} + 2 𝒯^{ac}{}_c v^b )`,

where, relative to the globally defined unit timelike vector `v` (`v^a v_a = −1`)
and the spatial projector `χ_a{}^b = δ_a{}^b + v_a v^b` of
`ChapterGravityProjector`:

* `S^{ab}` is the **spatial, symmetric, traceless** part of the torsion tensor
  `T_{ab}` (the irreducible piece isolated in `ChapterGravityIrrep`),
* `T` is its **trace**,
* `𝒯^{ab}` is a **spatial antisymmetric** tensor, and
* `e = det e_μ^a` is the vielbein determinant.

The manuscript then reads off the *projected* polymomenta

* `𝒜^{ab} = χ^a{}_{a₁}χ^b{}_{a₂}(p^{a₁a₂} − p^{a₂a₁}) = −2 e 𝒯^{ab}`,
* `𝒫 = η_{ab} χ^a{}_{a₁}χ^b{}_{a₂} p^{a₁a₂} = −4 e T`,
* `𝒮^{ab} = χ^a{}_{a₁}χ^b{}_{a₂}(p^{a₁a₂} + p^{a₂a₁} − (2/3) η^{a₁a₂} 𝒫) = 2 e S^{ab}`,

and uses them to rewrite the 3-dimensional Hamiltonian density in terms of the
momenta,

`ℋ = (1/16e) 𝒮^{ab}𝒮_{ab} − (1/24e) 𝒫² + (1/2) 𝒮^{ab}E_{ab} + (1/3) 𝒫 E_a{}^a − e(…)`,

which the manuscript asserts to be the same as its velocity form

`ℋ ≈ e( (1/4) S^{ab}S_{ab} − (2/3) T² + S^{ab}E_{ab} − (4/3) T E_a{}^a − (…) )`.

This file proves all four statements: the three inversion formulas, and the
equality of the momentum form and the velocity form of the Hamiltonian density
(the Legendre-transform consistency of the two displays).

## Model

Contravariant `(2,0)` tensors are real `4×4` matrices; `η = diag(−1,1,1,1)`
(`ChapterGravityProjector.metric`, which is its own inverse, so the same matrix
also represents `η^{ab}`), index lowering is `lower v`, and the spatial projector
is `spatialProj v`.  A tensor `M` is **spatial** (`IsSpatial`) when both of its
contractions with `v_·` vanish, which is exactly the condition for it to be
unchanged by the double `χ`-projection.

## Deliverables

* `metric_mul_metric`, `metric_mulVec_lower` — `η` is an involution;
* `proj` — the double spatial projection `M ↦ χ M χᵀ`, with its linearity, its
  compatibility with transposition, and its values on spatial tensors
  (`proj_eq_self_of_spatial`), on the term `2 𝒯^{ac}{}_c v^b`
  (`proj_vecMulVec_right`) and on the inverse metric (`proj_metric`, producing
  the spatial metric `h^{ab} = η^{ab} + v^a v^b`);
* `polyMom` — the book's `p^{ab}`, and `proj_polyMom` its projection;
* `calA_eq`, `calP_eq`, `calS_eq` — **the three inversion formulas**
  `𝒜 = −2e𝒯`, `𝒫 = −4eT`, `𝒮 = 2eS`;
* `polyMom_contract_v`, `polyMom_contract_v_spatial` — the remaining contraction
  `v_b p^{ab}`, computed honestly; see the note below;
* `contract` — the `η`-contraction `A^{ab}B_{ab}`, with its bilinearity;
* `hamiltonian_momentum_eq_velocity` — **the Legendre-transform consistency**:
  the momentum form and the velocity form of the Hamiltonian density agree.

## A note on `p^a`

The manuscript also lists `p^a = v_b p^{ab} = 2 e 𝒯^{ac}{}_c`.  With the
conventions fixed above (mostly-plus `η`, `v^a v_a = −1`, `p^{ab}` exactly as
displayed) the honest computation, recorded in `polyMom_contract_v`, gives

`v_b p^{ab} = −e ( (4/3) T v^a + 2 u^a )`,   `u^a := 𝒯^{ac}{}_c`,

whose spatial projection is `−2 e u^a` (`polyMom_contract_v_spatial`).  So this
last entry of the manuscript's list agrees with the computation only up to the
overall sign of the contraction with `v`, and after projecting away the part
along `v`; the three formulas `𝒜`, `𝒫`, `𝒮`, which are the ones entering the
Hamiltonian, hold exactly as printed.  Nothing else in this file depends on it.
-/

namespace BookProof.ChapterGravityPolymomentum

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

/-! ## Preliminaries -/





















/-! ## The double spatial projection of a `(2,0)` tensor -/

/-- The double spatial projection `(χ M χᵀ)^{ab} = χ^a{}_{a₁} χ^b{}_{a₂} M^{a₁a₂}`. -/
noncomputable def proj (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  spatialProj v * M * (spatialProj v)ᵀ









/-- A `(2,0)` tensor is **spatial** when both of its contractions with `v_·`
vanish; equivalently, when the double `χ`-projection leaves it unchanged. -/
structure IsSpatial (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  right : M.mulVec (lower v) = 0
  left : M.vecMul (lower v) = 0















/-! ## The polymomentum and its projections -/

/-- The book's polymomentum
`p^{ab} = e ( S^{ab} − (4/3) T η^{ab} − 𝒯^{ab} + 2 u^a v^b )`, with
`u^a = 𝒯^{ac}{}_c`. -/
noncomputable def polyMom (e T : ℝ) (S Tc : Matrix (Fin 4) (Fin 4) ℝ) (u v : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  e • (S - ((4 / 3) * T) • metric - Tc + (2 : ℝ) • vecMulVec u v)

/-- The projected antisymmetric part `𝒜^{ab}`. -/
noncomputable def calA (v : Fin 4 → ℝ) (p : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := proj v (p - pᵀ)

/-- The projected trace `𝒫 = η_{ab} χ^a{}_{a₁} χ^b{}_{a₂} p^{a₁a₂}`. -/
noncomputable def calP (v : Fin 4 → ℝ) (p : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (metric * proj v p).trace

/-- The projected symmetric traceless part `𝒮^{ab}`. -/
noncomputable def calS (v : Fin 4 → ℝ) (p : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  proj v (p + pᵀ) - ((2 / 3) * calP v p) • proj v metric

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}













/-! ## The Legendre transform: the momentum form of `ℋ` equals the velocity form -/

/-- The `η`-contraction `A^{ab} B_{ab} = η_{ac} η_{bd} A^{ab} B^{cd}`. -/
noncomputable def contract (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (metric * A * metric * Bᵀ).trace







end BookProof.ChapterGravityPolymomentum


