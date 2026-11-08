-- Prove2me | Definitions.Def_ChapterCarlemanTwoStepPromoted
-- name    : ChapterCarlemanTwoStepPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-07T21:41:59.923834+00:00
-- url     : https://prove2.me/theorems/d961ad2b-d483-4370-88d8-0893dd4c7c18
-- title:
--   Two-step Carleman criterion: lattice fluxes, recursion and the criterion
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCarlemanTwoStep.lean`): the two-step Carleman criterion on the multi-index lattice. The platform's served `Def_ChapterCarlemanTwoStep` copy is a skeleton (a bare `noncomputable section` with no namespace), so every consumer statement that says `open BookProof.CarlemanTwoStep` dies with `unknown namespace`, and published bundles are immutable, so the fix is a new bundle name that keeps the original namespace (the new-name route). This bundle carries the chapter's definitions: the interior and `k`-thick boundary faces `innK`/`faceK` of a lattice cube, the single-hop contributions `rtermG`/`ltermG`, the one- and two-step amplitudes `rc1`/`lc1`/`rc2`/`lc2`, and the two-step recursion `LadderRec2`. The chapter's theorem facts stay problem nodes. Consumers add a single `import Definitions.Def_ChapterCarlemanTwoStepPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanTwoStep.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterCarlemanTwoStep` copy is a
-- skeleton (no declarations at all), so `open BookProof.CarlemanTwoStep` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterCarlemanTwoStepPromoted`.
-- Left to the problem nodes on purpose (theorem facts):
--   sub_add_singleK
--   sub_singleK_apply
--   rc1_nonneg
--   lc2_vanish
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib


/-!
# A two-step Carleman criterion on the multi-index lattice

`BookProof.ChapterHermiteCarlemanEsa` proves a Carleman criterion for a *nearest
neighbour* recursion on the lattice of multi-indices: the hops are `α ↦ α ± eᵢ`, with
amplitudes of size `O(√αᵢ)`.  That is exactly the ladder structure of a **diagonal**
quadratic Hamiltonian `∑ᵢ cᵢ(πᵢ² + xᵢ²/4)` plus a first-order term.

A general **mode-diagonal** quadratic Hamiltonian

`H = ∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is not of that form: `xᵢ²`, `πᵢ²` and the squeezing generator `½(xᵢπᵢ + πᵢxᵢ)` all
contain `aᵢ†²` and `aᵢ²`, which move the `i`-th excitation number by **two**, with an
amplitude of size `O(αᵢ)`.  This module proves the Carleman criterion for such a
recursion: hops `α ↦ α ± eᵢ` *and* `α ↦ α ± 2eᵢ`, with amplitudes `O(N)` on the boundary
of the cube `{α : ∀ i, αᵢ ≤ N}`.

## What is proved

* `innK`, `faceK` — the interior and the `k`-thick boundary face of a cube in a fixed
  direction; `sum_shiftK`, `sum_cube_splitK` — the reindexing and splitting identities.
* `rtermG`, `ltermG`, `sum_cube_hop_im` — **the abstract flux cancellation**: for a
  single Hermitian hop family of step `k`, the interior contributions occur in conjugate
  pairs, so the imaginary part of the total contribution over a cube is carried entirely
  by the `k`-thick boundary face.
* `LadderRec2`, `flux_identity2` — the two-step recursion and its flux identity.
* `flux_boundG` — the flux through a face is at most the amplitude bound there times the
  `ℓ²`-mass carried by the face and its shift.
* `sum_range_of_multiplicity`, `faceK_multiplicity`, `shiftedK_multiplicity` — Bessel's
  inequality with multiplicity: a `k`-thick face meets at most `k` cubes, so the total
  face mass is at most `k` times the total mass.  (For `k = 1` the faces are disjoint;
  for `k = 2` they are not, and this is what replaces disjointness.)
* `ladder2_eq_zero` — **the criterion.**  A square-summable family satisfying the
  two-step recursion with a real diagonal and constant amplitudes, at a point off the
  real axis, vanishes.  The Carleman divergence used is `∑ 1/(N+1) = ∞`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.CarlemanTwoStep

open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

/-! ## 1. Cubes with a step -/

/-- The part of the cube that can still be raised by `k` in the direction `i` without
leaving the cube. -/
def innK (d N : ℕ) (i : Fin d) (k : ℕ) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => a i + k ≤ N)

/-- The `k`-thick boundary face of the cube in the direction `i`. -/
def faceK (d N : ℕ) (i : Fin d) (k : ℕ) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => N < a i + k)

/-! ## 2. The abstract flux cancellation for one hop family -/

variable {u : (Fin d →₀ ℕ) → ℂ}

/-- The raising contribution of a hop of step `k` in the direction `i`. -/
def rtermG (u : (Fin d →₀ ℕ) → ℂ) (w : ℂ) (rc : (Fin d →₀ ℕ) → Fin d → ℝ) (k : ℕ) (i : Fin d)
    (a : Fin d →₀ ℕ) : ℂ :=
  (starRingEnd ℂ) w * ((rc a i : ℝ) : ℂ) * (starRingEnd ℂ) (u a) * u (a + Finsupp.single i k)

/-- The lowering contribution of a hop of step `k` in the direction `i`. -/
def ltermG (u : (Fin d →₀ ℕ) → ℂ) (w : ℂ) (lc : (Fin d →₀ ℕ) → Fin d → ℝ) (k : ℕ) (i : Fin d)
    (a : Fin d →₀ ℕ) : ℂ :=
  w * ((lc a i : ℝ) : ℂ) * (starRingEnd ℂ) (u a) * u (a - Finsupp.single i k)







/-! ## 3. The two-step recursion -/

/-- The raising coefficient of a one-step hop: `√(αᵢ+1)`. -/
def rc1 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt ((a i : ℝ) + 1)

/-- The lowering coefficient of a one-step hop: `√αᵢ`. -/
def lc1 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt (a i : ℝ)

/-- The raising coefficient of a two-step hop: `√((αᵢ+1)(αᵢ+2))`. -/
def rc2 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt (((a i : ℝ) + 1) * ((a i : ℝ) + 2))

/-- The lowering coefficient of a two-step hop: `√(αᵢ(αᵢ−1))`. -/
def lc2 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt ((a i : ℝ) * ((a i : ℝ) - 1))

/-- **The two-step recursion.**  A real diagonal `lam`, one-step amplitudes `w1` and
two-step amplitudes `w2`, at the point `z`. -/
def LadderRec2 (u : (Fin d →₀ ℕ) → ℂ) (lam : (Fin d →₀ ℕ) → ℝ) (w1 w2 : Fin d → ℂ) (z : ℂ) :
    Prop :=
  ∀ a : Fin d →₀ ℕ,
    ((lam a : ℝ) : ℂ) * u a
      + ∑ i, ((starRingEnd ℂ) (w1 i) * ((rc1 a i : ℝ) : ℂ) * u (a + Finsupp.single i 1)
            + w1 i * ((lc1 a i : ℝ) : ℂ) * u (a - Finsupp.single i 1))
      + ∑ i, ((starRingEnd ℂ) (w2 i) * ((rc2 a i : ℝ) : ℂ) * u (a + Finsupp.single i 2)
            + w2 i * ((lc2 a i : ℝ) : ℂ) * u (a - Finsupp.single i 2))
      = z * u a

variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}



/-! ## 4. The flux bound -/



/-! ## 5. Bessel's inequality with multiplicity -/













/-! ## 6. The criterion -/



end

end BookProof.CarlemanTwoStep


