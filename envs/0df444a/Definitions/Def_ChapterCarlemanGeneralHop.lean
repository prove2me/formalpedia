-- Prove2me | Definitions.Def_ChapterCarlemanGeneralHop
-- name    : ChapterCarlemanGeneralHop
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:24:30.816552+00:00
-- url     : https://prove2.me/theorems/e7332896-26a7-48ff-85d4-7e0c2cc3dbb1
-- title:
--   Chapter CarlemanGeneralHop
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCarlemanGeneralHop.lean`): generated def bundle for ChapterCarlemanGeneralHop. See BookProof/ChapterCarlemanGeneralHop.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanGeneralHop.lean

import Definitions.Def_ChapterCarlemanTwoStep
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterHermiteCarlemanEsa
import Mathlib


/-!
# A Carleman criterion for general lattice hops

`BookProof.ChapterHermiteCarlemanEsa` and `BookProof.ChapterCarlemanTwoStep` prove
Carleman (flux) criteria for recursions whose hops move a **single** excitation number,
by one or by two.  That covers every **mode-diagonal** quadratic Hamiltonian.  A quadratic
Hamiltonian which couples two *distinct* modes — `xᵢxⱼ`, `πᵢπⱼ`, `xᵢπⱼ` with `i ≠ j` —
produces hops `α ↦ α ± (eᵢ + eⱼ)` and `α ↦ α ± (eᵢ − eⱼ)`, and the second kind is **not**
monotone: the shift lowers one coordinate while raising another.

This module runs the flux argument for a hop of the completely general shape
`α ↦ α + p − m` (`hshift`), with `p` and `m` multi-indices.

## What is proved

* `hshift`, `hshift_hshift` — the shift and its inverse on the set where it is defined.
* `rtG`, `ltG`, `hopB`, `sum_ltG`, `sum_hop_im` — **the abstract flux cancellation.**  For
  a Hermitian hop family, the contributions from pairs `α, α + p − m` which both lie in a
  finite set `A` cancel in the imaginary part, so the imaginary part of the total is
  carried by two boundary layers: the *outgoing* layer `A \ B` (points of `A` whose image
  leaves `A`) and the *incoming* layer `B \ A` (points outside `A` whose image lands in
  `A`).  For a monotone hop (`m = 0`) the incoming layer is empty and this specialises to
  the situation of the two earlier modules.
-/

namespace BookProof.CarlemanGeneralHop

open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

/-! ## 1. The general shift -/

/-- The lattice hop `α ↦ α + p − m` (truncated subtraction; it is used only where
`m ≤ α`). -/
def hshift (p m a : Fin d →₀ ℕ) : Fin d →₀ ℕ := a + p - m







/-! ## 2. The abstract flux cancellation -/

variable {u : (Fin d →₀ ℕ) → ℂ}

/-- The raising contribution of the hop `α ↦ α + p − m`. -/
def rtG (u : (Fin d →₀ ℕ) → ℂ) (w : ℂ) (c : (Fin d →₀ ℕ) → ℝ) (p m a : Fin d →₀ ℕ) : ℂ :=
  (starRingEnd ℂ) w * ((c a : ℝ) : ℂ) * (starRingEnd ℂ) (u a) * u (hshift p m a)

/-- The lowering contribution, i.e. the contribution of the opposite hop
`α ↦ α − p + m`. -/
def ltG (u : (Fin d →₀ ℕ) → ℂ) (w : ℂ) (c' : (Fin d →₀ ℕ) → ℝ) (p m a : Fin d →₀ ℕ) : ℂ :=
  w * ((c' a : ℝ) : ℂ) * (starRingEnd ℂ) (u a) * u (hshift m p a)

/-- The set of points that hop **into** `A`. -/
def hopB (A : Finset (Fin d →₀ ℕ)) (p m : Fin d →₀ ℕ) : Finset (Fin d →₀ ℕ) :=
  (A.filter (fun a => ∀ k, p k ≤ a k)).image (hshift m p)









/-! ## 3. The boundary layers of a cube -/

/-- The **outgoing** boundary layer of the cube for the hop `α ↦ α + p − m`: the points of
the cube at which the hop is defined and some coordinate is within `p` of the top. -/
def obd (d N : ℕ) (p m : Fin d →₀ ℕ) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => (∀ k, m k ≤ a k) ∧ ∃ k, N < a k + p k)

/-- The **incoming** boundary layer: points just outside the cube whose hop image can land
inside it.  It is empty for a monotone hop (`m = 0`). -/
def ibd (d N : ℕ) (m : Fin d →₀ ℕ) : Finset (Fin d →₀ ℕ) :=
  (cube d (N + 1)).filter (fun b => (∀ k, m k ≤ b k) ∧ ¬ (∀ k, b k ≤ N))









/-! ## 4. The flux bound -/



/-! ## 5. Bessel's inequality for the two boundary layers -/

















/-! ## 6. The recursion and the criterion -/

/-- **A general-hop ladder recursion.**  A real diagonal `lam`, and a finite family of
Hermitian hops `α ↦ α + p h − m h` with constant amplitudes `w h`. -/
def LadderRecH (u : (Fin d →₀ ℕ) → ℂ) (lam : (Fin d →₀ ℕ) → ℝ) {ι : Type*} [Fintype ι]
    (p m : ι → (Fin d →₀ ℕ)) (c c' : ι → (Fin d →₀ ℕ) → ℝ) (w : ι → ℂ) (z : ℂ) : Prop :=
  ∀ a : Fin d →₀ ℕ,
    ((lam a : ℝ) : ℂ) * u a
      + ∑ h : ι, ((starRingEnd ℂ) (w h) * ((c h a : ℝ) : ℂ) * u (hshift (p h) (m h) a)
          + w h * ((c' h a : ℝ) : ℂ) * u (hshift (m h) (p h) a))
      = z * u a

variable {ι : Type*} [Fintype ι] {lam : (Fin d →₀ ℕ) → ℝ} {p m : ι → (Fin d →₀ ℕ)}
  {c c' : ι → (Fin d →₀ ℕ) → ℝ} {w : ι → ℂ} {z : ℂ}





end

end BookProof.CarlemanGeneralHop


