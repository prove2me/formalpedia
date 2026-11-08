-- Prove2me | Definitions.Def_ChapterCarlemanGeneralHopPromoted
-- name    : ChapterCarlemanGeneralHopPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-07T22:25:24.795468+00:00
-- url     : https://prove2.me/theorems/43eb8570-0f70-4e16-ab21-4a6d93bdefd7
-- title:
--   Carleman flux criterion for a general hop: boundary layers and the recursion
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCarlemanGeneralHop.lean`): the boundary layers of a cube for a general hop `α ↦ α + p h − m h`, built on the re-carried Hermite-Carleman and two-step definitions (the served `Def_ChapterHermiteCarlemanEsa` copy predates most of that vocabulary, and published bundles are immutable, so the definitions reach the platform under new bundle names). This bundle carries the chapter's definitions: the hop `hshift`, the shift family `hopB`, the outgoing and incoming boundary layers `obd`/`ibd` of a cube, the single-hop contributions `ltG`/`hopG`, and the general-hop recursion `LadderRecH`. The chapter's theorem facts stay problem nodes. Consumers add a single `import Definitions.Def_ChapterCarlemanGeneralHopPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanGeneralHop.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterCarlemanGeneralHop` copy is a
-- skeleton (no declarations at all), so `open BookProof.CarlemanGeneralHop` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterCarlemanGeneralHopPromoted`.
-- Left to the problem nodes on purpose (theorem facts):
--   hshift_apply
--   hshift_hshift
--   hshift_le
--   mem_hopB
--   ltG_eq_conj_rtG
--   sum_ltG
--   mem_obd
--   mem_ibd
--   amp_eq_zero_of_not_mem_obd
--   in_mem_ibd
--   flux_bound_gen
--   obd_image_multiplicity
--   ibd_multiplicity
--   obd_mass_le
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
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
open BookProof.CarlemanTwoStep

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


