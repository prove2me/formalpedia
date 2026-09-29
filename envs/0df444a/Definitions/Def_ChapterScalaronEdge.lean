-- Prove2me | Definitions.Def_ChapterScalaronEdge
-- name    : ChapterScalaronEdge
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-17T19:44:38.062685+00:00
-- url     : https://prove2.me/theorems/63c6f8e8-5985-4c27-89e0-028bf15d0da5
-- title:
--   The strict one-particle edge for the Starobinsky fiber
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ScalaronEdge`, source chapter `BookProof/ChapterScalaronEdge.lean`): the strict one-particle edge for the Starobinsky fiber. The wall potential `V(phi) = K(1 - e^{-a phi})^2` at fixed parameters, the fiber Hamiltonian `h = -d^2/dphi^2 + V` on the compactly supported smooth core of `L^2(R)`, the working threshold `edgeShelf = M^4/(32 alpha)` below the plateau `M^4/(16 alpha)`, the confinement constants `edgeKinConst` and `edgeMassConst`, and the strict one-particle edge `starobinskyEdge_quadForm`: `quadratic form of h >= E0 * norm^2` with `E0 = min(edgeKinConst, edgeMassConst) > 0`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronEdge.lean

import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFriedrichsFormGap
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
import Mathlib


/-!
# The strict one-particle edge for the Starobinsky fiber

`CONSOLIDATED_PLAN.md` §state 28j/29, item 4: the strict one-particle edge for the
Starobinsky fiber.

The Einstein-frame scalaron potential is `V(φ) = K(1 − e^{−aφ})²` with `K = M⁴/(16α)`
and `a = √(2/3)/M` (`BookProof.Starobinsky.starobinskyV`).  Its plateau value — the
limit as `φ → +∞`, `starobinskyV_tendsto_plateau` — is `K = M⁴/(16α)`, and it has an
exponential wall as `φ → −∞` (`starobinskyV_tendsto_atBot_atTop`).  Consequently the
classically allowed region `{φ | V(φ) < c}` is *bounded* for every `0 < c < K`; we work
with the fixed working threshold `edgeShelf = M⁴/(32α) < K` (any constant strictly below
the plateau works, and a smaller constant only shrinks the window).

## What is proved

* `starobinskyV_lt_shelf_bounded` — for `0 < c < edgeShelf` the sublevel set
  `{φ | V(φ) < c}` is contained in `[−A, B]` with the explicit positive endpoints
  `A = log(1 + √(c/K))/a`, `B = −log(1 − √(c/K))/a`.
* `edge_sup_sq_le` — the elementary one-dimensional Agmon/Gagliardo bound
  `‖f(x)‖² ≤ δ‖f‖²_{L²} + δ⁻¹‖f'‖²_{L²}` for every compactly supported `C²` function
  and every `δ > 0` (integration of `d/dt‖f‖²` from the left end of the support).
* `edge_energy_bound` — the confinement estimate it buys: if `V ≥ 0` everywhere and
  `V ≥ c` outside `[−A, B]`, then
  `∫|f'|² + ∫V|f|² ≥ min(1/(4(A+B)²), c/2) · ∫|f|²`.
* **`starobinskyEdge_quadForm`** — the strict one-particle edge for the fiber
  Hamiltonian `h_ψ = −d²/dφ² + V(φ̂)` on the compactly supported smooth core of `L²(ℝ)`:
  `⟪h_ψ ψ, ψ⟫ ≥ E₀⟪ψ, ψ⟫` with the explicit `E₀ = min(edgeKinConst A B) (edgeMassConst c) > 0`.
* `starobinskyEdge_form_gap` — the same statement in the project's `quadForm` shape.
* **`scalaronEdge_friedrichs_gap`** — the lift of the edge off the core: the Friedrichs
  extension of `h_ψ` is a positive self-adjoint extension, is the operator the Hashimoto
  shift-invert scheme selects, and inherits the strict lower bound `E₀ > 0` on its whole
  domain (`BookProof.FriedrichsFormGap.friedrichs_extension_form_gap`).

## Honest boundary

* What becomes unconditional: the strict one-particle edge for the scalaron-fiber
  Schrödinger operator `−d²/dφ² + starobinskyV(φ̂)` on the compactly supported smooth
  core, and its transfer to the Friedrichs extension selected by the shift-invert scheme.
* What stays a modelling statement: that this fiber operator is *the* scalaron sector's
  one-particle input of the enclosure doctrine (same boundary as the constant-model wave).
  The TEGR kinetic/gravity sector is untouched and remains outside the gap claims.  No
  mass gap of any physical Yang–Mills or gravity Hamiltonian is claimed.
* The `E₀` produced is the constructive (non-sharp) confinement constant — the numerically
  observed `E₀ ≈ 0.689` at `α = 1/12` is a different, sharper statement, not claimed here.
* The number-preserving `dΓ` lift of `ChapterFockNumberPreservingGap` is *not* instantiated
  here: it consumes a one-particle operator that is an endomorphism of the finite-mode
  domain of a Hilbert basis, and `−d²/dφ² + V` leaves no finite-mode subspace of the
  compactly supported core invariant.  The Friedrichs transfer above is the honest
  off-core statement for this fiber.
-/

namespace BookProof.ScalaronEdge

open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert

/-! ## 0. The Starobinsky potential and the operator

The wall module works with the *explicit* potential `fun phi => starobinskyV M alpha phi`
at parameters `M, alpha` (see `starobinskyWall_esa`).  We fix parameters once and work with
that operator, so every statement below is an instance of the wall API. -/

variable (M alpha : ℝ)

/-- The wall potential at the fixed parameters. -/
noncomputable def scalV : ℝ → ℝ := fun phi => starobinskyV M alpha phi

theorem scalV_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scalV M alpha) :=
  contDiff_starobinskyV M alpha



/-- The working threshold below the shelf of the wall potential.  The plateau value is
`lim_{φ→+∞} V = M⁴/(16α)` (`starobinskyV_tendsto_plateau`), so the sublevel sets `{V < c}`
are bounded exactly for `c` strictly below it; `edgeShelf := M⁴/(32α)` is the fixed working
threshold used here (any constant strictly below the plateau works; the smaller the
constant, the smaller the window). -/
noncomputable def edgeShelf : ℝ := M ^ 4 / (32 * alpha)



/-- The fiber Hamiltonian: the Schrödinger operator with the wall potential on the
compactly supported smooth core of `L²(ℝ)` — exactly the operator of
`starobinskyWall_esa`. -/
noncomputable def starobinskyEdgeHam : ccDomain ℝ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  wallHam (scalV M alpha) (scalV_smooth M alpha)



/-! ## 1. Boundedness of the classically allowed region -/



/-! ## 2. The two explicit constants of the edge -/

/-- The kinetic part of the edge constant: the confinement cost of the window `[−A, B]`,
`E_kin = 1/(4(A+B)²)`. -/
noncomputable def edgeKinConst (A B : ℝ) : ℝ := 1 / (4 * (A + B) ^ 2)



/-- The mass part of the edge constant: half the outside cost, `E_mass = c/2`. -/
noncomputable def edgeMassConst (c : ℝ) : ℝ := c / 2



/-! ## 3. The elementary confinement estimate

Everything in this section is classical one-dimensional calculus for a compactly supported
`C²` function `f : ℝ → ℂ`; no property of the Starobinsky potential is used. -/









/-! ## 4. The strict one-particle edge -/











/-! ## 5. The edge off the core: the Friedrichs extension -/



end BookProof.ScalaronEdge


