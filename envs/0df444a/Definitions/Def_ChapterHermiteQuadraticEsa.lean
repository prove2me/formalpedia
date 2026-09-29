-- Prove2me | Definitions.Def_ChapterHermiteQuadraticEsa
-- name    : ChapterHermiteQuadraticEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:35.012598+00:00
-- url     : https://prove2.me/theorems/b65ee4d5-6a66-4475-b76e-96b7c2692c7b
-- title:
--   Unbounded quadratic-type perturbations on the Gauss–polynomial (Hermite) core The analytic input What is proved
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteQuadraticEsa`, source chapter `BookProof/ChapterHermiteQuadraticEsa.lean`): Unbounded quadratic-type perturbations on the Gauss–polynomial (Hermite) core The analytic input What is proved
--
--   `CONSOLIDATED_PLAN.md` §10.6.1 target 4 asks for essential self-adjointness of the *sum* `−Δ + V` on the Gauss–polynomial core of `L²(ℝᵈ)`. What was available so far is `BookProof.ChapterQgHermiteOscillatorEsa`: the harmonic (conformal-mode) Hamiltonian `−Δ + ‖x‖²/4` is essentially self-adjoint on that core, and — by Kato–Rellich with relative bound `0` — so is `−Δ + ‖x‖²/4 + B` for a *bounded* continuous `B`. On the other side, `BookProof.ChapterHermiteExpWall` shows that the exponentially growing scalaron wall is **not** relatively bounded on this core at all, so no Kato–Rellich argument can reach it.
--
--   This module fills the gap in between: **unbounded** perturbations of quadratic type.
--
--   The one quantitative fact needed is the relative bound of the harmonic potential itself with respect to the harmonic Hamiltonian, with constant `1`:
--
--   `‖(‖x‖²/4)ψ‖² ≤ ‖(−Δ + ‖x‖²/4)ψ‖² + (d/2)‖ψ‖²` (`norm_sq_harmPoly_mul_le`).
--
--   It comes from the anticommutator identity (`gaussInt_anticommutator`), which on the Gauss–polynomial core is a purely algebraic computation with the twisted derivative `coreD j = ∂ⱼ − xⱼ/2` and Gaussian integration by parts:
--
--   `⟪−Δψ, Wψ⟫ + ⟪Wψ, −Δψ⟫ = 2 ∑ⱼ ⟪∂ⱼψ, W ∂ⱼψ⟫ − (d/2)‖ψ‖²`, `W = ‖x‖²/4`,
--
--   whose right-hand side is `≥ −(d/2)‖ψ‖²` because `W ≥ 0`. (Classically this is `{−Δ, W} = −ΔW + 2∑ⱼ(−∂ⱼ)W∂ⱼ` with `ΔW = d/2`.)
--
--   * `gaussInt_anticommutator`, `two_re_inner_kin_harm_ge`, `norm_sq_harmPoly_mul_le`, `norm_harmPoly_mul_le` — the relative bound of `‖x‖²/4` with respect to `−Δ + ‖x‖²/4`, with relative constant `1` and additive constant `√(d/2)`; * `norm_potLp_le_of_le_harm` — the `L²` bound `‖Vψ‖ ≤ a‖Wψ‖ + b‖ψ‖` for a potential dominated pointwise by `a·‖x‖²/4 + b`; * **`harmonic_add_subquadratic_essentiallySelfAdjoint`** — the headline: if `V` is continuous with `|V(x)| ≤ a‖x‖²/4 + b` and `a < 1`, then `−Δ + ‖x‖²/4 + V` is essentially self-adjoint on the Gauss–polynomial core. The perturbation may be unbounded; * `harmonic_add_subquadratic_stone_flow` — the self-adjoint realization and its unitary group, read off from essential self-adjointness; * `quadraticGrowth_essentiallySelfAdjoint` — the criterion in growth form: a continuous potential `U` with `|U(x) − ‖x‖²/4| ≤ A‖x‖² + C‖x‖ + B` and `4A < 1`; * `scaledHarmonic_essentiallySelfAdjoint` — `−Δ + λ‖x‖²/4` is essentially self-adjoint on the (fixed, width-one) Gauss core for every `λ ∈ (0, 2)`; * **`confV_essentiallySelfAdjoint`** — the conformal-mode instance of §10.6.1 target 4: the regularized `R + αR²` conformal-mode Hamiltonian `−Δ + V₃`, `V₃(R_c) = −(M²/2)R_c + αR_c²`, is essentially self-adjoint on the Gauss core of `L²(ℝ)` for `0 < α < 1/2`, unconditionally (no finite-speed hypothesis), together with its Stone flow `confV_stone_flow`; * **`sectorQuad_essentiallySelfAdjoint`** — the two-variable reduced `(R_c, φ)` sector with the scalaron wall replaced by a quadratic term, `V₃(R_c) + μφ²` on `L²(ℝ²)`, for `0 < α < 1/2` and `0 < μ < 1/2`, with `sectorQuad_stone_flow`; `tendsto_starobinskyV_div_sq` computes the curvature of the scalaron potential at its minimum, `V(φ)/φ² → M²/(24α)`, and `sectorHarmonicApprox_essentiallySelfAdjoint` is the sector statement at that physically natural value of `μ`, valid when `M² < 12α`.
--
--   **Honest boundary.** The relative bound of `‖x‖²/4` against `−Δ + ‖x‖²/4` is exactly `1`, so the Kato–Rellich window `a < 1` is the natural limit of this method: it reaches quadratic potentials whose curvature is within a factor `2` of the width of the Gauss core (this is why `confV_essentiallySelfAdjoint` carries `α < 1/2`; a different `α` is the same operator on a Gauss core of a different width, which this module does not build), and every strictly subquadratic perturbation o
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteQuadraticEsa.lean

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent

import Mathlib

/-!
# Unbounded quadratic-type perturbations on the Gauss–polynomial (Hermite) core

`CONSOLIDATED_PLAN.md` §10.6.1 target 4 asks for essential self-adjointness of the *sum*
`−Δ + V` on the Gauss–polynomial core of `L²(ℝᵈ)`.  What was available so far is
`BookProof.ChapterQgHermiteOscillatorEsa`: the harmonic (conformal-mode) Hamiltonian
`−Δ + ‖x‖²/4` is essentially self-adjoint on that core, and — by Kato–Rellich with relative
bound `0` — so is `−Δ + ‖x‖²/4 + B` for a *bounded* continuous `B`.  On the other side,
`BookProof.ChapterHermiteExpWall` shows that the exponentially growing scalaron wall is
**not** relatively bounded on this core at all, so no Kato–Rellich argument can reach it.

This module fills the gap in between: **unbounded** perturbations of quadratic type.

## The analytic input

The one quantitative fact needed is the relative bound of the harmonic potential itself with
respect to the harmonic Hamiltonian, with constant `1`:

`‖(‖x‖²/4)ψ‖² ≤ ‖(−Δ + ‖x‖²/4)ψ‖² + (d/2)‖ψ‖²`   (`norm_sq_harmPoly_mul_le`).

It comes from the anticommutator identity (`gaussInt_anticommutator`), which on the
Gauss–polynomial core is a purely algebraic computation with the twisted derivative
`coreD j = ∂ⱼ − xⱼ/2` and Gaussian integration by parts:

`⟪−Δψ, Wψ⟫ + ⟪Wψ, −Δψ⟫ = 2 ∑ⱼ ⟪∂ⱼψ, W ∂ⱼψ⟫ − (d/2)‖ψ‖²`,  `W = ‖x‖²/4`,

whose right-hand side is `≥ −(d/2)‖ψ‖²` because `W ≥ 0`.  (Classically this is
`{−Δ, W} = −ΔW + 2∑ⱼ(−∂ⱼ)W∂ⱼ` with `ΔW = d/2`.)

## What is proved

* `gaussInt_anticommutator`, `two_re_inner_kin_harm_ge`, `norm_sq_harmPoly_mul_le`,
  `norm_harmPoly_mul_le` — the relative bound of `‖x‖²/4` with respect to `−Δ + ‖x‖²/4`,
  with relative constant `1` and additive constant `√(d/2)`;
* `norm_potLp_le_of_le_harm` — the `L²` bound `‖Vψ‖ ≤ a‖Wψ‖ + b‖ψ‖` for a potential
  dominated pointwise by `a·‖x‖²/4 + b`;
* **`harmonic_add_subquadratic_essentiallySelfAdjoint`** — the headline: if `V` is
  continuous with `|V(x)| ≤ a‖x‖²/4 + b` and `a < 1`, then `−Δ + ‖x‖²/4 + V` is essentially
  self-adjoint on the Gauss–polynomial core.  The perturbation may be unbounded;
* `harmonic_add_subquadratic_stone_flow` — the self-adjoint realization and its unitary
  group, read off from essential self-adjointness;
* `quadraticGrowth_essentiallySelfAdjoint` — the criterion in growth form: a continuous
  potential `U` with `|U(x) − ‖x‖²/4| ≤ A‖x‖² + C‖x‖ + B` and `4A < 1`;
* `scaledHarmonic_essentiallySelfAdjoint` — `−Δ + λ‖x‖²/4` is essentially self-adjoint on the
  (fixed, width-one) Gauss core for every `λ ∈ (0, 2)`;
* **`confV_essentiallySelfAdjoint`** — the conformal-mode instance of §10.6.1 target 4: the
  regularized `R + αR²` conformal-mode Hamiltonian `−Δ + V₃`,
  `V₃(R_c) = −(M²/2)R_c + αR_c²`, is essentially self-adjoint on the Gauss core of `L²(ℝ)`
  for `0 < α < 1/2`, unconditionally (no finite-speed hypothesis), together with its Stone
  flow `confV_stone_flow`;
* **`sectorQuad_essentiallySelfAdjoint`** — the two-variable reduced `(R_c, φ)` sector with
  the scalaron wall replaced by a quadratic term, `V₃(R_c) + μφ²` on `L²(ℝ²)`, for
  `0 < α < 1/2` and `0 < μ < 1/2`, with `sectorQuad_stone_flow`;
  `tendsto_starobinskyV_div_sq` computes the curvature of the scalaron potential at its
  minimum, `V(φ)/φ² → M²/(24α)`, and `sectorHarmonicApprox_essentiallySelfAdjoint` is the
  sector statement at that physically natural value of `μ`, valid when `M² < 12α`.

**Honest boundary.**  The relative bound of `‖x‖²/4` against `−Δ + ‖x‖²/4` is exactly `1`, so
the Kato–Rellich window `a < 1` is the natural limit of this method: it reaches quadratic
potentials whose curvature is within a factor `2` of the width of the Gauss core (this is why
`confV_essentiallySelfAdjoint` carries `α < 1/2`; a different `α` is the same operator on a
Gauss core of a different width, which this module does not build), and every strictly
subquadratic perturbation of them.  It does not reach the exponential scalaron wall — nothing
can, on this core, by `BookProof.ChapterHermiteExpWall`.
-/

namespace BookProof.HermiteQuadraticEsa

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. Algebraic preliminaries on the core -/



















/-! ## 2. The relative bound of the harmonic potential -/







/-! ## 3. Potentials dominated by the harmonic one -/





/-! ## 4. The essential self-adjointness theorem -/





/-! ## 5. The criterion in growth form, and instances -/













/-! ## 6. The regularized conformal mode of the `R + αR²` Hamiltonian -/

/-- The conformal-mode potential `V₃(R_c) = −(M²/2)R_c + αR_c²`, as a potential on `L²(ℝ)`. -/
def confW (M alpha : ℝ) (x : Vd 1) : ℝ := confV M alpha (x 0)















/-! ## 7. The reduced two-variable sector with a quadratic scalaron term

The reduced `(R_c, φ)` sector of the gauge-fixed `R + αR²` Hamiltonian carries the
conformal-mode parabola `V₃(R_c)` in the first variable and the scalaron potential `V(φ)` in
the second.  The scalaron wall itself is out of reach on this core
(`BookProof.ChapterHermiteExpWall`), but its *harmonic approximation at the minimum* is not:
`V` vanishes to second order at `φ = 0` with `V(φ)/φ² → M²/(24α)`
(`tendsto_starobinskyV_div_sq`), so the model potential `V₃(R_c) + μφ²` with
`μ = M²/(24α)` is the quadratic sector Hamiltonian.  Both variables are handled at once by
the two-dimensional criterion. -/

/-- The reduced sector potential with the scalaron wall replaced by a quadratic term:
`V₃(R_c) + μφ²` on `L²(ℝ²)`. -/
def sectorQuadW (M alpha mu : ℝ) (x : Vd 2) : ℝ := confV M alpha (x 0) + mu * (x 1) ^ 2



















end

end BookProof.HermiteQuadraticEsa


