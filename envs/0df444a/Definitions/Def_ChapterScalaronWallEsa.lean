-- Prove2me | Definitions.Def_ChapterScalaronWallEsa
-- name    : ChapterScalaronWallEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T20:18:27.176196+00:00
-- url     : https://prove2.me/theorems/5e79561f-2c3c-4421-babf-3b75d3600137
-- title:
--   The exponential scalaron wall: `−d²/dφ² + V` is essentially self-adjoint The non-perturbative argument What is proved
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ScalaronWallEsa`, source chapter `BookProof/ChapterScalaronWallEsa.lean`): The exponential scalaron wall: `−d²/dφ² + V` is essentially self-adjoint The non-perturbative argument What is proved
--
--   `CONSOLIDATED_PLAN.md` §10.6.1/§10.6.2 leaves one item of the quantum-gravity chapter open: the Schrödinger operator with the **exponentially growing** Einstein-frame scalaron wall
--
--   `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`,
--
--   whose growth as `φ → −∞` beats every polynomial (`starobinskyV_not_hasTemperateGrowth`). Every route the project had tried was perturbative relative to the harmonic (Gauss/Hermite) core, and each of them is *refuted* for such a wall: relative boundedness fails (`BookProof/ChapterHermiteExpWall.lean`) and the Carleman flux criterion is inapplicable because `∑ 1/Aₙ` converges. `BookProof/ChapterScalaronCoreEsa.lean` settles the multiplication operator alone; what was missing is the **sum** `−d²/dφ² + V`.
--
--   For a *non-negative* potential the classical argument needs no perturbation theory at all. A deficiency vector `u ∈ L²(ℝ)` at `z = ±i` satisfies the differential equation `u'' = (V − z)u` in the sense of distributions. The regularity toolkit of `BookProof/ChapterWeakSecondDerivative.lean` upgrades it to a genuine `C²` solution `W` with `u = W` almost everywhere, and then
--
--   `(|W|²)'' = 2 Re(conj W · W'') + 2|W'|² = 2 (V − Re z)|W|² + 2|W'|² ≥ 0`
--
--   because `Re z = 0` and `V ≥ 0`. So `|W|²` is a **convex**, non-negative and *integrable* function on the whole line — and such a function vanishes identically (`eq_zero_of_convexOn_nonneg_integrable`: convexity forces `F(a−s) + F(a+s) ≥ 2F(a)`, so `2 F(a) R ≤ ∫ F` for every `R`). Hence `u = 0`, both deficiency spaces are trivial and the operator is essentially self-adjoint.
--
--   * `eq_zero_of_convexOn_nonneg_integrable` — a non-negative integrable convex function on `ℝ` is zero; * `ode_solution_eq_zero` — the ODE step: an `L²` solution of `W'' = (V − z)W` with `V ≥ 0` and `Re z = 0` vanishes; * `wallHam` — the operator `−d²/dφ² + V` on the compactly supported smooth core of `L²(ℝ)`, with `wallHam_symmetricOn`; * `wallHam_weak_eq` — the deficiency equation in distributional form; * **`wallHam_essentiallySelfAdjoint`** — essential self-adjointness for *every* smooth `V ≥ 0`, with no growth hypothesis whatsoever; * `starobinskyWall_esa` — the scalaron instance, and `starobinskyWall_stone_flow` its unitary group `e^{−itH}`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

import Definitions.Def_ChapterWeakSecondDerivative
import Definitions.Def_ChapterScalaronCoreEsa
import Mathlib
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave


/-!
# The exponential scalaron wall: `−d²/dφ² + V` is essentially self-adjoint

`CONSOLIDATED_PLAN.md` §10.6.1/§10.6.2 leaves one item of the quantum-gravity chapter open:
the Schrödinger operator with the **exponentially growing** Einstein-frame scalaron wall

`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`,

whose growth as `φ → −∞` beats every polynomial (`starobinskyV_not_hasTemperateGrowth`).
Every route the project had tried was perturbative relative to the harmonic (Gauss/Hermite)
core, and each of them is *refuted* for such a wall: relative boundedness fails
(`BookProof/ChapterHermiteExpWall.lean`) and the Carleman flux criterion is inapplicable
because `∑ 1/Aₙ` converges.  `BookProof/ChapterScalaronCoreEsa.lean` settles the
multiplication operator alone; what was missing is the **sum** `−d²/dφ² + V`.

## The non-perturbative argument

For a *non-negative* potential the classical argument needs no perturbation theory at all.
A deficiency vector `u ∈ L²(ℝ)` at `z = ±i` satisfies the differential equation
`u'' = (V − z)u` in the sense of distributions.  The regularity toolkit of
`BookProof/ChapterWeakSecondDerivative.lean` upgrades it to a genuine `C²` solution `W`
with `u = W` almost everywhere, and then

`(|W|²)'' = 2 Re(conj W · W'') + 2|W'|² = 2 (V − Re z)|W|² + 2|W'|² ≥ 0`

because `Re z = 0` and `V ≥ 0`.  So `|W|²` is a **convex**, non-negative and *integrable*
function on the whole line — and such a function vanishes identically
(`eq_zero_of_convexOn_nonneg_integrable`: convexity forces
`F(a−s) + F(a+s) ≥ 2F(a)`, so `2 F(a) R ≤ ∫ F` for every `R`).  Hence `u = 0`, both
deficiency spaces are trivial and the operator is essentially self-adjoint.

## What is proved

* `eq_zero_of_convexOn_nonneg_integrable` — a non-negative integrable convex function on
  `ℝ` is zero;
* `ode_solution_eq_zero` — the ODE step: an `L²` solution of `W'' = (V − z)W` with `V ≥ 0`
  and `Re z = 0` vanishes;
* `wallHam` — the operator `−d²/dφ² + V` on the compactly supported smooth core of `L²(ℝ)`,
  with `wallHam_symmetricOn`;
* `wallHam_weak_eq` — the deficiency equation in distributional form;
* **`wallHam_essentiallySelfAdjoint`** — essential self-adjointness for *every* smooth
  `V ≥ 0`, with no growth hypothesis whatsoever;
* `starobinskyWall_esa` — the scalaron instance, and `starobinskyWall_stone_flow` its
  unitary group `e^{−itH}`.
-/

namespace BookProof.ScalaronWallEsa

open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

/-! ## 1. A non-negative integrable convex function on the line vanishes -/



/-! ## 2. The ODE step -/



/-! ## 3. The Schrödinger operator on the compactly supported smooth core of `L²(ℝ)` -/

/-- The one-dimensional kinetic operator `−d²/dx²` on Schwartz space. -/
def kinOpR : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  constCoeffOp (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) 0



/-- The kinetic term on the compactly supported smooth core of `L²(ℝ)`. -/
def kinCcR : ccDomain ℝ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  opL2 kinOpR ∘ₗ Submodule.inclusion (ccDomain_le_schwartzDomain (E := ℝ))

/-- **The Schrödinger operator `−d²/dx² + V`** on the compactly supported smooth core of
`L²(ℝ)`, for an arbitrary smooth real potential. -/
def wallHam (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ccDomain ℝ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  kinCcR + opCc V hV





/-! ## 4. The deficiency equation in distributional form -/



/-- A real test function, viewed as an element of the compactly supported smooth core.

`IsTestFun` is published as the bare conjunction `ContDiff ℝ ⊤ g ∧ HasCompactSupport g`
(`Def_ChapterWeakSecondDerivative`); the `IsTestFun.contDiff` / `.hasCompactSupport`
source lemmas are not part of that module, so the projections `hg.1` / `hg.2` are used
directly. -/
def testCc {g : ℝ → ℝ} (hg : IsTestFun g) : ccSchwartz ℝ :=
  ⟨(HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hg.2
      (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg.1),
    HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hg.2 (by simp)⟩





/-! ## 5. Essential self-adjointness -/





/-! ## 6. The scalaron wall -/





end

end BookProof.ScalaronWallEsa


