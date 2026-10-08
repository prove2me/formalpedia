-- Prove2me | Definitions.Def_ChapterSirkPerSystemFlowBound
-- name    : ChapterSirkPerSystemFlowBound
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:38:18.779533+00:00
-- url     : https://prove2.me/theorems/9c3dde9c-4131-460e-b645-48d538e7cd90
-- title:
--   ChapterSirkPerSystemFlowBound
-- statement:
--   ChapterSirkPerSystemFlowBound

import Definitions.Def_ChapterSirkPerSystem
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH9
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterSirkSpectralGeometry
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# Chapter SirkPerSystemFlowBound — the per-system end-to-end SIRK bound

`CONSOLIDATED_PLAN.md` §12.4 (definition of done for §12) asks, for each of the
four physical systems, for a **named theorem**

  `‖flow v − V_m ψ(B_m) V_m∗ v‖ ≤ bound(m, {z_j}, t, constants)`

with *every hypothesis discharged from the existing modules* and the constants
explicit.  §12.3 item 1 lists the systems in order (QYM, NS Lagrangian, NS
Eulerian, QG) and item 2 records the standing convention that Crouzeix's
inequality and the `e^{−hm}` deformation stay **named hypotheses with
citations**, never axioms.

The two preceding chapters supply the halves:

* `ChapterSirkEndToEnd.sirk_end_to_end` composes the pipeline with abstract
  constants;
* `ChapterSirkSpectralGeometry` identifies the Crouzeix domain `Σ` of the
  shift-invert (a real segment in the positive regime, a disc at a non-real
  shift), and `ChapterSirkPerSystem` instantiates `Σ` for every system.

What is missing — and is what this chapter adds — is the *composition of the
two*: a single named statement per system in which the selected extension, its
shift-invert, the Crouzeix domain, the Krylov transfer and the reconstruction
projection are all discharged, and the only remaining inputs are the two
Crouzeix estimates on the fixed domain.

## What is new here

* `adjoint_comp_self_of_isometry` / `norm_adjoint_apply_le_of_isometry`: the two
  adjoint hypotheses that every previous statement carried (`hVV` and `hVadj`)
  are **not** independent assumptions — they follow from `‖V x‖ = ‖x‖` alone.
  Every theorem below therefore asks only for isometry.
* `RationalScheme` / `IsSirkScheme`: the data of one order-`m` SIRK step
  (the rational approximant `p/qX`, its reduced denominator inverse, the exact
  and reduced propagators) and the hypotheses on it, bundled so that a
  per-system statement fits on a page and so that a *family* over `m` can be
  quantified for the convergence statements.
* `sirk_scheme_bound`, `sirk_scheme_tendsto`: the generic bound and its `m → ∞`
  convergence in the bundled form.
* The five per-system theorems, each of which produces the generator, its
  shift-invert and the Crouzeix domain from the project's own selection
  theorems and then states the bound and the convergence:
  `ym_sirk_flow_error_bound` / `ym_sirk_flow_error_tendsto_zero` (QYM, the
  Friedrichs route, `Σ = [0, γ⁻¹]`), `ns_sirk_flow_error_bound`,
  `nsDiff_sirk_flow_error_bound` (NS Eulerian, sequence space and differential),
  `diagKR_sirk_flow_error_bound` (NS Lagrangian, the concrete Kato–Rellich
  model), `qgR2_sirk_flow_error_bound` (QG, the `R + αR²` mode Hamiltonian),
  each at a non-real shift with `Σ` the disc of radius `|Im γ|⁻¹`.

## Honest boundary

Crouzeix's inequality and the `e^{−hm}` deformation are the fields `cxX`/`cxB`
of `IsSirkScheme`: named hypotheses, exactly as in `ChapterH4`, and stated on the
*fixed* domain `Σ` so that the constants `C` and `Dmin` do not depend on the
reduction order or on the seed.  The spectral consistency `flow = ψ(X)`
(`ChapterH4.psi_shift_eq_phi`) is likewise a hypothesis of the composition.
Nothing here claims global existence, a continuum mass gap, or anything about
floating-point arithmetic (§12.2 Gap 6; see `ChapterSirkFinitePrecision` for the
certificate layer).  The bound is permitted to depend on `t` through the
constants: the requirement of §12.2 Gap 3 is finiteness for every `t`, not
uniformity in `t`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open Filter Topology

namespace BookProof.ChapterSirkPerSystemFlowBound

open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH9
open BookProof.ChapterSirkEndToEnd BookProof.ChapterSirkSpectralGeometry
open BookProof.ChapterSirkPerSystem
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-! ## 0. An isometric embedding needs no extra adjoint hypotheses -/





/-! ## 1. One order-`m` SIRK step, bundled -/

/-- The data of one order-`m` SIRK step: the rational approximant `p / qX` with a
left inverse `qXinv` of its denominator, the inverse `qBinv` of the reduced
denominator, and the exact and reduced propagators `psiX`, `psiB`. -/
structure RationalScheme (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] where
  /-- The denominator of the rational approximant, evaluated at the generator. -/
  qX : E →L[ℂ] E
  /-- A left inverse of `qX` (the rational approximant is `p(X) qX⁻¹`). -/
  qXinv : E →L[ℂ] E
  /-- A right inverse of the compressed denominator. -/
  qBinv : G →L[ℂ] G
  /-- The numerator polynomial. -/
  p : Polynomial ℂ
  /-- The exact propagator, as a function of the shift-invert. -/
  psiX : E →L[ℂ] E
  /-- The reduced (`m × m`) propagator. -/
  psiB : G →L[ℂ] G

/-- The hypotheses of one order-`m` SIRK step against the generator `X`, the
isometric Krylov embedding `V` and the Crouzeix domain `S`.

`invX`/`invq` are the Krylov invariance of the retained subspace, `qXl`/`qBr` the
invertibility of the denominators, and `cxX`/`cxB` the two Crouzeix estimates —
the named hypotheses of `ChapterH4`, stated *conditionally on the numerical range
lying in `S`*, so that a single pair `(C, Dmin)` measured on `S` serves both. -/
structure IsSirkScheme (X : E →L[ℂ] E) (V : G →L[ℂ] E) (S : Set ℂ) (C Dmin h : ℝ) (m : ℕ)
    (s : RationalScheme E G) : Prop where
  /-- `V` is an isometric embedding of the reduced space. -/
  iso : ∀ x : G, ‖V x‖ = ‖x‖
  /-- The retained subspace is invariant under the generator. -/
  invX : ∀ x : G, ∃ y : G, X (V x) = V y
  /-- The retained subspace is invariant under the denominator. -/
  invq : ∀ x : G, ∃ y : G, s.qX (V x) = V y
  /-- `qXinv` is a left inverse of the denominator. -/
  qXl : s.qXinv.comp s.qX = ContinuousLinearMap.id ℂ E
  /-- `qBinv` is a right inverse of the compressed denominator. -/
  qBr : (compress V s.qX).comp s.qBinv = ContinuousLinearMap.id ℂ G
  /-- Crouzeix on the generator side, on the domain `S`. -/
  cxX : numRange X ⊆ S →
    ‖s.psiX - (Polynomial.aeval X s.p).comp s.qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin)
  /-- Crouzeix on the reduced side, on the same domain `S`. -/
  cxB : numRange (compress V X) ⊆ S →
    ‖s.psiB - (Polynomial.aeval (compress V X) s.p).comp s.qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin)





/-! ## 2. Quantum Yang–Mills: the Friedrichs route, `Σ = [0, γ⁻¹]` -/





/-! ## 3. Navier–Stokes, Eulerian: `Σ` a disc of radius `|Im γ|⁻¹` -/





/-! ## 4. Navier–Stokes, Lagrangian -/





/-! ## 5. Quantum gravity: the `R + αR²` mode Hamiltonian -/





/-! ## 6. Non-vacuity: the scheme hypotheses are satisfiable -/



end BookProof.ChapterSirkPerSystemFlowBound


