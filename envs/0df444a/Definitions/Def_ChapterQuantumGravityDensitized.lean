-- Prove2me | Definitions.Def_ChapterQuantumGravityDensitized
-- name    : ChapterQuantumGravityDensitized
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:42:56.522826+00:00
-- url     : https://prove2.me/theorems/de41f0a8-2c5c-4556-ab56-968008968c9e
-- title:
--   Source: `book.tex`, chapter *"Quantum Gravity"*, §*"Classical Hamiltonian"* / §*"Quantum Hamiltonian"* (~8138–8310), and ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QuantumGravityDensitized`, source chapter `BookProof/ChapterQuantumGravityDensitized.lean`).
--
--   Source: `book.tex`, chapter *"Quantum Gravity"*, §*"Classical Hamiltonian"* / §*"Quantum Hamiltonian"* (~8138–8310), and the plan item recorded in `CONSOLIDATED_PLAN.md` §10 (Parts A–D of the suggested `PLAN_LEAN_SPECIALIST_QG_FLOW.md`).
--
--   The manuscript's 3D gauge-fixed gravity Hamiltonian carries the **singular** kinetic terms
--
--   `H = (1/16 e) S^{ab} S_{ab} − (1/24 e) P² + …`,
--
--   whose `1/e` denominator (`e = det e_i^a`, the tetrad determinant) blows up where the tetrad degenerates. The route the manuscript suggests is the canonical change of variables to **densitized tetrads**
--
--   `y = √e`, `ẽ_i^a = √e · e_i^a`,
--
--   after which the principal part of the kinetic operator is a *flat* d'Alembertian with the constant coefficients `(1/16, −1/24)`.
--
--   **Part A — the change of variables.**
--
--   * `densY`, `densY_sq`, `hasDerivAt_densY`, `deriv_densY` — the new coordinate `y = √e` and its derivative; * `inv_eq_four_mul_deriv_densY_sq` — the **absorption identity** `1/e = 4 (∂y/∂e)²`: the singular denominator is a *square of a derivative of the new coordinate*, hence absorbed into the field derivatives. (The plan's prose writes `1/e = (∂y/∂e)²`; the honest identity carries the factor `4`, because `∂√e/∂e = 1/(2√e)`.) * `kinetic_absorption`, `conformal_absorption` — the two singular kinetic terms in densitized form: `(1/16e)S² = (1/16)(S/y)²` and `(1/24e)P² = (1/24)(P/y)²`, i.e. the coefficients become **constants** once the fields are densitized; * `densTetrad`, `densTetrad_det`, `densTetrad_recover` — the densitized tetrad `ẽ = √e · e`, its determinant and the inverse map where `e > 0`; * `tendsto_inv_det_atTop` versus `tendsto_densY_zero` — the honest statement of what the change of variables buys: `1/e → ∞` at a degenerate tetrad, while the new coordinate `y = √e` extends continuously by `0`.
--
--   **Part B — the flat principal part.**
--
--   * `qgSymbol` — the principal symbol `(1/16)Σξ_a² − (1/24)ξ_y²`; `qgSymbol_homogeneous` (it is a quadratic form), `qgSymbol_eq_metric_form` (it is the form of the constant metric `qgMetric`); * `qgMetric_det_ne_zero` — the field-space metric is non-degenerate, and `qgSymbol_pos` / `qgSymbol_neg` / `qgSymbol_indefinite` — it is **indefinite**: the operator is hyperbolic (a d'Alembertian), *not* elliptic. This is exactly why the elliptic Sears/Kato–Rellich route of the Navier–Stokes chapters does not apply and Strichartz's hyperbolic theorem is the named input; * `christoffel_eq_zero_of_const`, `qgMetric_christoffel_zero` — for a **constant** field-space metric every Christoffel symbol vanishes; this is the precise form of the plan's remark that the densitized coordinates are flat, so the point transformation produces no connection ("quantum potential") corrections; * `qgFullSymbol`, `qgFullSymbol_scaling` — the operator-order decomposition (2nd + 1st + 0th) as the scaling law of the full symbol.
--
--   **Part C — a realization on which the analytic hypotheses are *proved*.** In the Hermite (oscillator) basis the fiber operator is multiplication by the mode symbol `λ_k = (1/16)a_k² − (1/24)b_k² + V_k`, and for that realization
--
--   * `qgModeHamiltonian_essentiallySelfAdjoint` — the operator is essentially self-adjoint on its maximal domain in `ℓ²(ℕ)`, * `qgModeHamiltonian_deficiencyTrivialAt` — the deficiency space of the adjoint is trivial at **every** non-real `z` (the conclusion Strichartz's finite-speed argument is supposed to deliver in the continuum), and * `qgModeHamiltonian_not_bounded` — the operator really is unbounded, so the statement is not a bounded-operator triviality.
--
--   **Part D — Strichartz as a *named hypothesis*, never an axiom.**
--
--   * `strichartz_esa_of_finiteSpeed` — the deduction step: the finite-speed / unique-continuation input `ker(H* − z) = 0` for `Im z ≠ 0` (P. R. Chernoff, *Essential self-adjointness of powers of generators of hyperbolic e
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravityDensitized.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib

import Mathlib

/-!
# Quantum gravity: the densitized tetrad variables and the flat principal part

Source: `book.tex`, chapter *"Quantum Gravity"*, §*"Classical Hamiltonian"* /
§*"Quantum Hamiltonian"* (~8138–8310), and the plan item recorded in
`CONSOLIDATED_PLAN.md` §10 (Parts A–D of the suggested
`PLAN_LEAN_SPECIALIST_QG_FLOW.md`).

The manuscript's 3D gauge-fixed gravity Hamiltonian carries the **singular**
kinetic terms

  `H = (1/16 e) S^{ab} S_{ab} − (1/24 e) P² + …`,

whose `1/e` denominator (`e = det e_i^a`, the tetrad determinant) blows up where
the tetrad degenerates.  The route the manuscript suggests is the canonical
change of variables to **densitized tetrads**

  `y = √e`,  `ẽ_i^a = √e · e_i^a`,

after which the principal part of the kinetic operator is a *flat*
d'Alembertian with the constant coefficients `(1/16, −1/24)`.

## What is proved here (Parts A–D, all `sorry`-free and `axiom`-free)

**Part A — the change of variables.**

* `densY`, `densY_sq`, `hasDerivAt_densY`, `deriv_densY` — the new coordinate
  `y = √e` and its derivative;
* `inv_eq_four_mul_deriv_densY_sq` — the **absorption identity**
  `1/e = 4 (∂y/∂e)²`: the singular denominator is a *square of a derivative of
  the new coordinate*, hence absorbed into the field derivatives.  (The plan's
  prose writes `1/e = (∂y/∂e)²`; the honest identity carries the factor `4`,
  because `∂√e/∂e = 1/(2√e)`.)
* `kinetic_absorption`, `conformal_absorption` — the two singular kinetic terms
  in densitized form: `(1/16e)S² = (1/16)(S/y)²` and `(1/24e)P² = (1/24)(P/y)²`,
  i.e. the coefficients become **constants** once the fields are densitized;
* `densTetrad`, `densTetrad_det`, `densTetrad_recover` — the densitized tetrad
  `ẽ = √e · e`, its determinant and the inverse map where `e > 0`;
* `tendsto_inv_det_atTop` versus `tendsto_densY_zero` — the honest statement of
  what the change of variables buys: `1/e → ∞` at a degenerate tetrad, while
  the new coordinate `y = √e` extends continuously by `0`.

**Part B — the flat principal part.**

* `qgSymbol` — the principal symbol `(1/16)Σξ_a² − (1/24)ξ_y²`;
  `qgSymbol_homogeneous` (it is a quadratic form),
  `qgSymbol_eq_metric_form` (it is the form of the constant metric `qgMetric`);
* `qgMetric_det_ne_zero` — the field-space metric is non-degenerate, and
  `qgSymbol_pos` / `qgSymbol_neg` / `qgSymbol_indefinite` — it is **indefinite**:
  the operator is hyperbolic (a d'Alembertian), *not* elliptic.  This is exactly
  why the elliptic Sears/Kato–Rellich route of the Navier–Stokes chapters does
  not apply and Strichartz's hyperbolic theorem is the named input;
* `christoffel_eq_zero_of_const`, `qgMetric_christoffel_zero` — for a **constant**
  field-space metric every Christoffel symbol vanishes; this is the precise form
  of the plan's remark that the densitized coordinates are flat, so the point
  transformation produces no connection ("quantum potential") corrections;
* `qgFullSymbol`, `qgFullSymbol_scaling` — the operator-order decomposition
  (2nd + 1st + 0th) as the scaling law of the full symbol.

**Part C — a realization on which the analytic hypotheses are *proved*.**  In
the Hermite (oscillator) basis the fiber operator is multiplication by the mode
symbol `λ_k = (1/16)a_k² − (1/24)b_k² + V_k`, and for that realization

* `qgModeHamiltonian_essentiallySelfAdjoint` — the operator is essentially
  self-adjoint on its maximal domain in `ℓ²(ℕ)`,
* `qgModeHamiltonian_deficiencyTrivialAt` — the deficiency space of the adjoint
  is trivial at **every** non-real `z` (the conclusion Strichartz's finite-speed
  argument is supposed to deliver in the continuum), and
* `qgModeHamiltonian_not_bounded` — the operator really is unbounded, so the
  statement is not a bounded-operator triviality.

**Part D — Strichartz as a *named hypothesis*, never an axiom.**

* `strichartz_esa_of_finiteSpeed` — the deduction step: the finite-speed /
  unique-continuation input `ker(H* − z) = 0` for `Im z ≠ 0` (P. R. Chernoff,
  *Essential self-adjointness of powers of generators of hyperbolic equations*,
  J. Funct. Anal. **12** (1973) 401–414; the earlier "Strichartz, 13 82–93"
  was a misattribution) yields essential self-adjointness;
* `strichartz_finiteSpeed_satisfiable` — the hypothesis is **not vacuous**: the
  discretized realization of Part C satisfies it;
* `qg_esa_of_farisLavine` — the alternative route, through the *proved*
  Faris–Lavine criterion of `BookProof.ChapterFarisLavine`;
* `densitized_hasZeroDeficiencyOn_transfer` — the transfer step of
  `CONSOLIDATED_PLAN.md` §10.3: once the change of variables is made unitary by
  the Jacobian half-density factor, essential self-adjointness of the flat
  (densitized) operator gives it for the physical one.

## Scope (unchanged honesty discipline)

Nothing here claims essential self-adjointness of the **continuum** gravity
operator on `L²(ℝ⁸⁴ × ℤ₂¹⁹)`, nor global existence, nor any unitary-evolution
statement for it.  The continuum conclusion needs the Strichartz input for the
flat d'Alembertian with a polynomial potential, which enters *only* as the
explicit hypothesis of `strichartz_esa_of_finiteSpeed`.
-/

namespace BookProof.QuantumGravityDensitized

open Filter Topology BookProof.FarisLavine

/-! ## Part A — the densitized change of variables -/

/-- The densitized conformal coordinate `y = √e`, `e = det e_i^a`. -/
noncomputable def densY (e : ℝ) : ℝ := Real.sqrt e





















/-- The **densitized tetrad** `ẽ_i^a = √e · e_i^a`. -/
noncomputable def densTetrad (E : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Real.sqrt E.det • E









/-! ## Part B — the flat principal part -/

/-- The **principal symbol** of the transformed kinetic operator,
`(1/16) Σ_a ξ_a² − (1/24) ξ_y²`: a flat d'Alembertian in the densitized
variables. -/
noncomputable def qgSymbol {n : ℕ} (xi : Fin n → ℝ) (xiY : ℝ) : ℝ :=
  1 / 16 * ∑ a, (xi a) ^ 2 - 1 / 24 * xiY ^ 2



/-- The **flat field-space metric** of the densitized variables:
`diag(1/16, …, 1/16, −1/24)`. -/
noncomputable def qgMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal fun i => if i = Fin.last n then -(1 / 24) else 1 / 16





/-- The momenta assembled into one covector `(ξ_a, ξ_y)` of field space. -/
def qgMomenta {n : ℕ} (xi : Fin n → ℝ) (xiY : ℝ) : Fin (n + 1) → ℝ := Fin.snoc xi xiY













/-- The directional derivative of a field-space metric coefficient. -/
noncomputable def metricDeriv {m : ℕ} (g : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (q : EuclideanSpace ℝ (Fin m)) (i k l : Fin m) : ℝ :=
  fderiv ℝ (fun p => g p k l) q (EuclideanSpace.single i 1)

/-- The Christoffel symbols of a field-space metric `g` with inverse `ginv`. -/
noncomputable def christoffel {m : ℕ} (g ginv : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (q : EuclideanSpace ℝ (Fin m)) (k i j : Fin m) : ℝ :=
  1 / 2 * ∑ l, ginv q k l *
    (metricDeriv g q i l j + metricDeriv g q j l i - metricDeriv g q l i j)





/-- The **full symbol** of the transformed Hamiltonian: principal part (order 2)
plus a first-order part `b·ξ` plus the potential `−Ṽ`. -/
noncomputable def qgFullSymbol {n : ℕ} (xi : Fin n → ℝ) (xiY : ℝ)
    (b : Fin n → ℝ) (bY : ℝ) (V : ℝ) : ℝ :=
  qgSymbol xi xiY + ((∑ a, b a * xi a) + bY * xiY) - V



/-! ## Part C — the Hermite-basis realization, where the hypotheses are proved -/

/-- The **mode symbol** of the transformed gravity Hamiltonian in the Hermite
(oscillator) basis: `λ_k = (1/16) a_k² − (1/24) b_k² + V_k`, the hyperbolic
principal part plus the potential, mode by mode. -/
noncomputable def qgModeSymbol (a b V : ℕ → ℝ) (k : ℕ) : ℝ :=
  1 / 16 * (a k) ^ 2 - 1 / 24 * (b k) ^ 2 + V k

/-- The gravity fiber operator in the Hermite basis: multiplication by the mode
symbol on its maximal domain in `ℓ²(ℕ)`. -/
noncomputable def qgModeHamiltonian (a b V : ℕ → ℝ) :
    mulSymbolDomain (qgModeSymbol a b V) →ₗ[ℂ] L2Nat :=
  mulHamiltonian (qgModeSymbol a b V)











/-! ## Part D — Strichartz as a named hypothesis, and the transfer step -/

section Strichartz

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



end Strichartz



section FarisLavineRoute

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



end FarisLavineRoute

section Transfer


variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]



end Transfer

end BookProof.QuantumGravityDensitized


