-- Prove2me | Definitions.Def_ChapterStarobinskyPotential
-- name    : ChapterStarobinskyPotential
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:43:16.559305+00:00
-- url     : https://prove2.me/theorems/c54e4622-7fe2-430a-9a00-45af510bdcbb
-- title:
--   Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), steps 1 and — at the mode level — 3/4.
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StarobinskyPotential`, source chapter `BookProof/ChapterStarobinskyPotential.lean`).
--
--   Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), steps 1 and — at the mode level — 3/4.
--
--   The `f(R) = (M²/2)R + αR²` extension of the Einstein–Hilbert action is the one whose extra term *regularizes* the conformal mode: the linear `−(M²/2)R_c` term, whose negative conformal-mode gradient energy leaves pure general relativity unbounded below, is turned by the positive `αR_c²` into a parabola bounded below by `−M⁴/(16α)`.
--
--   **1. The ghost-free scalar–tensor form.** With `ψ = 1 + 4αR/M²` and `U(ψ) = (M⁴/16α)(ψ − 1)²`, `fR_eq_scalarTensor` is the identity `f(R) = (M²/2)ψR − U(ψ)`: `R + αR²` gravity is a *second-order* scalar–tensor theory.
--
--   **2. The Einstein-frame scalaron potential.** `starobinskyV M α φ = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` is manifestly a square, hence * `starobinskyV_nonneg` — non-negative, the strongest form of the correct (elliptic) sign; * `starobinskyV_zero` — vanishing at `φ = 0`, the flat Minkowski vacuum; * `starobinskyV_tendsto_plateau` — the large-field plateau `M⁴/(16α)`; * `starobinskyV_tendsto_atBot_atTop` — the exponential wall as `φ → −∞`.
--
--   **3. The conformal-mode potential and its regularization.** * `confV_completed_square` — `V₃(R_c) = α(R_c − M²/(4α))² − M⁴/(16α)`; * `confV_ge`, `confV_bddBelow` — bounded below by `−M⁴/(16α)` for `α > 0`; * `confV_zero_alpha_tendsto_atBot` — and *not* bounded below when `α = 0`: this is exactly what the `αR²` term buys.
--
--   **4. The mode Hamiltonian, its essential self-adjointness and its flow.** In the densitized variables the gravity fiber operator is multiplication by the mode symbol `(1/16)a_k² − (1/24)b_k² + V_k` (`BookProof.ChapterQuantumGravityDensitized`); with the Starobinsky conformal-mode potential `V_k = V₃(R_c k)` this is `qgR2ModeHamiltonian`, and * `qgR2Mode_potential_ge` — its potential part is bounded below by `−M⁴/(16α)`, uniformly in the mode, which is the regularization at the level of the operator; * `qgR2Mode_esa` — it is essentially self-adjoint on its maximal domain (deficiency trivial at every non-real `z`, `qgR2Mode_deficiencyTrivialAt`); * `mulSymbolDomain_dense` — that domain is dense (it contains the finitely supported states); * **`qgR2_stone_flow`** — hence, through the Stone bridge, it generates the complete unitary group `e^{−itH}` solving the Schrödinger equation on its domain: the first continuous flow for the gauge-fixed `R + αR²` gravity Hamiltonian in this development, the QG analogue of `ns_stone_flow` / `ym_fock_stone_flow`.
--
--   Unchanged from `CONSOLIDATED_PLAN.md` §10.3/§10.5. The flow above is that of the *mode* (Hermite-basis) realization, where the fiber operator is a multiplication operator; the continuum `L²(ℝ⁸⁴)` statement with the full polynomial potential still needs the Strichartz finite-speed / direct-integral input, and the gauge/BRST sector is outside the statement. No mass gap and no global existence is claimed. The potentials formalized here are the mathematics of the derivation, not the symbolic-algebra program that produced it.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStarobinskyPotential.lean

import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized

import Mathlib

/-!
# The R + αR² (Starobinsky) potentials, and the flow of the regularized conformal mode

Plan item **A5** (`CONSOLIDATED_PLAN.md` §10.5), steps 1 and — at the mode level — 3/4.

The `f(R) = (M²/2)R + αR²` extension of the Einstein–Hilbert action is the one whose extra
term *regularizes* the conformal mode: the linear `−(M²/2)R_c` term, whose negative
conformal-mode gradient energy leaves pure general relativity unbounded below, is turned by
the positive `αR_c²` into a parabola bounded below by `−M⁴/(16α)`.

## What is proved

**1. The ghost-free scalar–tensor form.**  With `ψ = 1 + 4αR/M²` and
`U(ψ) = (M⁴/16α)(ψ − 1)²`, `fR_eq_scalarTensor` is the identity
`f(R) = (M²/2)ψR − U(ψ)`: `R + αR²` gravity is a *second-order* scalar–tensor theory.

**2. The Einstein-frame scalaron potential.**  `starobinskyV M α φ = (M⁴/16α)(1 −
e^{−√(2/3)φ/M})²` is manifestly a square, hence
* `starobinskyV_nonneg` — non-negative, the strongest form of the correct (elliptic) sign;
* `starobinskyV_zero` — vanishing at `φ = 0`, the flat Minkowski vacuum;
* `starobinskyV_tendsto_plateau` — the large-field plateau `M⁴/(16α)`;
* `starobinskyV_tendsto_atBot_atTop` — the exponential wall as `φ → −∞`.

**3. The conformal-mode potential and its regularization.**
* `confV_completed_square` — `V₃(R_c) = α(R_c − M²/(4α))² − M⁴/(16α)`;
* `confV_ge`, `confV_bddBelow` — bounded below by `−M⁴/(16α)` for `α > 0`;
* `confV_zero_alpha_tendsto_atBot` — and *not* bounded below when `α = 0`: this is exactly
  what the `αR²` term buys.

**4. The mode Hamiltonian, its essential self-adjointness and its flow.**  In the
densitized variables the gravity fiber operator is multiplication by the mode symbol
`(1/16)a_k² − (1/24)b_k² + V_k` (`BookProof.ChapterQuantumGravityDensitized`); with the
Starobinsky conformal-mode potential `V_k = V₃(R_c k)` this is `qgR2ModeHamiltonian`, and
* `qgR2Mode_potential_ge` — its potential part is bounded below by `−M⁴/(16α)`, uniformly
  in the mode, which is the regularization at the level of the operator;
* `qgR2Mode_esa` — it is essentially self-adjoint on its maximal domain (deficiency trivial
  at every non-real `z`, `qgR2Mode_deficiencyTrivialAt`);
* `mulSymbolDomain_dense` — that domain is dense (it contains the finitely supported
  states);
* **`qgR2_stone_flow`** — hence, through the Stone bridge, it generates the complete unitary
  group `e^{−itH}` solving the Schrödinger equation on its domain: the first continuous flow
  for the gauge-fixed `R + αR²` gravity Hamiltonian in this development, the QG analogue of
  `ns_stone_flow` / `ym_fock_stone_flow`.

## Honest boundary

Unchanged from `CONSOLIDATED_PLAN.md` §10.3/§10.5.  The flow above is that of the
*mode* (Hermite-basis) realization, where the fiber operator is a multiplication operator;
the continuum `L²(ℝ⁸⁴)` statement with the full polynomial potential still needs the
Strichartz finite-speed / direct-integral input, and the gauge/BRST sector is outside the
statement.  No mass gap and no global existence is claimed.  The potentials formalized here
are the mathematics of the derivation, not the symbolic-algebra program that produced it.
-/

open Filter Topology
open BookProof.FarisLavine BookProof.QuantumGravityDensitized

namespace BookProof.Starobinsky


noncomputable section

/-! ## 1. The `f(R)` function and its scalar–tensor form -/

/-- The Starobinsky Lagrangian function `f(R) = (M²/2)R + αR²`. -/
def fR (M alpha R : ℝ) : ℝ := M ^ 2 / 2 * R + alpha * R ^ 2

/-- The scalar-tensor field `ψ = 1 + 4αR/M²`. -/
def scalaron (M alpha R : ℝ) : ℝ := 1 + 4 * alpha * R / M ^ 2

/-- The scalar-tensor potential `U(ψ) = (M⁴/16α)(ψ − 1)²`. -/
def Upot (M alpha psi : ℝ) : ℝ := M ^ 4 / (16 * alpha) * (psi - 1) ^ 2



/-! ## 2. The Einstein-frame scalaron potential -/

/-- The Einstein-frame scalaron potential
`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²`. -/
def starobinskyV (M alpha phi : ℝ) : ℝ :=
  M ^ 4 / (16 * alpha) * (1 - Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) ^ 2









/-! ## 3. The conformal-mode potential, and what `αR²` buys -/

/-- The conformal-mode spatial potential `V₃(R_c) = −(M²/2)R_c + αR_c²`. -/
def confV (M alpha Rc : ℝ) : ℝ := -(M ^ 2 / 2) * Rc + alpha * Rc ^ 2









/-! ## 4. The mode Hamiltonian, its essential self-adjointness and its unitary flow -/





variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc : ℕ → ℝ)

/-- The Starobinsky conformal-mode potential, mode by mode. -/
def qgR2ModePotential : ℕ → ℝ := fun k => confV M alpha (Rc k)

/-- **The `R + αR²` gravity mode Hamiltonian** in the densitized (Hermite-basis)
realization: multiplication by `(1/16)a_k² − (1/24)b_k² + V₃(R_c k)`. -/
def qgR2ModeHamiltonian :
    mulSymbolDomain (qgModeSymbol a b (qgR2ModePotential M alpha Rc)) →ₗ[ℂ] L2Nat :=
  qgModeHamiltonian a b (qgR2ModePotential M alpha Rc)











end

end BookProof.Starobinsky


