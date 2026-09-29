-- Prove2me | Definitions.Def_ChapterNavierStokesDiffFarisLavine
-- name    : ChapterNavierStokesDiffFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T11:32:28.272426+00:00
-- url     : https://prove2.me/theorems/4a7bbbef-1303-4e5c-b19b-ecfbf6e7206f
-- title:
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` and `BookProof.ChapterNavierStokesFockManyMode` prove the two Faris–La ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesDiffFarisLavine`, source chapter `BookProof/ChapterNavierStokesDiffFarisLavine.lean`).
--
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` and `BookProof.ChapterNavierStokesFockManyMode` prove the two Faris–Lavine inequalities — the relative bound `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` and the form-commutator bound `±i[H, N] ≤ c N` — in the *sequence* (occupation-number) realization, and `BookProof.ChapterNavierStokesDifferentialL2` proves essential self-adjointness of the Navier–Stokes quadratic symbol written as an honest differential operator on `L²(du₁du₂du₃)`, but by transporting the sequence-space theorem along the Hermite basis. This module supplies the missing layer: the two Faris–Lavine inequalities **for the differential operator itself**, against a differential comparison operator, and the resulting Faris–Lavine proof of essential self-adjointness in `L²(ℝ³)`.
--
--   On the Gauss–polynomial (Hermite) core `polyGaussCore` of `L²(ℝ³)`, with `πᵢ = −i ∂/∂uᵢ` (`momOp`) and `uᵢ` multiplication by the coordinate (`posOp`):
--
--   * the Hamiltonian is the Weyl quantization `nsDiffH A c = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` of the Navier–Stokes quadratic symbol `A_i(u) = u_j u_{i,j} − ν u_{i,jj}`, `Vᵢ = ∑ₖA_{iₖ}uₖ + cᵢ` (`BookProof.ChapterNavierStokesDifferentialL2`); * the comparison operator is the *differential* harmonic-oscillator operator `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, whose one-mode blocks are the honest second-order operators `−∂²/∂uᵢ² + uᵢ²/4`.
--
--   `oscOp_eq_number` is the algebraic heart of the identification: on the Gauss–polynomial core, `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½`, proved as a polynomial identity (`oscPoly_eq`) from the Leibniz rule `∂ᵢ(uᵢp) = p + uᵢ∂ᵢp`. Hence `nsDiffN μ` is the transport of multiplication by the comparison symbol `velSym μ β = μ(2|β| + 3) + 1` (`intertwined_nsDiffN`, `velNcore_eq_diagMax`), and `embedCore_surjective` says the Gauss–polynomial core *is* the transported finite-mode core, so every statement about core states is a statement about all of `polyGaussCore`.
--
--   * `nsDiffN_symmetricOn`, `nsDiffN_quadForm_ge_norm_sq` — the differential comparison operator is symmetric and dominates the identity (`⟪f, Nf⟫ ≥ ‖f‖²`); * `nsDiffH_relative_bound` — **the first Faris–Lavine inequality** for the differential operator: `‖H f‖² ≤ a‖N f‖² + b‖f‖²` on the Hermite core, for every real velocity gradient `A` and constant part `c`; * `nsDiffH_commForm_bound` — **the second Faris–Lavine inequality**: `|⟪f, i[H, N] f⟫| ≤ c ⟪f, N f⟫`; * `diffMaxDom`, `diffMaxH`, `diffMaxN` — the same pair on the maximal domain of the comparison operator in `L²(ℝ³)`, with the Faris–Lavine package there (`diffMaxH_symmetricOn`, `diffMaxN_quadForm_nonneg`, `diffMaxN_add_one_surjective`, `diffMaxN_core_approx`, `diffMaxH_relative_bound`, `diffMaxH_commForm_bound`) and `diffMaxH_restrict`, which identifies its restriction to the Hermite core with `nsDiffH`; * `nsDiffH_esa_of_farisLavine` — **the payoff**: essential self-adjointness of the differentially written Navier–Stokes symbol on the Hermite core of `L²(du₁du₂du₃)`, obtained from the Faris–Lavine criterion of `BookProof.ChapterFarisLavine` applied in `L²(ℝ³)` itself — the alternative route to `BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`, which transported essential self-adjointness instead of the estimates.
--
--   The estimates are the transported sequence-space ones: the mathematics unifying the two pictures is the identification `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` and the fact that the Gauss–polynomial core is the transported finite-mode core, not a new analytic input. The non-vacuity of the mechanism (a genuinely non-zero commutator `[H, N]`, and an unbounded `H`) is recorded in `BookProof.ChapterNavierStokesHermiteFarisLavine.commForm_ne_zero_of_pos`, `BookProof.ChapterNavierStokesFockManyMode.fock_commForm_ne_zero` and `BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_not_bounded`. As everywhere on
--
--   ...
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean

import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Mathlib

import Mathlib

/-!
# The two Faris–Lavine inequalities for the *differential* Navier–Stokes symbol

`BookProof.ChapterNavierStokesHermiteFarisLavine` and
`BookProof.ChapterNavierStokesFockManyMode` prove the two Faris–Lavine inequalities — the
relative bound `‖Hx‖² ≤ a‖Nx‖² + b‖x‖²` and the form-commutator bound
`±i[H, N] ≤ c N` — in the *sequence* (occupation-number) realization, and
`BookProof.ChapterNavierStokesDifferentialL2` proves essential self-adjointness of the
Navier–Stokes quadratic symbol written as an honest differential operator on
`L²(du₁du₂du₃)`, but by transporting the sequence-space theorem along the Hermite basis.
This module supplies the missing layer: the two Faris–Lavine inequalities **for the
differential operator itself**, against a differential comparison operator, and the
resulting Faris–Lavine proof of essential self-adjointness in `L²(ℝ³)`.

## The two operators

On the Gauss–polynomial (Hermite) core `polyGaussCore` of `L²(ℝ³)`, with `πᵢ = −i ∂/∂uᵢ`
(`momOp`) and `uᵢ` multiplication by the coordinate (`posOp`):

* the Hamiltonian is the Weyl quantization `nsDiffH A c = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` of the
  Navier–Stokes quadratic symbol `A_i(u) = u_j u_{i,j} − ν u_{i,jj}`, `Vᵢ = ∑ₖA_{iₖ}uₖ + cᵢ`
  (`BookProof.ChapterNavierStokesDifferentialL2`);
* the comparison operator is the *differential* harmonic-oscillator operator
  `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, whose one-mode blocks are the honest
  second-order operators `−∂²/∂uᵢ² + uᵢ²/4`.

`oscOp_eq_number` is the algebraic heart of the identification: on the Gauss–polynomial
core, `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½`, proved as a polynomial identity (`oscPoly_eq`) from the
Leibniz rule `∂ᵢ(uᵢp) = p + uᵢ∂ᵢp`.  Hence `nsDiffN μ` is the transport of multiplication
by the comparison symbol `velSym μ β = μ(2|β| + 3) + 1` (`intertwined_nsDiffN`,
`velNcore_eq_diagMax`), and `embedCore_surjective` says the Gauss–polynomial core *is* the
transported finite-mode core, so every statement about core states is a statement about
all of `polyGaussCore`.

## What is proved

* `nsDiffN_symmetricOn`, `nsDiffN_quadForm_ge_norm_sq` — the differential comparison
  operator is symmetric and dominates the identity (`⟪f, Nf⟫ ≥ ‖f‖²`);
* `nsDiffH_relative_bound` — **the first Faris–Lavine inequality** for the differential
  operator: `‖H f‖² ≤ a‖N f‖² + b‖f‖²` on the Hermite core, for every real velocity
  gradient `A` and constant part `c`;
* `nsDiffH_commForm_bound` — **the second Faris–Lavine inequality**:
  `|⟪f, i[H, N] f⟫| ≤ c ⟪f, N f⟫`;
* `diffMaxDom`, `diffMaxH`, `diffMaxN` — the same pair on the maximal domain of the
  comparison operator in `L²(ℝ³)`, with the Faris–Lavine package there
  (`diffMaxH_symmetricOn`, `diffMaxN_quadForm_nonneg`, `diffMaxN_add_one_surjective`,
  `diffMaxN_core_approx`, `diffMaxH_relative_bound`, `diffMaxH_commForm_bound`) and
  `diffMaxH_restrict`, which identifies its restriction to the Hermite core with
  `nsDiffH`;
* `nsDiffH_esa_of_farisLavine` — **the payoff**: essential self-adjointness of the
  differentially written Navier–Stokes symbol on the Hermite core of `L²(du₁du₂du₃)`,
  obtained from the Faris–Lavine criterion of `BookProof.ChapterFarisLavine` applied in
  `L²(ℝ³)` itself — the alternative route to
  `BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`,
  which transported essential self-adjointness instead of the estimates.

## Honest boundary

The estimates are the transported sequence-space ones: the mathematics unifying the two
pictures is the identification `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` and the fact that the
Gauss–polynomial core is the transported finite-mode core, not a new analytic input.  The
non-vacuity of the mechanism (a genuinely non-zero commutator `[H, N]`, and an unbounded
`H`) is recorded in `BookProof.ChapterNavierStokesHermiteFarisLavine.commForm_ne_zero_of_pos`,
`BookProof.ChapterNavierStokesFockManyMode.fock_commForm_ne_zero` and
`BookProof.ChapterNavierStokesDifferentialL2.nsDiffH_not_bounded`.  As everywhere on this
route, nothing here claims global regularity of the classical Navier–Stokes equation
(Contention D5): the statement is about the Hilbert-space operator at one Eulerian fiber,
where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates.
-/

namespace BookProof.NavierStokesFlow

namespace DiffFarisLavine

open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open LpNat FarisLavine IkebeKato ThreeComponent CanonicalVector DifferentialL2

noncomputable section

/-! ## The number operator in the sequence picture -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The number operator `a_i† a_i` of the mode `i` on the finite-mode core of `ℓ²(Vel)`. -/
def numSeq (i : Fin 3) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel := (cre i).comp (ann i)



set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The comparison operator in the sequence picture**, on the finite-mode core:
`N = 2μ ∑ᵢ a_i† a_i + (3μ + 1)`. -/
def velNcore (mu : ℝ) : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel :=
  (((2 * mu : ℝ) : ℂ)) • (∑ i, numSeq i) + (((3 * mu + 1 : ℝ) : ℂ)) • LinearMap.id



/-! ## The differential comparison operator -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The one-mode oscillator `πᵢ² + uᵢ²/4` on the Hermite core of `L²(ℝ³)`. -/
def oscOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  (momOp i).comp (momOp i) + ((1 / 4 : ℂ)) • (posOp i).comp (posOp i)





set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential comparison operator** `N = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1` on the Hermite
core of `L²(du₁du₂du₃)`, with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` multiplication by the coordinate. -/
def nsDiffN (mu : ℝ) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  (((2 * mu : ℝ) : ℂ)) • (∑ i, oscOp i) + LinearMap.id





/-! ## The core is exactly the transported finite-mode core -/





/-! ## The transport of the two pictures -/

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The constant part of the fiber field in the *sequence* normalization
`uᵢ = (aᵢ + aᵢ†)/√2`, corresponding to the differential constant part `c`. -/
def seqConst (c : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => c j / Real.sqrt 2

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The comparison strength of the differential data**: the constant `μ` for which
`N = 2μ ∑ᵢ(πᵢ² + uᵢ²/4) + 1` dominates the Hamiltonian. -/
def diffMu (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) : ℝ := velMu A (seqConst c)











/-! ## The Faris–Lavine package in the differential picture -/













/-! ## Essential self-adjointness by the Faris–Lavine criterion, in `L²(du₁du₂du₃)` -/

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The maximal domain of the differential comparison operator** in `L²(ℝ³)`. -/
def diffMaxDom (mu : ℝ) : Submodule ℂ (L2d 3) :=
  Submodule.map (velUnitary.toLinearEquiv : L2I Vel →ₗ[ℂ] L2d 3) (maxDom (velSym mu))

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- The maximal domain of `L²(ℝ³)` is the unitary image of the sequence one. -/
def diffMaxEquiv (mu : ℝ) : maxDom (velSym mu) ≃ₗ[ℂ] diffMaxDom mu :=
  (velUnitary.toLinearEquiv).submoduleMap (maxDom (velSym mu))



set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential comparison operator on its maximal domain.** -/
def diffMaxN (mu : ℝ) : diffMaxDom mu →ₗ[ℂ] L2d 3 :=
  (velUnitary.toLinearEquiv : L2I Vel →ₗ[ℂ] L2d 3).comp
    ((diagMax (velSym mu)).comp (diffMaxEquiv mu).symm.toLinearMap)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.
/-- **The differential Navier–Stokes Hamiltonian on the maximal domain** of the
comparison operator. -/
def diffMaxH : diffMaxDom (velMu A (seqConst c)) →ₗ[ℂ] L2d 3 :=
  (velUnitary.toLinearEquiv : L2I Vel →ₗ[ℂ] L2d 3).comp
    ((velH A (seqConst c)).comp (diffMaxEquiv (velMu A (seqConst c))).symm.toLinearMap)

























end

end DiffFarisLavine

end BookProof.NavierStokesFlow


