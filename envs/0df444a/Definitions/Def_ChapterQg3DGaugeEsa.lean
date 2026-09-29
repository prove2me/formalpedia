-- Prove2me | Definitions.Def_ChapterQg3DGaugeEsa
-- name    : ChapterQg3DGaugeEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-18T13:08:09.278175+00:00
-- url     : https://prove2.me/theorems/81f7b1b6-ad26-4986-b9f6-12171b5ea931
-- title:
--   3D gauge ESA definitions
-- statement:
--   Formal definitions for the 3D gauge essential self-adjointness.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterQg3DGaugeEsa.lean

import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib


/-!
# Essential self-adjointness of the 3D gauge-fixed gravity Hamiltonian on the
Gauss–polynomial core of `L²(ℝ⁸⁴)`

`BookProof.ChapterQuantumGravity3DGauge` builds the concrete densitized, Weyl-ordered
3D gauge-fixed gravity Hamiltonian

`H = ½ Σ_j κ_j π_j² + ½ Σ_m T_m²`,  `κ = qgKappa`,  `T_m = ∂_μ e_ν^a − ∂_ν e_μ^a`,

on a Gauss–polynomial core of `L²(ℝ⁸⁴)` and proves it symmetric there, but stops short of a
self-adjointness statement: the signature `qgKappa` is *hyperbolic*
(`qgKappa_conformal_neg`), so the Friedrichs machinery — which needs a semibounded form —
does not apply to it.

This module closes that gap along the route recorded as the strategy of record in
`CONSOLIDATED_PLAN.md` §10.2b: **the one-particle operator is quadratic in the canonical
pair**, and the general real quadratic Hamiltonian is already known to be essentially
self-adjoint on the plain Gauss–polynomial core by
`BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint` (proved through the Carleman-flux
criterion on the simplex shells, with no sign, ellipticity or definiteness hypothesis).
What is needed is therefore only an **identification**: the gravity Hamiltonian *is* one of
those quadratic Hamiltonians, for an explicit pair of real coefficient matrices.

## What is proved

* `torsionVec`, `qgFqQ`, `qgFqP` — the coefficient data: `T_m = Σ_i (torsionVec m i)·x_i` is
  a *linear* form in the coordinates, so `½ Σ_m T_m²` is the quadratic form of the
  (positive semidefinite) Gram matrix `qgFqQ = ½ Σ_m v_m v_mᵀ`, while the kinetic term is
  the diagonal momentum matrix `qgFqP κ = diag(κ/2)`.
* `sum_torsionVec_X`, `qgFqQ_quadratic_eq` — the two polynomial identities behind it.
* `qgSignedPoly_eq_fqPoly` — the operator identity at polynomial level:
  `½ Σ_j κ_j π_j² + ½ Σ_m T_m² = fqPoly (diag(κ/2)) qgFqQ 0 0 0` for **every** real
  signature `κ`.
* `qgSigned_eq_fqOp` — the same identity on the core of `L²(ℝ⁸⁴)`.
* `qgSigned_essentiallySelfAdjointOn_core` — **the headline in general form**: for every
  real signature `κ` the operator `½ Σ_j κ_j π_j² + ½ Σ_m T_m²` is essentially
  self-adjoint on the Gauss–polynomial core.
* `qg3D_essentiallySelfAdjointOn_core` — the physical, *hyperbolic* instance: the gravity
  Hamiltonian `qg3DHamiltonian` itself is essentially self-adjoint on the core, so its
  closure is the unique self-adjoint realization, and `qg3D_stone_flow` is the complete
  unitary group it generates (Stone).
* `qg3DElliptic_essentiallySelfAdjointOn_core` — the elliptic sector, for comparison: it is
  the same statement with `qgKappaElliptic`, and it *upgrades* the Friedrichs extension of
  `ChapterQuantumGravity3DGauge` from existence to uniqueness.

## Honest boundary

This is the **one-particle** operator of the final-Hamiltonian doctrine — the `h` of
`H = Σᵢⱼ hᵢⱼ C†(eᵢ) A(eⱼ)` — realized on the 84 field-space coordinates, with the torsion
potential of `ChapterQuantumGravity3DGauge`. No mass gap, no spectrum and no continuum
limit is claimed; the Fock lift is the separate `dΓ` layer. The statement is essential
self-adjointness on the Gauss–polynomial core of `L²(ℝ⁸⁴)`, which is dense
(`polyGaussCore_dense`).

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.Qg3DGaugeEsa

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The torsion terms as linear forms in the coordinates -/

/-- The first spacetime index carried by the `m`-th torsion operator. -/
def torsionMu (m : Fin 64) : Fin 4 := ⟨m.val / 16, by omega⟩

/-- The second spacetime index carried by the `m`-th torsion operator. -/
def torsionNu (m : Fin 64) : Fin 4 := ⟨m.val / 4 % 4, by omega⟩

/-- The internal index carried by the `m`-th torsion operator. -/
def torsionA (m : Fin 64) : Fin 4 := ⟨m.val % 4, by omega⟩

/-- The polynomial momentum operator `π_j = −i ∂_j` on the Gauss–polynomial coordinates
(the `BookProof.YangMillsHermite` one; abbreviated here to keep the formulas readable). -/
abbrev pmom (j : Fin 84) : MvPolynomial (Fin 84) ℂ →ₗ[ℂ] MvPolynomial (Fin 84) ℂ :=
  YangMillsHermite.momOp j

/-- The polynomial of the `m`-th torsion term, `T_m = ∂_μ e_ν^a − ∂_ν e_μ^a`. -/
def torsionP (m : Fin 64) : MvPolynomial (Fin 84) ℂ :=
  torsionPoly (torsionMu m) (torsionNu m) (torsionA m)



/-- The coordinate index `∂_μ e_ν^a` of the `m`-th torsion term. -/
def torsionIdx1 (m : Fin 64) : Fin 84 := idxDE (torsionMu m) (torsionNu m) (torsionA m)

/-- The coordinate index `∂_ν e_μ^a` subtracted in the `m`-th torsion term. -/
def torsionIdx2 (m : Fin 64) : Fin 84 := idxDE (torsionNu m) (torsionMu m) (torsionA m)

/-- **The torsion term is a linear form**: `T_m = Σ_i (torsionVec m i)·x_i`, with the
coefficient vector `v_m = e_{∂_μ e_ν^a} − e_{∂_ν e_μ^a}`. -/
def torsionVec (m : Fin 64) (i : Fin 84) : ℝ :=
  (if i = torsionIdx1 m then 1 else 0) - (if i = torsionIdx2 m then 1 else 0)





/-! ## 2. The coefficient matrices of the quadratic Hamiltonian -/

/-- The momentum matrix of the gravity Hamiltonian: the diagonal `diag(κ/2)`. -/
def qgFqP (kappa : Fin 84 → ℝ) (j k : Fin 84) : ℝ := if j = k then kappa j / 2 else 0

/-- The coordinate matrix of the gravity Hamiltonian: `½ Σ_m v_m v_mᵀ`, the Gram matrix of
the torsion coefficient vectors. -/
def qgFqQ (i j : Fin 84) : ℝ := (1 / 2) * ∑ m : Fin 64, torsionVec m i * torsionVec m j





/-! ## 3. The identification with the general quadratic Hamiltonian -/

/-- The polynomial-level two-signed gravity Hamiltonian `½ Σ_j κ_j π_j² + ½ Σ_m T_m²`, for
an arbitrary real signature `κ`. -/
def qgSignedPoly (kappa : Fin 84 → ℝ) :
    MvPolynomial (Fin 84) ℂ →ₗ[ℂ] MvPolynomial (Fin 84) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((∑ j : Fin 84, ((kappa j : ℝ) : ℂ) • (pmom j).comp (pmom j))
      + ∑ m : Fin 64, (mulOp (torsionP m)).comp (mulOp (torsionP m)))







/-! ## 4. Transport to the core of `L²(ℝ⁸⁴)` -/









/-! ## 5. Essential self-adjointness -/









end

end BookProof.Qg3DGaugeEsa


