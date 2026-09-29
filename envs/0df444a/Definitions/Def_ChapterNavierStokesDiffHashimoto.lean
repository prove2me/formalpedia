-- Prove2me | Definitions.Def_ChapterNavierStokesDiffHashimoto
-- name    : ChapterNavierStokesDiffHashimoto
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:42:02.49431+00:00
-- url     : https://prove2.me/theorems/4feed85e-9e35-4929-be7c-a2604f97652a
-- title:
--   `BookProof.ChapterNavierStokesHashimoto` proves the Hashimoto/SIRK selection theorem for the Navier–Stokes fiber generat ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesDiffHashimoto`, source chapter `BookProof/ChapterNavierStokesDiffHashimoto.lean`).
--
--   `BookProof.ChapterNavierStokesHashimoto` proves the Hashimoto/SIRK selection theorem for the Navier–Stokes fiber generator in its **abstract sequence-space** realization: the Hermite matrix `velCore` on `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`. The **differential** realization — the same Hamiltonian written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication operator on the Gauss–polynomial (product Hermite) core of `L²(du₁du₂du₃)`, `BookProof.NavierStokesFlow.DifferentialL2.nsDiffH` — was proved essentially self-adjoint (`nsDiffH_essentiallySelfAdjointOn_core`) but carried no selection theorem. This module supplies it.
--
--   * `nsDiffPoly`, `nsDiffH_eq_coreOp` — the differentially written Weyl-ordered Hamiltonian is the transport of a polynomial-level operator, namely the sum of the Weyl products `½(πᵢ Vᵢ + Vᵢ πᵢ)` of the momentum with the affine fiber field; * `nsDiffPoly_polySym`, `nsDiffH_symmetricOn` — it is Gauss symmetric, hence symmetric on the Hermite core of `L²(ℝ³)`; * `nsDiffH_selfAdjoint_extension`, `nsDiffH_selfAdjoint_extension_unique` — the differential operator has exactly one self-adjoint extension, its closure (no positivity: the strain, vorticity and constant hoppings carry arbitrary signs); * `nsDiffH_hashimoto_selects` — **the headline**: for an arbitrary sequence of non-real shifts `γⱼ` the shift-inverted resolvents `Xⱼ = (γⱼ − G)⁻¹` of the differential Navier–Stokes generator exist, are bounded by `1/|Im γⱼ|`, share the domain of `G`, satisfy the resolvent identity, commute, satisfy the Hashimoto–Nodera SIRK relation, have strongly convergent Galerkin truncations, and each determines `G` completely; * `nsDiffH_shiftInvert_selects` — the single-shift form; * `nsQuadraticDiffH_hashimoto_selects` — the same with the coefficients spelled out as `(ν, u_{i,j}, u_{i,jj})`; * `exists_l2dHilbertBasisNat` — non-vacuity: `L²(ℝ³)` carries an `ℕ`-indexed Hilbert basis (the product Hermite functions, enumerated).
--
--   Unchanged (Contention D5): the theorem is a statement about the Hilbert-space operator at one Eulerian fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates. Nothing here claims global regularity of the classical Navier–Stokes equation.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterNavierStokesHashimoto
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesDifferentialL2

import Mathlib

/-!
# The Hashimoto/SIRK shift-invert limit selects the *differential* Navier–Stokes generator

`BookProof.ChapterNavierStokesHashimoto` proves the Hashimoto/SIRK selection theorem for
the Navier–Stokes fiber generator in its **abstract sequence-space** realization: the
Hermite matrix `velCore` on `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`.  The **differential**
realization — the same Hamiltonian written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine
multiplication operator on the Gauss–polynomial (product Hermite) core of
`L²(du₁du₂du₃)`, `BookProof.NavierStokesFlow.DifferentialL2.nsDiffH` — was proved
essentially self-adjoint (`nsDiffH_essentiallySelfAdjointOn_core`) but carried no
selection theorem.  This module supplies it.

## What is proved

* `nsDiffPoly`, `nsDiffH_eq_coreOp` — the differentially written Weyl-ordered
  Hamiltonian is the transport of a polynomial-level operator, namely the sum of the
  Weyl products `½(πᵢ Vᵢ + Vᵢ πᵢ)` of the momentum with the affine fiber field;
* `nsDiffPoly_polySym`, `nsDiffH_symmetricOn` — it is Gauss symmetric, hence symmetric
  on the Hermite core of `L²(ℝ³)`;
* `nsDiffH_selfAdjoint_extension`, `nsDiffH_selfAdjoint_extension_unique` — the
  differential operator has exactly one self-adjoint extension, its closure (no
  positivity: the strain, vorticity and constant hoppings carry arbitrary signs);
* `nsDiffH_hashimoto_selects` — **the headline**: for an arbitrary sequence of non-real
  shifts `γⱼ` the shift-inverted resolvents `Xⱼ = (γⱼ − G)⁻¹` of the differential
  Navier–Stokes generator exist, are bounded by `1/|Im γⱼ|`, share the domain of `G`,
  satisfy the resolvent identity, commute, satisfy the Hashimoto–Nodera SIRK relation,
  have strongly convergent Galerkin truncations, and each determines `G` completely;
* `nsDiffH_shiftInvert_selects` — the single-shift form;
* `nsQuadraticDiffH_hashimoto_selects` — the same with the coefficients spelled out as
  `(ν, u_{i,j}, u_{i,jj})`;
* `exists_l2dHilbertBasisNat` — non-vacuity: `L²(ℝ³)` carries an `ℕ`-indexed Hilbert
  basis (the product Hermite functions, enumerated).

## Honest boundary

Unchanged (Contention D5): the theorem is a statement about the Hilbert-space operator
at one Eulerian fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent
canonical coordinates.  Nothing here claims global regularity of the classical
Navier–Stokes equation.
-/

open Filter Topology

namespace BookProof.NavierStokesFlow

namespace DiffHashimoto

open MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

/-! ## The polynomial-level form of the differential Hamiltonian -/





/-- **The affine fiber field on polynomial coordinates**: `Vᵢ = ∑ₖ A_{ik} uₖ + cᵢ`. -/
def fieldPoly (i : Fin 3) : Module.End ℂ (MvPolynomial (Fin 3) ℂ) :=
  (∑ k, ((A i k : ℝ) : ℂ) • mulXPoly k) + (((c i : ℝ) : ℂ) • LinearMap.id)







/-- **The differentially written Weyl-ordered Navier–Stokes Hamiltonian on polynomial
coordinates**: `∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)`. -/
def nsDiffPoly : Module.End ℂ (MvPolynomial (Fin 3) ℂ) :=
  ∑ i, BookProof.YangMillsHermite.weylProd (momPoly i) (fieldPoly A c i)







/-! ## Symmetry of the differential operator -/



/-! ## The self-adjoint differential generator -/





/-! ## The Hashimoto/SIRK selection on `L²(du₁du₂du₃)` -/







/-! ## Non-vacuity -/





end

end DiffHashimoto

end BookProof.NavierStokesFlow


