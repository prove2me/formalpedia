-- Prove2me | Definitions.Def_ChapterYangMillsAbelianEsa
-- name    : ChapterYangMillsAbelianEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T11:48:01.017878+00:00
-- url     : https://prove2.me/theorems/5556f28b-19f9-4a06-ac70-3e3366216c84
-- title:
--   Chapter ChapterYangMillsAbelianEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.YangMillsAbelianEsa`, source chapter `BookProof/ChapterYangMillsAbelianEsa.lean`): Chapter ChapterYangMillsAbelianEsa
--
--   Generated def bundle for ChapterYangMillsAbelianEsa. See BookProof/ChapterYangMillsAbelianEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsAbelianEsa.lean

import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Mathlib
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsFriedrichs


/-!
# Essential self-adjointness of the **abelian** gauge-fixed Yang–Mills Hamiltonian on the
Gauss–polynomial core of `L²(ℝ⁹⁹)`

`BookProof.ChapterYangMillsHermite` builds the field-space Weyl-gauge Yang–Mills
Hamiltonian

`H₁ = ½ Σ_m π_m² + ½ Σ_m B_m²`,  `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`,

on the Gauss–polynomial core of `L²(ℝ⁹⁹)` and proves it symmetric and positive there, so
that the Friedrichs machinery applies (`ym_hermite_friedrichs_extension`).  What it does
*not* give is **uniqueness** of the self-adjoint realization.

This module supplies it in the **abelian** case `f_{abc} = 0` — the numerics' "abelian
gapless limit" operator.  There the magnetic field
`B_{i a} = ε_{ijk} ∂_j A_{k,a}` is a *linear* form in the coordinates, so `H₁` is a genuine
real quadratic Hamiltonian in the canonical pair, and the Carleman instrument
`BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint` — the engine behind
`BookProof.Qg3DGaugeEsa.qg3D_essentiallySelfAdjointOn_core` — applies verbatim.  What is
needed is only an **identification**: the abelian Yang–Mills Hamiltonian *is* one of those
quadratic Hamiltonians, for an explicit pair of real coefficient matrices.

## What is proved

* `gramWeyl_eq` — the reusable algebraic step: for coefficient vectors `v_m` the
  Weyl-ordered Gram combination `Σ_{i,j} (½ Σ_m v_{m i} v_{m j}) ·½(T_iT_j + T_jT_i)`
  is `½ Σ_m S_m²` with `S_m = Σ_i v_{m i} T_i`.
* `ymMomVec`, `ymMagVec`, `ymFqP`, `ymFqQ` — the coefficient data: the `24` momenta
  `π_m = −i ∂/∂A_{j,a}` pick out `24` of the `99` coordinates, and the abelian magnetic
  field is the linear form `Σ_n (ymMagVec m n)·x_n`.
* `sum_ymMomVec_mom`, `sum_ymMagVec_X` — the two identities behind that.
* `ymAbelianPoly_eq_fqPoly` — the operator identity at polynomial level:
  `½ Σ_m π_m² + ½ Σ_m B_m² = fqPoly ymFqP ymFqQ 0 0 0`.
* `ymAbelian_eq_fqOp` — the same identity on the core of `L²(ℝ⁹⁹)`.
* `ymAbelian_essentiallySelfAdjointOn_core` — **the headline**: the abelian gauge-fixed
  Yang–Mills Hamiltonian `ymHamiltonian (coreRepPoly 99) 0` is essentially self-adjoint on
  the Gauss–polynomial core, so its closure is the unique self-adjoint realization — and in
  particular *is* the Friedrichs extension of `ym_hermite_friedrichs_extension`.
* `ymAbelian_positiveExtension_eq_closure` — consequently the Friedrichs extension *is* the
  closure: in the abelian case the selection problem is empty.
* `ymAbelian_hashimoto_selects` — the Hashimoto/SIRK shift-invert algorithm selects that
  unique realization, at any family of non-real shifts.
* `ymAbelian_stone_flow` — the complete unitary group it generates (Stone).

## Honest boundary

This is the **abelian** (`f_{abc} = 0`) one-particle operator only.  For `g ≠ 0` the term
`B²` is quartic in the coordinates and neither this quadratic instrument nor the
Faris–Lavine sums-of-squares machinery covers it; that remains open.  No mass gap, no
spectrum and no continuum limit is claimed here; the Fock lift is the separate `dΓ` layer.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.YangMillsAbelianEsa

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

/-! ## 1. A reusable Gram identity for Weyl-ordered squares -/







/-! ## 2. The coefficient data of the abelian Yang–Mills Hamiltonian -/

/-- The coordinate index of the field `A_{j,a}` carried by the `m`-th of the `24`
field/colour pairs — the coordinate the `m`-th momentum differentiates. -/
def ymMomIdx (m : Fin 24) : Fin 99 := idxA (decodeSpace m) (decodeColor m)



/-- The coefficient vector of the `m`-th momentum: the unit vector at `ymMomIdx m`. -/
def ymMomVec (m : Fin 24) (n : Fin 99) : ℝ := if n = ymMomIdx m then 1 else 0

/-- The coefficient vector of the `m`-th **abelian** magnetic field
`B_{i a} = ε_{ijk} ∂_j A_{k,a}`, a linear form in the `99` coordinates. -/
def ymMagVec (m : Fin 24) (n : Fin 99) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    (if n = idxD j k (decodeColor m) then levi (decodeSpace m) j k else 0)

/-- The momentum matrix of the abelian Yang–Mills Hamiltonian. -/
def ymFqP (i j : Fin 99) : ℝ := (1 / 2) * ∑ m : Fin 24, ymMomVec m i * ymMomVec m j

/-- The coordinate matrix of the abelian Yang–Mills Hamiltonian: the Gram matrix of the
magnetic coefficient vectors. -/
def ymFqQ (i j : Fin 99) : ℝ := (1 / 2) * ∑ m : Fin 24, ymMagVec m i * ymMagVec m j







/-! ## 3. The identification with the general quadratic Hamiltonian -/

/-- The polynomial-level abelian Yang–Mills Hamiltonian `½ Σ_m π_m² + ½ Σ_m B_m²`. -/
def ymAbelianPoly : MvPolynomial (Fin 99) ℂ →ₗ[ℂ] MvPolynomial (Fin 99) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((∑ m : Fin 24, (YangMillsHermite.momOp (ymMomIdx m)).comp
        (YangMillsHermite.momOp (ymMomIdx m)))
      + ∑ m : Fin 24, (mulOp (magPoly 0 (decodeSpace m) (decodeColor m))).comp
          (mulOp (magPoly 0 (decodeSpace m) (decodeColor m))))





/-! ## 4. Transport to the core of `L²(ℝ⁹⁹)` -/









/-! ## 5. Essential self-adjointness -/









end

end BookProof.YangMillsAbelianEsa


