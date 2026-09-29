-- Prove2me | Definitions.Def_ChapterYangMillsHermite
-- name    : ChapterYangMillsHermite
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:22:13.438359+00:00
-- url     : https://prove2.me/theorems/99ab6bf3-0603-4d4c-91a2-d9d86b648f30
-- title:
--   `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the **field-space** (option (b)) realization of the Weyl-gauge Yang–M ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.YangMillsHermite`, source chapter `BookProof/ChapterYangMillsHermite.lean`).
--
--   `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the **field-space** (option (b)) realization of the Weyl-gauge Yang–Mills Hamiltonian: the fields must act as genuine multiplication and differentiation operators on a dense core of `L²(ℝ⁹⁹)`, not merely abstractly on an occupation-number space.
--
--   The core is `BookProof.HermiteProductCore.polyGaussCore`, the span of the product Hermite functions `p(x) e^{-‖x‖²/4}`. Because the map `p ↦ p · e^{-‖x‖²/4}` is an injective linear map from `ℂ[X₀,…,X₉₈]`, every operator can be defined at the purely algebraic level of polynomials and transported to the core (`CoreRep`).
--
--   * `mulOp f` — multiplication by a polynomial (F.2, the coordinate operators `A_{k,a}`); * `derOp j`, `momOp j` — the true derivative `∂_j` of `p·e^{-‖x‖²/4}` written back on the polynomial factor, and the momentum `π_j = −i ∂_j` (F.3); * `magPoly i a` — the magnetic field `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`, a *real* polynomial in the `99 = 3 + 24 + 72` coordinates (3 spatial, 24 fields `A_{j,a}`, 72 independent derivative coordinates `∂_j A_{k,a}`), acting by multiplication (F.4); * `weylProd` — the Weyl ordering `½(PQ + QP)`, symmetric whenever `P` and `Q` are (F.5); the canonical commutation relation `[A_{j}, π_{j}] = i` is `commutator_coord_mom`; * `ymHamiltonian` — `H₁ = ½ Σ π² + ½ Σ B²`, the *positive* sum of squares (the sign of `book.tex:7077` reconciled), well defined, symmetric and positive on the core (F.6–F.8); * `ym_hermite_friedrichs_extension` (F.9) and `ym_hermite_hashimoto_selects` (F.10) — the instantiation of the already-proved `BookProof.FriedrichsExtension.friedrichs_extension_exists` and `BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs`.
--
--   Nothing here claims a mass gap or global existence; the Millennium problem stays out of scope.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib

import Mathlib

/-!
# The gauge-fixed Yang–Mills Hamiltonian on the Gauss–polynomial core of `L²(ℝ⁹⁹)`

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the **field-space** (option
(b)) realization of the Weyl-gauge Yang–Mills Hamiltonian: the fields must act as
genuine multiplication and differentiation operators on a dense core of
`L²(ℝ⁹⁹)`, not merely abstractly on an occupation-number space.

The core is `BookProof.HermiteProductCore.polyGaussCore`, the span of the product
Hermite functions `p(x) e^{-‖x‖²/4}`.  Because the map `p ↦ p · e^{-‖x‖²/4}` is
an injective linear map from `ℂ[X₀,…,X₉₈]`, every operator can be defined at the
purely algebraic level of polynomials and transported to the core (`CoreRep`).

* `mulOp f` — multiplication by a polynomial (F.2, the coordinate operators
  `A_{k,a}`);
* `derOp j`, `momOp j` — the true derivative `∂_j` of `p·e^{-‖x‖²/4}` written back
  on the polynomial factor, and the momentum `π_j = −i ∂_j` (F.3);
* `magPoly i a` — the magnetic field
  `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`, a *real* polynomial
  in the `99 = 3 + 24 + 72` coordinates (3 spatial, 24 fields `A_{j,a}`, 72
  independent derivative coordinates `∂_j A_{k,a}`), acting by multiplication
  (F.4);
* `weylProd` — the Weyl ordering `½(PQ + QP)`, symmetric whenever `P` and `Q`
  are (F.5); the canonical commutation relation `[A_{j}, π_{j}] = i` is
  `commutator_coord_mom`;
* `ymHamiltonian` — `H₁ = ½ Σ π² + ½ Σ B²`, the *positive* sum of squares (the
  sign of `book.tex:7077` reconciled), well defined, symmetric and positive on
  the core (F.6–F.8);
* `ym_hermite_friedrichs_extension` (F.9) and `ym_hermite_hashimoto_selects`
  (F.10) — the instantiation of the already-proved
  `BookProof.FriedrichsExtension.friedrichs_extension_exists` and
  `BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs`.

Nothing here claims a mass gap or global existence; the Millennium problem stays
out of scope.
-/

namespace BookProof.YangMillsHermite

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

/-! ## Conjugate polynomials and the inner product on the core -/

/-- Complex conjugation of the coefficients of a polynomial. -/
def starP (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ := map (starRingEnd ℂ) p

















/-- A polynomial with *real* coefficients is fixed by `starP`; these are exactly
the ones that act as symmetric multiplication operators. -/
def RealCoeff (p : MvPolynomial (Fin d) ℂ) : Prop := starP p = p















/-! ## Polynomial-level operators and Gauss symmetry -/

/-- A polynomial-level operator is **Gauss symmetric** when it is symmetric for
the Gaussian inner product `⟪p, q⟫ = ∫ p̄ q e^{-‖x‖²/2}`.  By
`inner_pgLp_pgLp` this is exactly symmetry of the transported operator on the
core. -/
def PolySym (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : Prop :=
  ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (starP (T p) * q) = gaussInt (starP p * T q)





/-- The **adjoint pairing** of two operators: `S` and `T` are adjoint when
`⟪S p, q⟫ = ⟪p, T q⟫`. -/
def PolyAdj (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : Prop :=
  ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (starP (S p) * q) = gaussInt (starP p * T q)





/-- **Weyl ordering** `½(PQ + QP)`: the symmetric product of two operators.
This is the ordering prescription for the non-commuting `πA` cross terms. -/
def weylProd (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  ((1 / 2 : ℝ) : ℂ) • (S.comp T + T.comp S)



/-! ### Multiplication operators (F.2) -/

/-- Multiplication by a fixed polynomial. -/
def mulOp (f : MvPolynomial (Fin d) ℂ) : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  LinearMap.mulLeft ℂ f





/-! ### Momentum operators (F.3) -/

/-- The derivative `∂_j` acting on `p·e^{-‖x‖²/4}`, written back on the
polynomial factor: `∂_j (p e^{-‖x‖²/4}) = (∂_j p − ½ x_j p) e^{-‖x‖²/4}`. -/
def derOp (j : Fin d) : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  (pderiv j).toLinearMap - ((1 / 2 : ℝ) : ℂ) • mulOp (X j)



/-- The **momentum operator** `π_j = −i ∂_j` on the core (F.3). -/
def momOp (j : Fin d) : Module.End ℂ (MvPolynomial (Fin d) ℂ) := (-Complex.I) • derOp j




















/-! ## Transport to the Gauss–polynomial core of `L²(ℝᵈ)` -/

/-- A **representation of the Gauss–polynomial core**: a linear isomorphism from
the polynomials onto a submodule `D` of `L²(ℝᵈ)` realizing `p ↦ p·e^{-‖x‖²/4}`.
Every polynomial-level operator is transported to `D` through it. -/
structure CoreRep (d : ℕ) (D : Submodule ℂ (L2d d)) where
  /-- The isomorphism from polynomials onto the core. -/
  equiv : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] D
  /-- It really is `p ↦ p·e^{-‖x‖²/4}`. -/
  coe_equiv : ∀ p, ((equiv p : D) : L2d d) = pgLp p

section Transport

variable {D : Submodule ℂ (L2d d)}

/-- Transport of a polynomial-level operator to the core. -/
def CoreRep.op (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : D →ₗ[ℂ] D :=
  Φ.equiv.conj T









/-- Any submodule that *is* the range of `pgMap` is a `CoreRep`. -/
def CoreRep.ofRangeEq (h : LinearMap.range (pgMap (d := d)) = D) : CoreRep d D where
  equiv := (LinearEquiv.ofInjective pgMap pgMap_injective).trans (LinearEquiv.ofEq _ _ h)
  coe_equiv := fun _ => rfl

/-- The core `polyGaussCore` itself is a `CoreRep`. -/
def coreRepPoly (d : ℕ) : CoreRep d (polyGaussCore (d := d)) := CoreRep.ofRangeEq rfl

theorem finiteModeDomain_coreBasis (e : ℕ ≃ (Fin d →₀ ℕ)) :
    finiteModeDomain (coreBasis e) = polyGaussCore (d := d) := span_range_coreBasis e

/-- The finite-mode domain of the adapted orthonormal basis `coreBasis e` is a
`CoreRep`: this is what lets the abstract Hashimoto/Friedrichs theorems, stated
for `finiteModeDomain`, be instantiated by the field-space operators. -/
def coreRepBasis (e : ℕ ≃ (Fin d →₀ ℕ)) : CoreRep d (finiteModeDomain (coreBasis e)) :=
  CoreRep.ofRangeEq (finiteModeDomain_coreBasis e).symm

end Transport

section YangMills

variable {D : Submodule ℂ (L2d 99)}

/-! ## The Yang–Mills coordinates of `ℝ⁹⁹`

`99 = 3 + 24 + 72`: three spatial coordinates `x_i`, the `24 = 3 × 8` gauge-field
coordinates `A_{j,a}` (`j` spatial, `a` an `SU(3)` colour index), and the
`72 = 3 × 3 × 8` coordinates `∂_j A_{k,a}`, which in the book's parametrization
are independent coordinates of the configuration space. -/

/-- The coordinate index of the gauge field `A_{j,a}`. -/
def idxA (j : Fin 3) (a : Fin 8) : Fin 99 := ⟨3 + 8 * j.val + a.val, by omega⟩

/-- The coordinate index of the independent derivative coordinate `∂_j A_{k,a}`. -/
def idxD (j k : Fin 3) (a : Fin 8) : Fin 99 := ⟨27 + 24 * j.val + 8 * k.val + a.val, by omega⟩



/-- The **Levi-Civita symbol** on three indices, in the closed form
`ε_{ijk} = (i−j)(j−k)(k−i)/2`. -/
def levi (i j k : Fin 3) : ℝ :=
  ((((i : ℤ) - (j : ℤ)) * ((j : ℤ) - (k : ℤ)) * ((k : ℤ) - (i : ℤ)) : ℤ) : ℝ) / 2



/-- The **magnetic field** `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`
as a polynomial in the `99` coordinates.  The structure constants `f_{abc}` of
the (compact) gauge group are real; only that is used. -/
def magPoly (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (i : Fin 3) (a : Fin 8) :
    MvPolynomial (Fin 99) ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) •
    (X (idxD j k a) + ∑ b : Fin 8, ∑ c : Fin 8,
      ((fabc a b c : ℝ) : ℂ) • (X (idxA j b) * X (idxA k c)))



/-- The spatial index carried by the `m`-th of the `24` field/colour pairs. -/
def decodeSpace (m : Fin 24) : Fin 3 := ⟨m.val / 8, by omega⟩

/-- The colour index carried by the `m`-th of the `24` field/colour pairs. -/
def decodeColor (m : Fin 24) : Fin 8 := ⟨m.val % 8, by omega⟩

/-! ## The Hamiltonian on the core (F.6–F.8) -/

/-- The **momentum operators** `π^{j}_{a} = −i ∂/∂A_{j,a}` on the core, one for
each of the `24` field coordinates (F.3). -/
def piOps (Φ : CoreRep 99 D) (m : Fin 24) : D →ₗ[ℂ] D :=
  Φ.op (momOp (idxA (decodeSpace m) (decodeColor m)))

/-- The **magnetic-field operators** `B_{i a}` on the core: multiplication by the
real polynomial `magPoly` (F.4). -/
def magOps (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) : D →ₗ[ℂ] D :=
  Φ.op (mulOp (magPoly fabc (decodeSpace m) (decodeColor m)))





/-- **The gauge-fixed Yang–Mills Hamiltonian on the core** (F.6),
`H₁ = ½ Σ_m (π_m)² + ½ Σ_m (B_m)²`.  The sign is the *positive* sum of squares —
the reconciliation of `book.tex:7077`, which writes `H = −½ππ − ½BB`; the
positive convention is the one bounded below, i.e. the one to which the
Friedrichs machinery applies. -/
def ymHamiltonian (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : D →ₗ[ℂ] L2d 99 :=
  weylOp (piOps Φ) (magOps Φ fabc)









/-! ## Instantiation of the Friedrichs and Hashimoto theorems (F.9, F.10) -/





/-- A concrete enumeration of the monomials of `ℂ[X₀,…,X₉₈]`, so that
`ym_hermite_hashimoto_selects` is not vacuous. -/
def ymEnum : ℕ ≃ (Fin 99 →₀ ℕ) :=
  letI : Denumerable (Fin 99 →₀ ℕ) := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv (Fin 99 →₀ ℕ)).symm

end YangMills


end

end BookProof.YangMillsHermite


