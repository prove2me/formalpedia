-- Prove2me | Definitions.Def_ChapterQgHermiteOscillatorEsa
-- name    : ChapterQgHermiteOscillatorEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-12T11:56:22.932098+00:00
-- url     : https://prove2.me/theorems/db82a824-95cb-4fd3-a330-960c983cbf21
-- title:
--   Essential self-adjointness on the Gauss–polynomial core: the harmonic (conformal-mode) potential
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.QgHermiteOscillatorEsa`, source chapter `BookProof/ChapterQgHermiteOscillatorEsa.lean`): Essential self-adjointness on the Gauss–polynomial core: the harmonic (conformal-mode) potential
--
--   `BookProof.ChapterQgHermiteFriedrichs` realizes the one-particle Hamiltonian `−Δ + W` on the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)` and produces a canonical *semibounded* self-adjoint (Friedrichs) extension of it. That is existence, not uniqueness: `CONSOLIDATED_PLAN.md` §10.6.1 target 4 asks for **essential** self-adjointness on the core, which is what forces the extension to be the only one.
--
--   This module proves the uniqueness statement for the potential the conformal-mode sector contributes — the **harmonic (parabolic) potential** `W(x) = ‖x‖²/4` — in every dimension:
--
--   > `−Δ + ‖x‖²/4` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᵈ)`.
--
--   Two ingredients:
--
--   * a general criterion, `essentiallySelfAdjointOn_of_eigenbasis`: *a linear map on a subspace `D` which has an orthonormal Hilbert basis of eigenvectors, with real eigenvalues, all lying in `D`, has trivial deficiency at every non-real point, hence is essentially self-adjoint on `D`*. (The proof is the one-line computation `(λ − z)⟪e, w⟫ = 0`, plus completeness of the basis.) * the identification of `−Δ + ‖x‖²/4` with the **number operator plus `d/2`**: on the polynomial side `kinPoly p + harmPoly * p = ∑ⱼ a†ⱼaⱼ p + (d/2) p` (`kinPoly_add_harmPoly`), and `a†ᵢaᵢ` acts on the product Hermite polynomial `He_α` by the multiplier `αᵢ` (`crePoly_annPoly_hermiteMv`). The product Hermite functions of `BookProof.ChapterHermiteProductBasis` are therefore eigenvectors of the Hamiltonian with eigenvalues `|α| + d/2` (`hamCore_hermiteMvLp`), and they are an orthonormal basis lying inside the core.
--
--   The conclusion `harmonicCore_essentiallySelfAdjoint` is unconditional — no finite-speed or unique-continuation hypothesis — and `harmonicCore_stone_flow` reads off what it buys: a self-adjoint realization of the Hamiltonian together with the unitary group it generates, obtained from essential self-adjointness rather than from a choice of extension.
--
--   A Kato–Rellich step widens the class: `harmonic_add_bounded_essentiallySelfAdjoint` shows that `−Δ + ‖x‖²/4 + B` is still essentially self-adjoint on the core for *any* continuous bounded real `B`, since multiplication by `B` is symmetric on the core with `‖Bψ‖ ≤ M‖ψ‖` (`potCore_symmetricOn`, `norm_potLp_le`) — relative bound `0`.
--
--   **Honest boundary.** The potential here is a parabola plus a bounded function, not the exponentially growing scalaron potential. For the *potential term* alone the exponential case is settled in `BookProof.ChapterScalaronHermiteEsa` (`potCore_essentiallySelfAdjoint`, `scalaronPot_essentiallySelfAdjoint`); §10.6.1 target 4 for the *sum* `−Δ + V` with `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` is *not* proved here and remains open, as does target 2 (which needs restating) and target 3.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteOscillatorEsa.lean

import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterKatoRellichRelative

import Mathlib

/-!
# Essential self-adjointness on the Gauss–polynomial core: the harmonic (conformal-mode)
potential

`BookProof.ChapterQgHermiteFriedrichs` realizes the one-particle Hamiltonian `−Δ + W` on
the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)` and produces a canonical *semibounded*
self-adjoint (Friedrichs) extension of it.  That is existence, not uniqueness:
`CONSOLIDATED_PLAN.md` §10.6.1 target 4 asks for **essential** self-adjointness on the
core, which is what forces the extension to be the only one.

This module proves the uniqueness statement for the potential the conformal-mode sector
contributes — the **harmonic (parabolic) potential** `W(x) = ‖x‖²/4` — in every dimension:

> `−Δ + ‖x‖²/4` is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝᵈ)`.

Two ingredients:

* a general criterion, `essentiallySelfAdjointOn_of_eigenbasis`: *a linear map on a
  subspace `D` which has an orthonormal Hilbert basis of eigenvectors, with real
  eigenvalues, all lying in `D`, has trivial deficiency at every non-real point, hence is
  essentially self-adjoint on `D`*.  (The proof is the one-line computation
  `(λ − z)⟪e, w⟫ = 0`, plus completeness of the basis.)
* the identification of `−Δ + ‖x‖²/4` with the **number operator plus `d/2`**:
  on the polynomial side `kinPoly p + harmPoly * p = ∑ⱼ a†ⱼaⱼ p + (d/2) p`
  (`kinPoly_add_harmPoly`), and `a†ᵢaᵢ` acts on the product Hermite polynomial `He_α` by
  the multiplier `αᵢ` (`crePoly_annPoly_hermiteMv`).  The product Hermite functions of
  `BookProof.ChapterHermiteProductBasis` are therefore eigenvectors of the Hamiltonian
  with eigenvalues `|α| + d/2` (`hamCore_hermiteMvLp`), and they are an orthonormal basis
  lying inside the core.

The conclusion `harmonicCore_essentiallySelfAdjoint` is unconditional — no finite-speed or
unique-continuation hypothesis — and `harmonicCore_stone_flow` reads off what it buys: a
self-adjoint realization of the Hamiltonian together with the unitary group it generates,
obtained from essential self-adjointness rather than from a choice of extension.

A Kato–Rellich step widens the class: `harmonic_add_bounded_essentiallySelfAdjoint` shows
that `−Δ + ‖x‖²/4 + B` is still essentially self-adjoint on the core for *any* continuous
bounded real `B`, since multiplication by `B` is symmetric on the core with
`‖Bψ‖ ≤ M‖ψ‖` (`potCore_symmetricOn`, `norm_potLp_le`) — relative bound `0`.

**Honest boundary.**  The potential here is a parabola plus a bounded function, not the
exponentially growing scalaron potential.  For the *potential term* alone the exponential
case is settled in `BookProof.ChapterScalaronHermiteEsa`
(`potCore_essentiallySelfAdjoint`, `scalaronPot_essentiallySelfAdjoint`); §10.6.1 target 4
for the *sum* `−Δ + V` with `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` is *not* proved here and
remains open, as does target 2 (which needs restating) and target 3.
-/

namespace BookProof.QgHermiteOscillator

open MeasureTheory Complex MvPolynomial
open BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs

noncomputable section

/-! ## A general criterion: an orthonormal eigenbasis inside the domain -/

section Criterion

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {ι : Type*} {D : Submodule ℂ F}







end Criterion

variable {d : ℕ}

/-! ## The harmonic potential -/

/-- The harmonic (conformal-mode) potential `‖x‖²/4`, the one for which the
Gauss–polynomial core is the eigenbasis. -/
def harmW (x : Vd d) : ℝ := ‖x‖ ^ 2 / 4

theorem continuous_harmW : Continuous (harmW (d := d)) := by
  unfold harmW
  fun_prop

theorem expBounded_harmW : ExpBounded (harmW (d := d)) := by
  refine ⟨1, 1, zero_le_one, fun x => ?_⟩
  have h := Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) 2
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfac] at h
  have hpos : (0 : ℝ) ≤ harmW x := by
    unfold harmW; positivity
  rw [abs_of_nonneg hpos, one_mul, one_mul]
  unfold harmW
  nlinarith [sq_nonneg ‖x‖]

/-- The harmonic potential, as a polynomial in the coordinates. -/
def harmPoly : MvPolynomial (Fin d) ℂ := ∑ j : Fin d, C (1 / 4 : ℂ) * X j ^ 2





/-! ## The Hamiltonian is the number operator plus `d/2` -/





/-! ## The Hermite functions are eigenvectors -/





/-- The total degree of a multi-index — the eigenvalue of the number operator. -/
def mvDeg (a : Fin d →₀ ℕ) : ℕ := ∑ i : Fin d, a i



/-! ## The Hamiltonian on the core, and its essential self-adjointness -/

/-- The harmonic Hamiltonian on the Gauss–polynomial core. -/
def harmCore : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  hamCore harmW continuous_harmW expBounded_harmW















/-! ## Bounded perturbations: `−Δ + ‖x‖²/4 + B` -/

/-- Multiplication by the potential, as a linear map out of the polynomials. -/
def potPolyMap (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := potLp W hWc hWb
  map_add' := potLp_add W hWc hWb
  map_smul' c p := potLp_smul W hWc hWb c p

/-- Multiplication by the potential, as an operator on the Gauss–polynomial core. -/
def potCore (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (potPolyMap W hWc hWb).comp (coreEquiv (d := d)).symm.toLinearMap













end

end BookProof.QgHermiteOscillator


