-- Prove2me | Definitions.Def_ChapterNavierStokesDifferentialL2
-- name    : ChapterNavierStokesDifferentialL2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:09:21.665616+00:00
-- url     : https://prove2.me/theorems/59dee199-fd46-4bba-a46f-6a23347d3341
-- title:
--   `BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component fiber Hamiltonian `H = ∑ᵢ ½(πᵢVᵢ + ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesDifferentialL2`, source chapter `BookProof/ChapterNavierStokesDifferentialL2.lean`).
--
--   `BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component fiber Hamiltonian `H = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)`, `Vᵢ(u) = ∑ₖ A_{ik}u_k + c_i`, is essentially self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, and `BookProof.ChapterNavierStokesCanonicalVector` shows that this sequence-space matrix *is* the Weyl-ordered expression in the abstract ladder operators of that space. What both modules record as the honest open step is the **differential realization**: the operator written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication operator, on the Hermite core of `L²(du₁du₂du₃)`. This module takes that step.
--
--   The Hilbert space is `L²(ℝ³)` and the dense domain is the Gauss–polynomial (product Hermite) core `polyGaussCore` of `BookProof.ChapterHermiteProductCore`: the functions `p(u)·e^{-‖u‖²/4}` with `p` a polynomial. Since `pgMap` is injective, the core carries the polynomial coordinates `coreEquiv`, and an operator on the core is given by a polynomial operator (`coreOp`). Two such operators are the physical ones:
--
--   * `posOp i` — multiplication by the coordinate `uᵢ` (`pgFun_mulXPoly`); * `momOp i` — the differential operator `πᵢ = −i ∂/∂uᵢ`. That it *is* the derivative is `momOp_apply_eq_differential`: the value of `momOp i` at `p·e^{-‖u‖²/4}` is, pointwise, `−i` times the honest derivative `deriv (fun t => f (u with uᵢ := t)) uᵢ` of the function along the `i`-th coordinate (Mathlib's `deriv`, `hasDerivAt_pgFun_sec`).
--
--   `comm_momOp_posOp` is the canonical commutation relation `[πᵢ, u_k] = −i δ_{ik}` for these genuinely differential operators.
--
--   `nsDiffH A c = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` with `Vᵢ` the multiplication operator by the affine field `∑ₖ A_{ik}u_k + c_i` is the Weyl quantization of the Navier–Stokes quadratic symbol `A_i(u) = u_j u_{i,j} − ν u_{i,jj}` at one Eulerian fiber (linear part the velocity gradient, constant part `−ν` times the velocity Laplacian).
--
--   The **unitary transport** is `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)`, the Hilbert-basis isomorphism given by the product Hermite functions (`BookProof.ChapterHermiteProductBasis`). It carries the finite-mode core onto the Gauss–polynomial core (`map_finiteModes`) and the abstract ladder operators onto the differential ones (`intertwine_ann`, `intertwine_cre`), hence the abstract canonical Hamiltonian onto the differential one (`conj_canH`). The conclusions:
--
--   * `nsDiffH_essentiallySelfAdjointOn_core` — the **differentially written** Navier–Stokes quadratic symbol is essentially self-adjoint on the Hermite core of `L²(ℝ³)`, for every real velocity gradient and every constant part; * `nsQuadraticDiffH_essentiallySelfAdjointOn_core` — the same with the coefficients spelled out as `(ν, u_{i,j}, u_{i,jj})`; * `nsDiffH_not_bounded`, `polyGaussCore_dense_L2` — the operator is genuinely unbounded and the domain is dense, so the statement is not a bounded-operator artefact.
--
--   Nothing here claims global regularity of the *classical* Navier–Stokes PDE (Contention D5, the deliberate scope cut): the theorem is about the Hilbert-space operator at one Eulerian fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib
import Mathlib

import Mathlib
import Mathlib
import Mathlib
import Mathlib

import Mathlib
import Mathlib

import Mathlib

import Mathlib
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.FarisLavine

/-!
# The differential realization of the Navier–Stokes quadratic symbol on `L²(du₁du₂du₃)`

`BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component
fiber Hamiltonian `H = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)`, `Vᵢ(u) = ∑ₖ A_{ik}u_k + c_i`, is essentially
self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, and
`BookProof.ChapterNavierStokesCanonicalVector` shows that this sequence-space matrix *is*
the Weyl-ordered expression in the abstract ladder operators of that space.  What both
modules record as the honest open step is the **differential realization**: the operator
written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication operator, on the Hermite
core of `L²(du₁du₂du₃)`.  This module takes that step.

## The setting

The Hilbert space is `L²(ℝ³)` and the dense domain is the Gauss–polynomial (product
Hermite) core `polyGaussCore` of `BookProof.ChapterHermiteProductCore`: the functions
`p(u)·e^{-‖u‖²/4}` with `p` a polynomial.  Since `pgMap` is injective, the core carries the
polynomial coordinates `coreEquiv`, and an operator on the core is given by a polynomial
operator (`coreOp`).  Two such operators are the physical ones:

* `posOp i` — multiplication by the coordinate `uᵢ` (`pgFun_mulXPoly`);
* `momOp i` — the differential operator `πᵢ = −i ∂/∂uᵢ`.  That it *is* the derivative is
  `momOp_apply_eq_differential`: the value of `momOp i` at `p·e^{-‖u‖²/4}` is, pointwise,
  `−i` times the honest derivative `deriv (fun t => f (u with uᵢ := t)) uᵢ` of the function
  along the `i`-th coordinate (Mathlib's `deriv`, `hasDerivAt_pgFun_sec`).

`comm_momOp_posOp` is the canonical commutation relation `[πᵢ, u_k] = −i δ_{ik}` for these
genuinely differential operators.

## The Hamiltonian and the transport

`nsDiffH A c = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` with `Vᵢ` the multiplication operator by the affine
field `∑ₖ A_{ik}u_k + c_i` is the Weyl quantization of the Navier–Stokes quadratic symbol
`A_i(u) = u_j u_{i,j} − ν u_{i,jj}` at one Eulerian fiber (linear part the velocity
gradient, constant part `−ν` times the velocity Laplacian).

The **unitary transport** is `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)`, the Hilbert-basis
isomorphism given by the product Hermite functions
(`BookProof.ChapterHermiteProductBasis`).  It carries the finite-mode core onto the
Gauss–polynomial core (`map_finiteModes`) and the abstract ladder operators onto the
differential ones (`intertwine_ann`, `intertwine_cre`), hence the abstract canonical
Hamiltonian onto the differential one (`conj_canH`).  The conclusions:

* `nsDiffH_essentiallySelfAdjointOn_core` — the **differentially written** Navier–Stokes
  quadratic symbol is essentially self-adjoint on the Hermite core of `L²(ℝ³)`, for every
  real velocity gradient and every constant part;
* `nsQuadraticDiffH_essentiallySelfAdjointOn_core` — the same with the coefficients spelled
  out as `(ν, u_{i,j}, u_{i,jj})`;
* `nsDiffH_not_bounded`, `polyGaussCore_dense_L2` — the operator is genuinely unbounded and
  the domain is dense, so the statement is not a bounded-operator artefact.

## Honest boundary

Nothing here claims global regularity of the *classical* Navier–Stokes PDE (Contention D5,
the deliberate scope cut): the theorem is about the Hilbert-space operator at one Eulerian
fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical
coordinates.
-/

namespace BookProof.NavierStokesFlow.DifferentialL2

open MeasureTheory MvPolynomial

noncomputable section

/-! ## Differentiating along one coordinate -/

variable {d : ℕ}

/-- The line through `x` in the `i`-th coordinate direction. -/
def sec (i : Fin d) (x : Vd d) (t : ℝ) : Vd d :=
  (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i t) : Vd d)















/-! ## The polynomial coordinates of the core -/

/-- The Gauss–polynomial core, coordinatized by polynomials. -/
def coreEquiv : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] (polyGaussCore (d := d)) :=
  LinearEquiv.ofInjective (pgMap (d := d)) (pgMap_injective (d := d))



/-- An operator on the core, given by an operator on the polynomial coordinates. -/
def coreOp (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  (coreEquiv (d := d)).toLinearMap ∘ₗ T ∘ₗ (coreEquiv (d := d)).symm.toLinearMap





/-! ## The canonical pair: multiplication by `uᵢ` and `−i ∂/∂uᵢ` -/

/-- Multiplication by the coordinate, on polynomials. -/
def mulXPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := X i * p
  map_add' p q := by rw [mul_add]
  map_smul' c p := by simp

/-- The momentum `−i ∂/∂uᵢ`, on polynomial coordinates. -/
def momPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p))
  map_add' p q := by simp only [map_add, mul_add]; ring
  map_smul' c p := by
    simp only [RingHom.id_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul]; ring





/-- **The position operator** `uᵢ` on the Hermite core of `L²(ℝᵈ)`. -/
def posOp (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  coreOp (mulXPoly i)

/-- **The momentum operator** `πᵢ = −i ∂/∂uᵢ` on the Hermite core of `L²(ℝᵈ)`. -/
def momOp (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  coreOp (momPoly i)











/-! ## The unitary transport from the three-mode sequence space

The product Hermite functions indexed by `Vel = Fin 3 → ℕ` form a Hilbert basis of
`L²(ℝ³)`, so the sequence space `ℓ²(Vel)` of
`BookProof.ChapterNavierStokesThreeComponent` is unitarily `L²(du₁du₂du₃)`. -/

/-- A three-mode index, read as a finitely supported multi-index. -/
def velIdx : Vel ≃ (Fin 3 →₀ ℕ) := Finsupp.equivFunOnFinite.symm







/-- The product Hermite function attached to a three-mode index. -/
def hermiteVel (b : Vel) : L2d 3 := hermiteMvLp (velIdx b)

theorem orthonormal_hermiteVel : Orthonormal ℂ hermiteVel :=
  orthonormal_hermiteMvLp.comp velIdx velIdx.injective

theorem range_hermiteVel : Set.range hermiteVel = Set.range (hermiteMvLp (d := 3)) :=
  velIdx.surjective.range_comp _

/-- **The three-mode product Hermite basis of `L²(ℝ³)`.** -/
def velBasis : HilbertBasis Vel ℂ (L2d 3) :=
  HilbertBasis.mk orthonormal_hermiteVel
    (by
      rw [range_hermiteVel, span_hermiteMvLp]
      have hd := polyGaussCore_dense (d := 3)
      rw [Submodule.dense_iff_topologicalClosure_eq_top] at hd
      rw [hd])

@[simp] theorem velBasis_apply (b : Vel) : velBasis b = hermiteVel b := by
  rw [velBasis, HilbertBasis.coe_mk]

/-- **The unitary transport** `ℓ²(Vel) ≃ L²(du₁du₂du₃)` given by the product Hermite
basis. -/
def velUnitary : L2I Vel ≃ₗᵢ[ℂ] L2d 3 := velBasis.repr.symm

@[simp] theorem velUnitary_single (b : Vel) :
    velUnitary (lp.single 2 b (1 : ℂ)) = hermiteVel b := by
  rw [velUnitary, velBasis.repr_symm_single, velBasis_apply]

/-! ### The finite-mode core is spanned by its basis states -/

theorem coreState_coe (b : Vel) :
    ((coreState b : lpFiniteModes Vel) : L2I Vel) = lp.single 2 b (1 : ℂ) := rfl

/-- The finite-mode core of `ℓ²(Vel)` is the algebraic span of the basis states. -/
theorem lpFiniteModes_eq_span :
    lpFiniteModes Vel
      = Submodule.span ℂ (Set.range fun b : Vel => (lp.single 2 b (1 : ℂ) : L2I Vel)) := by
  classical
  refine le_antisymm (fun f hf => ?_) ?_
  · have hfin : (Function.support ((f : Vel → ℂ))).Finite := hf
    have hsum : f = ∑ b ∈ hfin.toFinset, ((f : Vel → ℂ) b) • (lp.single 2 b (1 : ℂ)) := by
      refine lp.ext (funext fun j => ?_)
      rw [lp.coeFn_sum]
      simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq hfin.toFinset j (fun b => (f : Vel → ℂ) b)]
      by_cases hj : j ∈ hfin.toFinset
      · rw [if_pos hj]
      · rw [if_neg hj]
        have : j ∉ Function.support ((f : Vel → ℂ)) := by
          simpa [Set.Finite.mem_toFinset] using hj
        simpa [Function.mem_support] using this
    rw [hsum]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact lpSingle_mem_lpFiniteModes b 1

/-- The basis states span the finite-mode core as a module in its own right. -/
theorem span_coreState :
    Submodule.span ℂ (Set.range coreState) = (⊤ : Submodule ℂ (lpFiniteModes Vel)) := by
  refine Submodule.map_injective_of_injective
    (Submodule.injective_subtype (lpFiniteModes Vel)) ?_
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact lpFiniteModes_eq_span.symm



/-! ### The ladder action on the basis states -/







/-! ### The transport of the core, and of the ladder operators -/

theorem hermiteVel_mem_core (b : Vel) : hermiteVel b ∈ polyGaussCore (d := 3) :=
  hermiteMvLp_mem_core (velIdx b)



theorem velUnitary_mem_core (x : lpFiniteModes Vel) :
    velUnitary ((x : L2I Vel)) ∈ polyGaussCore (d := 3) := by
  have hspan : (⊤ : Submodule ℂ (lpFiniteModes Vel))
      ≤ (polyGaussCore (d := 3)).comap
        (velUnitary.toLinearEquiv.toLinearMap ∘ₗ (lpFiniteModes Vel).subtype) := by
    rw [← span_coreState, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    change velUnitary ((coreState b : L2I Vel)) ∈ polyGaussCore (d := 3)
    rw [coreState_coe, velUnitary_single]
    exact hermiteVel_mem_core b
  exact hspan Submodule.mem_top

/-- **The transport of the finite-mode core into the Gauss–polynomial core.** -/
def embedCore : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  LinearMap.codRestrict _ (velUnitary.toLinearEquiv.toLinearMap ∘ₗ (lpFiniteModes Vel).subtype)
    velUnitary_mem_core





/-- **The annihilation operator on the Hermite core of `L²(ℝ³)`**: `∂ᵢ + uᵢ/2`. -/
def annOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  coreOp (annPoly i)

/-- **The creation operator on the Hermite core of `L²(ℝ³)`**: `uᵢ/2 − ∂ᵢ`. -/
def creOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  coreOp (crePoly i)





/-! ### The algebra of intertwined operators -/

/-- `T'` is the transport of `T`: the two agree through `embedCore`. -/
def Intertwined (T : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel)
    (T' : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3))) : Prop :=
  ∀ x, T' (embedCore x) = embedCore (T x)

















/-! ### Position and momentum as ladder combinations -/





/-! ### The transported canonical pair -/









/-! ### The differentially written Navier–Stokes quadratic symbol -/

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

/-- **The affine fiber field as a multiplication operator** on the Hermite core of
`L²(ℝ³)`: `Vᵢ(u) = ∑ₖ A_{ik} uₖ + cᵢ`. -/
def fieldOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  (∑ k, ((A i k : ℝ) : ℂ) • posOp k) + (((c i : ℝ) : ℂ) • LinearMap.id)

/-- **The differentially written Weyl-ordered Hamiltonian**
`∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` on the Hermite core of `L²(du₁du₂du₃)`, with `πᵢ = −i ∂/∂uᵢ`
and `Vᵢ` multiplication by the affine field. -/
def nsDiffH : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  ∑ i, ((1 : ℂ) / 2) • ((momOp i).comp (fieldOp A c i) + (fieldOp A c i).comp (momOp i))





/-! ## Essential self-adjointness of the differentially written operator -/









/-! ## The Navier–Stokes reading of the coefficients -/

/-- **The quantized Navier–Stokes quadratic symbol on `L²(du₁du₂du₃)`**,
`∑ᵢ ½(πᵢ Aᵢ + Aᵢ πᵢ)` with `Aᵢ(u) = ∑ⱼ (grad i j) uⱼ − ν (lap i)`, `πᵢ = −i ∂/∂uᵢ`. -/
def nsQuadraticDiffH (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  nsDiffH grad (fun i => -(nu * lap i))



end

end BookProof.NavierStokesFlow.DifferentialL2


