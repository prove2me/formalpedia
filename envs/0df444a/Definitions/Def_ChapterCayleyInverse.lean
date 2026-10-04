-- Prove2me | Definitions.Def_ChapterCayleyInverse
-- name    : ChapterCayleyInverse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T19:02:50.757298+00:00
-- url     : https://prove2.me/theorems/da6ac5de-7a56-47b0-a756-f94c08dd9d4b
-- title:
--   The Lean 4 theorem `isSelfAdjointOn_of_surjective` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCayleyInverse.lean`): generated def bundle for ChapterCayleyInverse. See BookProof/ChapterCayleyInverse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCayleyInverse.lean

import Definitions.Def_ChapterCayleyTransform
import Mathlib


/-!
# The inverse Cayley transform: unitaries give self-adjoint operators

`BookProof.ChapterCayleyTransform` sends a densely defined self-adjoint operator
`A` to the unitary `V = (A - i)(A + i)⁻¹`.  This module goes the other way and
thereby closes the correspondence.

Two ingredients:

* `isSelfAdjointOn_of_surjective` — the **basic criterion**: a symmetric operator
  for which `A + i` and `A - i` are both *onto* is self-adjoint (no density and
  no closedness needed).  The proof is the standard three-line inner-product
  argument, and this is the criterion by which almost all concrete self-adjoint
  operators are recognised.
* The **inverse Cayley transform** of a unitary `V` such that `1 - V` is
  injective: on the domain `D = ran(1 - V)` the operator
  `A = i(1 + V)(1 - V)⁻¹` (`invCayleyOp`) is symmetric
  (`invCayleyOp_symmetric`), `A ± i` are onto (`invCayleyOp_add_i_surjective`,
  `invCayleyOp_sub_i_surjective` — indeed `(A + i)(1 - V)y = 2iy` and
  `(A - i)(1 - V)y = 2iVy`), hence `A` is self-adjoint
  (`invCayleyOp_isSelfAdjointOn`).  With density of `ran(1 - V)` this packages as
  an `UnboundedSelfAdjoint` bundle, `ofUnitary`.

The two constructions are mutually inverse:

* `cayley_ofUnitary` — the Cayley transform of `ofUnitary V` is `V` again;
* `invCayleyDomain_cayley` and `invCayleyOp_cayley` — starting from a
  self-adjoint `T`, the inverse Cayley transform of `cayley T` has domain
  `D(T)` and equals `T` there.

So self-adjoint operators correspond exactly to unitaries with `1` not an
eigenvalue and `ran(1 - V)` dense: the unbounded layer is faithfully encoded by a
*bounded* object.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped InnerProductSpace

namespace BookProof.ChapterCayleyInverse

open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The basic criterion for self-adjointness -/

/-- **Basic criterion.**  A symmetric operator whose shifts `A + i` and `A - i`
are surjective is self-adjoint. -/
theorem isSelfAdjointOn_of_surjective {D : Submodule ℂ H} {A : D →ₗ[ℂ] H}
    (hsym : IsSymmetricOn D A)
    (hplus : ∀ z : H, ∃ psi : D, A psi + Complex.I • (psi : H) = z)
    (hminus : ∀ z : H, ∃ psi : D, A psi - Complex.I • (psi : H) = z) :
    IsSelfAdjointOn D A := by
  ext phi
  constructor
  · rintro ⟨eta, heta⟩
    obtain ⟨chi, hchi⟩ := hminus (eta - Complex.I • phi)
    have key : ∀ psi : D, ⟪A psi + Complex.I • (psi : H), phi - (chi : H)⟫_ℂ = 0 := by
      intro psi
      have h1 : ⟪A psi + Complex.I • (psi : H), phi⟫_ℂ = ⟪(psi : H), eta - Complex.I • phi⟫_ℂ := by
        rw [inner_add_left, heta psi, inner_smul_left, inner_sub_right, inner_smul_right]
        simp [Complex.conj_I]
        ring
      have h2 : ⟪A psi + Complex.I • (psi : H), (chi : H)⟫_ℂ
          = ⟪(psi : H), eta - Complex.I • phi⟫_ℂ := by
        rw [← hchi, inner_sub_right, inner_add_left, inner_smul_left, inner_smul_right,
          hsym psi chi]
        simp [Complex.conj_I]
        ring
      rw [inner_sub_right, h1, h2, sub_self]
    obtain ⟨psi0, hpsi0⟩ := hplus (phi - (chi : H))
    have := key psi0
    rw [hpsi0, inner_self_eq_zero] at this
    have : phi = (chi : H) := sub_eq_zero.mp this
    rw [this]
    exact chi.2
  · intro hphi
    exact ⟨A ⟨phi, hphi⟩, fun psi => hsym psi ⟨phi, hphi⟩⟩

/-! ## The inverse Cayley transform of a unitary -/

variable (V : H ≃ₗᵢ[ℂ] H)

/-- The operator `1 - V`. -/
def oneSubU : H →ₗ[ℂ] H where
  toFun x := x - V x
  map_add' x y := by simp only [map_add]; abel
  map_smul' c x := by simp only [map_smul, RingHom.id_apply, smul_sub]

/-- The operator `1 + V`. -/
def onePlusU : H →ₗ[ℂ] H where
  toFun x := x + V x
  map_add' x y := by simp only [map_add]; abel
  map_smul' c x := by simp only [map_smul, RingHom.id_apply, smul_add]

@[simp] theorem oneSubU_apply (x : H) : oneSubU V x = x - V x := rfl
@[simp] theorem onePlusU_apply (x : H) : onePlusU V x = x + V x := rfl

/-- The domain of the inverse Cayley transform: `ran(1 - V)`. -/
def invCayleyDomain : Submodule ℂ H := LinearMap.range (oneSubU V)

variable (hinj : Function.Injective (oneSubU V))

/-- `1 - V` as a linear equivalence onto its range. -/
noncomputable def oneSubEquiv : H ≃ₗ[ℂ] invCayleyDomain V :=
  LinearEquiv.ofInjective (oneSubU V) hinj

@[simp] theorem oneSubEquiv_coe (y : H) :
    ((oneSubEquiv V hinj y : invCayleyDomain V) : H) = y - V y := rfl

/-- The **inverse Cayley transform** `A = i(1 + V)(1 - V)⁻¹`, on `ran(1 - V)`. -/
noncomputable def invCayleyOp : invCayleyDomain V →ₗ[ℂ] H :=
  (Complex.I • onePlusU V) ∘ₗ ((oneSubEquiv V hinj).symm : invCayleyDomain V →ₗ[ℂ] H)

theorem invCayleyOp_apply (y : H) :
    invCayleyOp V hinj (oneSubEquiv V hinj y) = Complex.I • (y + V y) := by
  simp [invCayleyOp]

/-- The inverse Cayley transform is symmetric. -/
theorem invCayleyOp_symmetric : IsSymmetricOn (invCayleyDomain V) (invCayleyOp V hinj) := by
  intro psi phi
  obtain ⟨y, rfl⟩ := (oneSubEquiv V hinj).surjective psi
  obtain ⟨z, rfl⟩ := (oneSubEquiv V hinj).surjective phi
  rw [invCayleyOp_apply, invCayleyOp_apply, oneSubEquiv_coe, oneSubEquiv_coe]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, V.inner_map_map, Complex.conj_I]
  ring

/-- `(A + i)(1 - V)y = 2iy`. -/
theorem invCayleyOp_add_i (y : H) :
    invCayleyOp V hinj (oneSubEquiv V hinj y)
        + Complex.I • ((oneSubEquiv V hinj y : invCayleyDomain V) : H)
      = (2 * Complex.I) • y := by
  rw [invCayleyOp_apply, oneSubEquiv_coe]
  module

/-- `(A - i)(1 - V)y = 2iVy`. -/
theorem invCayleyOp_sub_i (y : H) :
    invCayleyOp V hinj (oneSubEquiv V hinj y)
        - Complex.I • ((oneSubEquiv V hinj y : invCayleyDomain V) : H)
      = (2 * Complex.I) • V y := by
  rw [invCayleyOp_apply, oneSubEquiv_coe]
  module

theorem invCayleyOp_add_i_surjective (z : H) :
    ∃ psi : invCayleyDomain V,
      invCayleyOp V hinj psi + Complex.I • (psi : H) = z := by
  refine ⟨oneSubEquiv V hinj ((2 * Complex.I : ℂ)⁻¹ • z), ?_⟩
  rw [invCayleyOp_add_i, smul_smul, mul_inv_cancel₀ (by simp [Complex.I_ne_zero]), one_smul]

theorem invCayleyOp_sub_i_surjective (z : H) :
    ∃ psi : invCayleyDomain V,
      invCayleyOp V hinj psi - Complex.I • (psi : H) = z := by
  refine ⟨oneSubEquiv V hinj (V.symm ((2 * Complex.I : ℂ)⁻¹ • z)), ?_⟩
  rw [invCayleyOp_sub_i, V.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ (by simp [Complex.I_ne_zero]), one_smul]

/-- The inverse Cayley transform of a unitary with `1 - V` injective is
**self-adjoint** on `ran(1 - V)`. -/
theorem invCayleyOp_isSelfAdjointOn :
    IsSelfAdjointOn (invCayleyDomain V) (invCayleyOp V hinj) :=
  isSelfAdjointOn_of_surjective (invCayleyOp_symmetric V hinj)
    (invCayleyOp_add_i_surjective V hinj) (invCayleyOp_sub_i_surjective V hinj)

/-- The unbounded self-adjoint operator attached to a unitary `V` for which `1`
is not an eigenvalue and `ran(1 - V)` is dense. -/
noncomputable def ofUnitary (hdense : Dense ((invCayleyDomain V : Submodule ℂ H) : Set H)) :
    UnboundedSelfAdjoint H where
  domain := invCayleyDomain V
  op := invCayleyOp V hinj
  denseDomain := hdense
  symmetric := invCayleyOp_symmetric V hinj
  selfAdjoint := invCayleyOp_isSelfAdjointOn V hinj

/-! ## The two constructions are mutually inverse -/

section RoundTrip

variable [CompleteSpace H]



variable (T : UnboundedSelfAdjoint H)







end RoundTrip

end BookProof.ChapterCayleyInverse


