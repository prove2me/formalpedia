-- Prove2me | Definitions.Def_ChapterUnboundedPosition
-- name    : ChapterUnboundedPosition
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:13:55.813437+00:00
-- url     : https://prove2.me/theorems/91588148-2c0d-4d24-915f-8d6049e59f2f
-- title:
--   Source: the *Boundary* paragraphs of proof plan appendix §E (`Book/ProofPlans.lean`) and the `ConditionalUnitary` chapte ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.UnboundedPosition`, source chapter `BookProof/ChapterUnboundedPosition.lean`).
--
--   Source: the *Boundary* paragraphs of proof plan appendix §E (`Book/ProofPlans.lean`) and the `ConditionalUnitary` chapter — everything the book formalizes about the dynamics-based unitary is carried by *bounded* operators (matrices on the cyclic lattice in `BookProof.ChapterContinuityUnitary`, bounded operators on `ℓ²(ℤ)` in `BookProof.ChapterContinuityUnitaryInfinite`, a bounded self-adjoint generator on `L²(μ)` in `BookProof.ChapterBornMeasure`). The remaining open layer is *unboundedness*.
--
--   This module makes that layer precise rather than rhetorical. For a real "multiplier" `f : ℤ → ℝ` — the lattice position field `f k = k` being the case of interest — it builds the multiplication operator on its **natural domain**
--
--   `D(f) = {ψ ∈ ℓ²(ℤ) : f · ψ ∈ ℓ²(ℤ)}`
--
--   (a submodule, `mulDomain`), proves that this domain is **dense** (`mulDomain_dense`, via the finitely supported vectors), that the operator is **symmetric** on it (`mulOp_symmetric`), and that for the position field it is genuinely **unbounded** (`position_unbounded`): no constant `C` satisfies `‖x̂ψ‖ ≤ C‖ψ‖` on the domain. So the object here is not a bounded operator in disguise; it is the first honest instance of the unbounded layer, and `position_not_boundedOperator` records that it is not the restriction of any bounded operator either.
--
--   The module then goes past symmetry in the two directions that matter for the book's claim.
--
--   * **Self-adjointness.** `adjointDomain_eq_mulDomain` shows the adjoint domain is *exactly* `D(f)` — nothing larger — and `adjoint_eq_mulOp` shows the adjoint acts by multiplication there. So the maximal multiplication operator, position included, is a genuine self-adjoint observable, not merely a symmetric one. * **The unitary group.** `phaseUnitary f t` is the pointwise phase `ψ k ↦ exp(i t f k) ψ k`, a `LinearIsometryEquiv` of `ℓ²(ℤ)` (`phaseUnitary_zero`, `phaseUnitary_add` give the one-parameter group law), strongly continuous at `0` for *every* state (`tendsto_phaseUnitary`), whose generator is the unbounded operator: for `ψ ∈ D(f)` the difference quotient converges in `ℓ²(ℤ)` to `i·f·ψ` (`tendsto_slope_phaseUnitary`), which is Stone's relation `dU/dt|₀ = iA` for an unbounded self-adjoint `A`.
--
--   What therefore remains genuinely open is *not* "symmetric ⟹ self-adjoint ⟹ a unitary group" — that implication is discharged here for multiplication operators — but the same package for unbounded operators that are not multiplication operators in the ambient basis (a continuum Laplacian, say), i.e. Stone's theorem in full generality.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterUnboundedPosition.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite

import Mathlib

import Mathlib
open BookProof.ChapterContinuityUnitaryInfinite

/-!
# The unbounded layer: a self-adjoint operator on `ℓ²(ℤ)` and the group it generates

Source: the *Boundary* paragraphs of proof plan appendix §E
(`Book/ProofPlans.lean`) and the `ConditionalUnitary` chapter — everything the
book formalizes about the dynamics-based unitary is carried by *bounded*
operators (matrices on the cyclic lattice in
`BookProof.ChapterContinuityUnitary`, bounded operators on `ℓ²(ℤ)` in
`BookProof.ChapterContinuityUnitaryInfinite`, a bounded self-adjoint generator on
`L²(μ)` in `BookProof.ChapterBornMeasure`).  The remaining open layer is
*unboundedness*.

This module makes that layer precise rather than rhetorical.  For a real
"multiplier" `f : ℤ → ℝ` — the lattice position field `f k = k` being the case of
interest — it builds the multiplication operator on its **natural domain**

  `D(f) = {ψ ∈ ℓ²(ℤ) : f · ψ ∈ ℓ²(ℤ)}`

(a submodule, `mulDomain`), proves that this domain is **dense**
(`mulDomain_dense`, via the finitely supported vectors), that the operator is
**symmetric** on it (`mulOp_symmetric`), and that for the position field it is
genuinely **unbounded** (`position_unbounded`): no constant `C` satisfies
`‖x̂ψ‖ ≤ C‖ψ‖` on the domain.  So the object here is not a bounded operator in
disguise; it is the first honest instance of the unbounded layer, and
`position_not_boundedOperator` records that it is not the restriction of any
bounded operator either.

The module then goes past symmetry in the two directions that matter for the
book's claim.

* **Self-adjointness.**  `adjointDomain_eq_mulDomain` shows the adjoint domain is
  *exactly* `D(f)` — nothing larger — and `adjoint_eq_mulOp` shows the adjoint
  acts by multiplication there.  So the maximal multiplication operator, position
  included, is a genuine self-adjoint observable, not merely a symmetric one.
* **The unitary group.**  `phaseUnitary f t` is the pointwise phase
  `ψ k ↦ exp(i t f k) ψ k`, a `LinearIsometryEquiv` of `ℓ²(ℤ)`
  (`phaseUnitary_zero`, `phaseUnitary_add` give the one-parameter group law),
  strongly continuous at `0` for *every* state (`tendsto_phaseUnitary`), whose
  generator is the unbounded operator: for `ψ ∈ D(f)` the difference quotient
  converges in `ℓ²(ℤ)` to `i·f·ψ` (`tendsto_slope_phaseUnitary`), which is
  Stone's relation `dU/dt|₀ = iA` for an unbounded self-adjoint `A`.

What therefore remains genuinely open is *not* "symmetric ⟹ self-adjoint ⟹ a
unitary group" — that implication is discharged here for multiplication
operators — but the same package for unbounded operators that are not
multiplication operators in the ambient basis (a continuum Laplacian, say), i.e.
Stone's theorem in full generality.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped ENNReal InnerProductSpace

namespace BookProof.ChapterUnboundedPosition


/-! ## The natural domain of a multiplication operator -/

/-- The **natural domain** `D(f) = {ψ ∈ ℓ²(ℤ) : f·ψ ∈ ℓ²(ℤ)}` of multiplication
by a real field `f`, as a submodule of `ℓ²(ℤ)`. -/
def mulDomain (f : ℤ → ℝ) : Submodule ℂ L2Z where
  carrier := {psi : L2Z | Memℓp (fun k => (f k : ℂ) * (psi : ℤ → ℂ) k) 2}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, lp.coeFn_zero, Pi.zero_apply, mul_zero]
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb
    have heq : (fun k => (f k : ℂ) * ((a + b : L2Z) : ℤ → ℂ) k)
        = (fun k => (f k : ℂ) * (a : ℤ → ℂ) k) + fun k => (f k : ℂ) * (b : ℤ → ℂ) k := by
      funext k
      simp [mul_add]
    change Memℓp _ 2
    rw [heq]
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    have heq : (fun k => (f k : ℂ) * ((c • a : L2Z) : ℤ → ℂ) k)
        = c • fun k => (f k : ℂ) * (a : ℤ → ℂ) k := by
      funext k
      simp [mul_left_comm]
    change Memℓp _ 2
    rw [heq]
    exact ha.const_smul c



/-- Multiplication by `f`, on its natural domain. -/
noncomputable def mulOp (f : ℤ → ℝ) : mulDomain f →ₗ[ℂ] L2Z where
  toFun psi := ⟨fun k => (f k : ℂ) * ((psi : L2Z) : ℤ → ℂ) k, psi.2⟩
  map_add' a b := by
    ext k
    simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c a := by
    ext k
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul]
    ring





/-! ## The domain is dense -/







/-! ## The position field really is unbounded -/

/-- The lattice **position field** `x̂ : k ↦ k`. -/
def positionField : ℤ → ℝ := fun k => (k : ℝ)





/-! ## The adjoint: the maximal multiplication operator is self-adjoint -/





/-- The domain of the adjoint of multiplication by `f`. -/
def adjointDomain (f : ℤ → ℝ) : Set L2Z :=
  {phi | ∃ eta : L2Z, ∀ psi : mulDomain f, ⟪mulOp f psi, phi⟫_ℂ = ⟪(psi : L2Z), eta⟫_ℂ}







/-! ## The unitary group generated by the multiplication operator -/

/-- The phase `e^{i t f k}` of the group generated by multiplication by `f`. -/
noncomputable def phase (f : ℤ → ℝ) (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp (Complex.I * ((t * f k : ℝ) : ℂ))

theorem norm_phase (f : ℤ → ℝ) (t : ℝ) (k : ℤ) : ‖phase f t k‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _



theorem memℓp_phase (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) :
    Memℓp (fun k => phase f t k * (psi : ℤ → ℂ) k) 2 := by
  refine BookProof.ChapterContinuityUnitaryInfinite.memℓp_two_of_summable ?_
  have h : ∀ k : ℤ, ‖phase f t k * (psi : ℤ → ℂ) k‖ ^ 2 = ‖(psi : ℤ → ℂ) k‖ ^ 2 := by
    intro k
    rw [norm_mul, norm_phase, one_mul]
  simpa only [h] using BookProof.ChapterContinuityUnitaryInfinite.summable_normSq psi

/-- Multiplication by the phase `e^{i t f}`, as a linear map. -/
noncomputable def phaseLin (f : ℤ → ℝ) (t : ℝ) : L2Z →ₗ[ℂ] L2Z where
  toFun psi := ⟨fun k => phase f t k * (psi : ℤ → ℂ) k, memℓp_phase f t psi⟩
  map_add' a b := by
    ext k
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c a := by
    ext k
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem phaseLin_apply (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) (k : ℤ) :
    ((phaseLin f t psi : L2Z) : ℤ → ℂ) k = phase f t k * (psi : ℤ → ℂ) k := rfl

theorem phaseLin_add (f : ℤ → ℝ) (s t : ℝ) (psi : L2Z) :
    phaseLin f s (phaseLin f t psi) = phaseLin f (s + t) psi := by
  ext k
  simp only [phaseLin_apply, phase, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem phaseLin_zero (f : ℤ → ℝ) (psi : L2Z) : phaseLin f 0 psi = psi := by
  ext k
  simp [phase]

theorem phaseLin_norm (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) : ‖phaseLin f t psi‖ = ‖psi‖ := by
  have key : ‖phaseLin f t psi‖ ^ 2 = ‖psi‖ ^ 2 := by
    rw [BookProof.ChapterContinuityUnitaryInfinite.norm_sq_eq_tsum,
      BookProof.ChapterContinuityUnitaryInfinite.norm_sq_eq_tsum]
    refine tsum_congr fun k => ?_
    rw [phaseLin_apply, norm_mul, norm_phase, one_mul]
  have hpow : ‖phaseLin f t psi‖ ^ ((2 : ℕ) : ℝ) = ‖psi‖ ^ ((2 : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast] using key
  exact Real.rpow_left_injOn (x := ((2 : ℕ) : ℝ)) (by norm_num)
    (norm_nonneg _) (norm_nonneg _) hpow

/-- **The unitary group `U t = e^{i t f}` generated by multiplication by `f`.**
Every `U t` is a unitary of `ℓ²(ℤ)` — for the position field this is the group
generated by an *unbounded* self-adjoint observable. -/
noncomputable def phaseUnitary (f : ℤ → ℝ) (t : ℝ) : L2Z ≃ₗᵢ[ℂ] L2Z where
  toLinearEquiv :=
    { phaseLin f t with
      invFun := phaseLin f (-t)
      left_inv := fun psi => by
        change phaseLin f (-t) (phaseLin f t psi) = psi
        rw [phaseLin_add, neg_add_cancel, phaseLin_zero]
      right_inv := fun psi => by
        change phaseLin f t (phaseLin f (-t) psi) = psi
        rw [phaseLin_add, add_neg_cancel, phaseLin_zero] }
  norm_map' := phaseLin_norm f t















end BookProof.ChapterUnboundedPosition


