-- Prove2me | Definitions.Def_ChapterScalarDGammaEsa
-- name    : ChapterScalarDGammaEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-09T10:08:45.886988+00:00
-- url     : https://prove2.me/theorems/4572a14a-8f53-404a-ab18-98a6d313c017
-- title:
--   Chapter ScalarDGammaEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterScalarDGammaEsa.lean`): generated def bundle for ChapterScalarDGammaEsa. See BookProof/ChapterScalarDGammaEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalarDGammaEsa.lean

import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Mathlib
import Theorems.Thm_BookProof_TensorCore_sectorOp_apply


/-!
# An unconditional instance: second quantization of a scalar one-particle operator

The main theorem of `BookProof/ChapterSecondQuantizationCoreEsa.lean` carries one hypothesis,
sector by sector: essential self-adjointness of the derivation `dΓ(A)⁽ⁿ⁾` on the *full*
tensor power `D₂^{⊗n}` of the domain of the closure.  This module discharges that hypothesis
completely in a concrete family of examples — the **scalar** one-particle operators
`A = c • id` with `c : ℝ`, defined on all of `H` — and thereby produces an unconditional
statement of the second quantization theorem over an arbitrary dense core `D`:

> If `D ⊆ H` is any dense subspace, then `dΓ(c • id)` is essentially self-adjoint on the
> finite-particle domain `𝓕_fin(D)`.

Here `D` is a core for `c • id` but is in general *not* invariant under anything and carries
no resolvent; the passage from `H` to `D` is exactly the core transfer principle.  On the
`n`-particle sector the derivation is the scalar `n · c`, which is bounded, so the
sector hypothesis follows from the elementary criterion
`BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense`.

## Contents

* `scalarOp` — the one-particle operator `c • id` on `⊤`;
* `symmetricOn_scalarOp`, `isGraphCore_scalarOp` — it is symmetric, and every dense subspace
  is a core for it;
* `derPow_scalar` — the sector derivation of a scalar operator is the scalar `n · c`;
* `essentiallySelfAdjointOn_fockSectorDom_scalar` — the sector hypothesis, proved;
* `dGamma_scalar_essentiallySelfAdjointOn_fockCore` — **the unconditional theorem**.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.ScalarDGamma

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
  BookProof.SecondQuantizationCore BookProof.DirectSumEsa

noncomputable section

/-! ## The elementary-tensor equations of `inclPow` / `derPow`

The platform's published `Def_ChapterTensorGraphCore` carries the definitions but not these
three `rfl` equations, so each consumer states them itself. -/

@[simp] theorem inclPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (n : ℕ)
    (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    inclPow Hs D₂ (n + 1) (a ⊗ₜ[ℂ] b) = (a : Hs.carrier) ⊗ₜ[ℂ] inclPow Hs D₂ n b := rfl

@[simp] theorem derPow_zero (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (x : ((domSpace Hs D₂).pow 0)) :
    derPow Hs D₂ A 0 x = 0 := rfl

@[simp] theorem derPow_tmul (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
    (A : D₂ →ₗ[ℂ] Hs.carrier) (n : ℕ) (a : D₂) (b : ((domSpace Hs D₂).pow n)) :
    derPow Hs D₂ A (n + 1) (a ⊗ₜ[ℂ] b)
      = (A a) ⊗ₜ[ℂ] inclPow Hs D₂ n b + (a : Hs.carrier) ⊗ₜ[ℂ] derPow Hs D₂ A n b := rfl

variable (Hs : IPSpace) (c : ℝ)

/-! ## The scalar one-particle operator -/

/-- The scalar one-particle operator `A = c • id`, defined on all of `H`. -/
def scalarOp : (⊤ : Submodule ℂ Hs.carrier) →ₗ[ℂ] Hs.carrier :=
  (c : ℂ) • (⊤ : Submodule ℂ Hs.carrier).subtype

@[simp] theorem scalarOp_apply (x : (⊤ : Submodule ℂ Hs.carrier)) :
    scalarOp Hs c x = (c : ℂ) • (x : Hs.carrier) := rfl

/-- A real scalar operator is symmetric. -/
theorem symmetricOn_scalarOp : SymmetricOn ⊤ (scalarOp Hs c) := by
  intro x y
  rw [scalarOp_apply, scalarOp_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- **Every dense subspace is a core for a scalar operator.** -/
theorem isGraphCore_scalarOp {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) : IsGraphCore D (scalarOp Hs c) := by
  intro x ε hε
  have hden : (0 : ℝ) < 1 + |c| := by positivity
  have hpos : 0 < ε / (1 + |c|) := by positivity
  obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.mp (hdense (x : Hs.carrier)) _ hpos
  have hxy : ‖(x : Hs.carrier) - y‖ < ε / (1 + |c|) := by rw [← dist_eq_norm]; exact hy
  have hmul : (1 + |c|) * ‖(x : Hs.carrier) - y‖ < ε := by
    have := (mul_lt_mul_of_pos_left hxy hden)
    calc (1 + |c|) * ‖(x : Hs.carrier) - y‖ < (1 + |c|) * (ε / (1 + |c|)) := this
      _ = ε := by field_simp
  have hnn : 0 ≤ ‖(x : Hs.carrier) - y‖ := norm_nonneg _
  refine ⟨⟨y, trivial⟩, hyD, ?_, ?_⟩
  · nlinarith [abs_nonneg c]
  · have hEq : scalarOp Hs c x - scalarOp Hs c ⟨y, trivial⟩
        = (c : ℂ) • ((x : Hs.carrier) - y) := by
      simp only [scalarOp_apply]
      rw [smul_sub]
    rw [hEq, norm_smul]
    have hc : ‖(c : ℂ)‖ = |c| := by simp
    rw [hc]
    nlinarith

/-! ## The sector derivation of a scalar operator -/

/-- The sector derivation of the scalar operator `c • id` is the scalar `n · c`. -/
theorem derPow_scalar (n : ℕ) (x : ((domSpace Hs ⊤).pow n)) :
    derPow Hs ⊤ (scalarOp Hs c) n x = ((n : ℂ) * c) • inclPow Hs ⊤ n x := by
  induction n with
  | zero => simp [derPow]
  | succ n ih =>
      have hx : x ∈ Submodule.span ℂ
          {t : ((⊤ : Submodule ℂ Hs.carrier) ⊗[ℂ] ((domSpace Hs ⊤).pow n).carrier) |
            ∃ (p : (⊤ : Submodule ℂ Hs.carrier)) (q : ((domSpace Hs ⊤).pow n)),
              p ⊗ₜ[ℂ] q = t} := by
        rw [TensorProduct.span_tmul_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, b, rfl⟩ := ht
          rw [derPow_tmul, inclPow_tmul, ih b, scalarOp_apply, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul,
            ← add_smul]
          have hcoef : (c : ℂ) + (n : ℂ) * c = ((n + 1 : ℕ) : ℂ) * c := by push_cast; ring
          rw [hcoef]
      | zero => simp
      | add s t _ _ hs ht => rw [map_add, map_add, hs, ht, smul_add]
      | smul r s _ hs => rw [map_smul, map_smul, hs, smul_comm]

/-! ## The sector domain is everything -/

/-- With the full domain `⊤`, the inclusion of tensor powers is surjective. -/
theorem inclPow_top_surjective (n : ℕ) : Function.Surjective (inclPow Hs ⊤ n) := by
  induction n with
  | zero => exact fun x => ⟨x, rfl⟩
  | succ n ih =>
      have h1 : Function.Surjective ((⊤ : Submodule ℂ Hs.carrier).subtype) :=
        fun x => ⟨⟨x, trivial⟩, rfl⟩
      exact TensorProduct.map_surjective h1 ih



/-- The sector derivation of a scalar operator, seen inside `H^{⊗n}`, is the scalar
`n · c`. -/
theorem sectorOp_scalar (n : ℕ) (x : sectorDom Hs ⊤ n) :
    sectorOp Hs ⊤ (scalarOp Hs c) n x = ((n : ℂ) * c) • (x : (Hs.pow n).carrier) := by
  obtain ⟨x₀, hx₀⟩ := x.2
  have hx : (x : (Hs.pow n).carrier) = inclPow Hs ⊤ n x₀ := hx₀.symm
  rw [sectorOp_apply Hs ⊤ _ n x x₀ hx, derPow_scalar, hx]

/-! ## The sector hypothesis, discharged -/







/-! ## The unconditional theorem -/



end

end BookProof.ScalarDGamma


