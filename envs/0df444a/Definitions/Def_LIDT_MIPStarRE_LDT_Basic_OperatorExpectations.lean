-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
-- name    : LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:49:58.459591+00:00
-- url     : https://prove2.me/theorems/eb96de9d-0c1e-4681-b5ce-41be7325a306
-- title:
--   LIDT definitions: LDT / Basic / OperatorExpectations
-- statement:
--   This bundle supplies linearity, positivity, tensor-sandwich, and quadratic identities for the real operator expectation `ev`.
--
--   Principal definitions:
--   - `ev_add`: expectation is additive on operator sums.
--   - `ev_sub`: expectation respects operator subtraction.
--   - `ev_scale`: expectation commutes with real scalar multiplication.
--   - `ev_one_of_isNormalized`: a normalized state has unit expectation on identity.
--   - `ev_adjoint_self_nonneg`: adjoint-square expectations are nonnegative.
--   - `normalizedTrace_diff_sq_nonneg`: a positive state gives a nonnegative quadratic for a difference.
--   - `ev_diff_triangle`: squared expectation distance obeys the two-step triangle bound.
--   - `ev_opTensor_sandwich_cauchy_schwarz`: supplies the tensor-sandwich Cauchy-Schwarz estimate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/OperatorExpectations.lean#L20-L581

-- Generated from MIPStarRE/LDT/Basic/OperatorExpectations.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open scoped _root_.Matrix

namespace LIDT

/-!
# Operator expectation infrastructure for the low individual degree test

Expectation-value and normalized-trace lemmas for quantum operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Bridging lemmas: expectation-value linearity -/

/-- `ev` distributes over addition. -/
theorem ev_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (X + Y) = ev ψ X + ev ψ Y := by
  simp [ev, mul_add,
    MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]

/-- `ev` distributes over subtraction. -/
theorem ev_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (X - Y) = ev ψ X - ev ψ Y := by
  simp [ev, mul_sub,
    MIPStarRE.Quantum.normalizedTrace_sub, Complex.sub_re]

/-! ### Algebraic lemmas for operator expectation values -/

/-- `ev` commutes with complex scalar multiplication by a real number. -/
theorem ev_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (c : Error) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ ((c : ℂ) • X) = c * ev ψ X := by
  simp only [ev]
  rw [show ψ.density * ((c : ℂ) • X) = (c : ℂ) • (ψ.density * X)
    from by rw [mul_smul_comm]]
  rw [MIPStarRE.Quantum.normalizedTrace_smul]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- `ev` commutes with the real scalar action on operators.

This is the real-scalar form of `ev_scale`; it is convenient when expanding
operator averages, whose weights act by the real scalar action before being
coerced to complex matrix scalars. -/
theorem ev_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (c : Error) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ (c • X) = c * ev ψ X := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simpa using ev_scale ψ c X

/-! ### Self-difference and zero-matrix infrastructure -/

/-- `ev` of the zero operator is zero. -/
theorem ev_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) : ev ψ (0 : MIPStarRE.Quantum.Op ι) = 0 := by
  simp [ev]



/-- A normalized state has unit expectation on the identity operator. -/
@[simp] theorem ev_one_of_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) :
    ev ψ (1 : MIPStarRE.Quantum.Op ι) = 1 := by
  have hψre := congrArg Complex.re hψ
  simpa [ev] using hψre

/-! ### PSD trace positivity -/

/-- For a PSD state `ψ` and any operator `M`, `E[Mᴴ M] ≥ 0`. -/
theorem ev_adjoint_self_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : MIPStarRE.Quantum.Op ι) :
    0 ≤ ev ψ (Mᴴ * M) := by
  simp only [ev]
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * Mᴴ) M,
        ← Matrix.mul_assoc]
    have hpos : 0 ≤ M * ψ.density * Mᴴ := by
      simpa [Matrix.star_eq_conjTranspose] using
        star_right_conjugate_nonneg ψ.density_psd M
    exact (Complex.nonneg_iff.mp
      (Matrix.nonneg_iff_posSemidef.mp hpos).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-! ### Parallelogram inequality for normalized trace -/

/-- PSD trace nonnegativity for difference quadratic:
`0 ≤ Re τ(ρ (D₁ - D₂)ᴴ(D₁ - D₂))` for PSD ρ. -/
theorem normalizedTrace_diff_sq_nonneg {n : Type*} [Fintype n]
    (ρ D₁ D₂ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ Complex.re
      (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂)))) := by
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (ρ * (D₁ - D₂)ᴴ) (D₁ - D₂),
        ← Matrix.mul_assoc]
    have hpos : 0 ≤ (D₁ - D₂) * ρ * (D₁ - D₂)ᴴ := by
      simpa [Matrix.star_eq_conjTranspose] using
        star_right_conjugate_nonneg hρ.nonneg (D₁ - D₂)
    exact (Complex.nonneg_iff.mp (Matrix.nonneg_iff_posSemidef.mp hpos).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-- Triangle inequality for normalized trace of PSD-weighted quadratic forms.

For PSD `ρ`, the real part of `τ(ρ (D₁ + D₂)ᴴ(D₁ + D₂))` is bounded by twice
the sum of the corresponding quadratic forms for `D₁` and `D₂`. -/
theorem normalizedTrace_triangle {n : Type*} [Fintype n]
    (ρ D₁ D₂ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂)))) ≤
      2 * (Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
           Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂)))) := by
  have h_para : (D₁ + D₂)ᴴ * (D₁ + D₂) + (D₁ - D₂)ᴴ * (D₁ - D₂) =
      (D₁ᴴ * D₁ + D₂ᴴ * D₂) + (D₁ᴴ * D₁ + D₂ᴴ * D₂) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      add_mul, mul_add, sub_mul, mul_sub]
    abel
  have h_trace_id :
      MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂))) +
      MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂))) =
      MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂)) +
      MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂)) := by
    rw [← MIPStarRE.Quantum.normalizedTrace_add, ← Matrix.mul_add, h_para,
        Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add]
  have h_re_id :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ + D₂)ᴴ * (D₁ + D₂)))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * ((D₁ - D₂)ᴴ * (D₁ - D₂)))) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) := by
    have := congr_arg Complex.re h_trace_id
    simp only [Complex.add_re] at this
    exact this
  have h_lin :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁ + D₂ᴴ * D₂))) =
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) := by
    rw [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, Complex.add_re]
  linarith [normalizedTrace_diff_sq_nonneg ρ D₁ D₂ hρ]

/-! ### Operator-level triangle inequality for squared differences -/

/-- Operator-level triangle inequality for expectation of squared differences:
`E[(X-Z)ᴴ(X-Z)] ≤ 2*(E[(X-Y)ᴴ(X-Y)] + E[(Y-Z)ᴴ(Y-Z)])`. -/
theorem ev_diff_triangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y Z : MIPStarRE.Quantum.Op ι) :
    ev ψ ((X - Z)ᴴ * (X - Z)) ≤
    2 * (ev ψ ((X - Y)ᴴ * (X - Y)) +
         ev ψ ((Y - Z)ᴴ * (Y - Z))) := by
  simp only [ev]
  have hdecomp : X - Z = (X - Y) + (Y - Z) := by abel
  rw [hdecomp]
  exact normalizedTrace_triangle ψ.density (X - Y) (Y - Z)
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd)

/-- Three-vector version of the normalized-trace triangle inequality.

If a difference is decomposed as three successive differences, its squared norm
is bounded by `3` times the sum of the three squared norms. This is the `k = 3`
case of the paper's `prop:triangle-inequality-for-vectors-squared`, and it is
used by the Step 6 projectivization chain in `inductive_step.tex:154--158`. -/
theorem normalizedTrace_triangle_three {n : Type*} [Fintype n]
    (ρ D₁ D₂ D₃ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    Complex.re (MIPStarRE.Quantum.normalizedTrace
        (ρ * (((D₁ + D₂ + D₃)ᴴ) * (D₁ + D₂ + D₃)))) ≤
      3 * (Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₃ᴴ * D₃)))) := by
  let S := ((D₁ + D₂ + D₃)ᴴ) * (D₁ + D₂ + D₃)
  let E12 := (D₁ - D₂)ᴴ * (D₁ - D₂)
  let E13 := (D₁ - D₃)ᴴ * (D₁ - D₃)
  let E23 := (D₂ - D₃)ᴴ * (D₂ - D₃)
  let Base := D₁ᴴ * D₁ + D₂ᴴ * D₂ + D₃ᴴ * D₃
  have h_para : S + (E12 + E13 + E23) = Base + Base + Base := by
    simp only [S, E12, E13, E23, Base, Matrix.conjTranspose_add,
      Matrix.conjTranspose_sub, add_mul, mul_add, sub_mul, mul_sub]
    abel
  have h_trace_id :
      MIPStarRE.Quantum.normalizedTrace (ρ * S) +
          (MIPStarRE.Quantum.normalizedTrace (ρ * E12) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E13) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E23)) =
        MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
          MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
          MIPStarRE.Quantum.normalizedTrace (ρ * Base) := by
    calc
      MIPStarRE.Quantum.normalizedTrace (ρ * S) +
          (MIPStarRE.Quantum.normalizedTrace (ρ * E12) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E13) +
            MIPStarRE.Quantum.normalizedTrace (ρ * E23))
          = MIPStarRE.Quantum.normalizedTrace
              (ρ * (S + (E12 + E13 + E23))) := by
              simp [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, add_assoc]
      _ = MIPStarRE.Quantum.normalizedTrace (ρ * (Base + Base + Base)) := by
              rw [h_para]
      _ = MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
            MIPStarRE.Quantum.normalizedTrace (ρ * Base) +
            MIPStarRE.Quantum.normalizedTrace (ρ * Base) := by
              simp [Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add, add_assoc]
  have h_re_id := congrArg Complex.re h_trace_id
  simp only [Complex.add_re] at h_re_id
  have h_base :
      Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * Base)) =
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₁ᴴ * D₁))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₂ᴴ * D₂))) +
        Complex.re (MIPStarRE.Quantum.normalizedTrace (ρ * (D₃ᴴ * D₃))) := by
    simp [Base, Matrix.mul_add, MIPStarRE.Quantum.normalizedTrace_add,
      Complex.add_re, add_assoc]
  have h12 := normalizedTrace_diff_sq_nonneg ρ D₁ D₂ hρ
  have h13 := normalizedTrace_diff_sq_nonneg ρ D₁ D₃ hρ
  have h23 := normalizedTrace_diff_sq_nonneg ρ D₂ D₃ hρ
  rw [h_base] at h_re_id
  linarith

/-- Three-step operator triangle inequality for squared differences. -/
theorem ev_diff_triangle_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y Z W : MIPStarRE.Quantum.Op ι) :
    ev ψ ((X - W)ᴴ * (X - W)) ≤
      3 * (ev ψ ((X - Y)ᴴ * (X - Y)) +
        ev ψ ((Y - Z)ᴴ * (Y - Z)) +
        ev ψ ((Z - W)ᴴ * (Z - W))) := by
  simp only [ev]
  have hdecomp : X - W = (X - Y) + (Y - Z) + (Z - W) := by abel
  rw [hdecomp]
  exact normalizedTrace_triangle_three ψ.density (X - Y) (Y - Z) (Z - W)
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd)

/-! ### Infrastructure for bridge lemma proofs -/

/-- `ev` distributes over finite sums. -/
theorem ev_finset_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} (ψ : QuantumState ι) (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ι) :
    ev ψ (∑ a ∈ s, f a) = ∑ a ∈ s, ev ψ (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero]
  | @insert a s hna ih =>
    rw [Finset.sum_insert hna, Finset.sum_insert hna, ev_add, ih]

/-- `ev` distributes over univ sums. -/
theorem ev_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] (ψ : QuantumState ι)
    (f : α → MIPStarRE.Quantum.Op ι) :
    ev ψ (∑ a, f a) = ∑ a, ev ψ (f a) :=
  ev_finset_sum ψ Finset.univ f

/-- Evaluation of an operator average is the average of the evaluations. -/
theorem ev_averageOperatorOverDistribution {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution α)
    (A : α → MIPStarRE.Quantum.Op ι) :
    ev ψ (averageOperatorOverDistribution 𝒟 A) =
      avgOver 𝒟 (fun a => ev ψ (A a)) := by
  unfold averageOperatorOverDistribution avgOver
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_real_smul ψ (𝒟.weight a) (A a)

/-- `ev` of a PSD operator is nonneg. -/
theorem ev_nonneg_of_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) (hX : 0 ≤ X) :
    0 ≤ ev ψ X := by
  simp only [ev]
  unfold MIPStarRE.Quantum.normalizedTrace
  classical
  simp only [Complex.div_natCast_re]
  apply div_nonneg
  · -- Factor X = star S * S via C*-algebra PSD factorization
    obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
    rw [hS, Matrix.star_eq_conjTranspose,
        ← Matrix.mul_assoc, Matrix.trace_mul_comm (ψ.density * Sᴴ) S,
        ← Matrix.mul_assoc]
    have hpos : 0 ≤ S * ψ.density * Sᴴ := by
      simpa [Matrix.star_eq_conjTranspose] using
        star_right_conjugate_nonneg ψ.density_psd S
    exact (Complex.nonneg_iff.mp (Matrix.nonneg_iff_posSemidef.mp hpos).trace_nonneg).1
  · exact Nat.cast_nonneg _

/-- `ev` is monotone under the matrix order. -/
theorem ev_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X Y : MIPStarRE.Quantum.Op ι) (h : X ≤ Y) :
    ev ψ X ≤ ev ψ Y := by
  have hsub : ev ψ Y - ev ψ X = ev ψ (Y - X) := (ev_sub ψ Y X).symm
  linarith [ev_nonneg_of_psd ψ (Y - X) (sub_nonneg.mpr h)]

/-- For Hermitian ρ, A, B: `ev ψ (A * B) = ev ψ (B * A)`.
Follows from `ntr(ρ B A) = conj(ntr(ρ A B))` when all three are Hermitian,
and Re is invariant under conjugation. -/
theorem normalizedTrace_conjTranspose {d : Type*} [Fintype d]
    (X : MIPStarRE.Quantum.Op d) :
    MIPStarRE.Quantum.normalizedTrace Xᴴ = star (MIPStarRE.Quantum.normalizedTrace X) := by
  simp only [MIPStarRE.Quantum.normalizedTrace, Matrix.trace_conjTranspose]
  rw [star_div₀, star_natCast]

/-- Taking the adjoint does not change `ev`. -/
theorem ev_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ Xᴴ = ev ψ X := by
  unfold ev
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  have hstar :
      star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) =
        MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ) := by
    rw [← normalizedTrace_conjTranspose]
    rw [Matrix.conjTranspose_mul, hρ]
    exact MIPStarRE.Quantum.normalizedTrace_mul_comm Xᴴ ψ.density
  simpa [Complex.star_def, Complex.conj_re] using congrArg Complex.re hstar.symm

theorem ev_mul_comm_of_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι)
    (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ev ψ (A * B) = ev ψ (B * A) := by
  simp only [ev]
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  -- key: star(ntr(ρ(AB))) = ntr((ρAB)ᴴ) = ntr(BᴴAᴴρᴴ) = ntr(BAρ) = ntr(ρ(BA))
  have key : star (MIPStarRE.Quantum.normalizedTrace (ψ.density * (A * B))) =
      MIPStarRE.Quantum.normalizedTrace (ψ.density * (B * A)) := by
    rw [← normalizedTrace_conjTranspose]
    -- (ρ(AB))ᴴ = (AB)ᴴρᴴ = BᴴAᴴρᴴ = BAρ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB, hρ]
    -- goal: ntr((B * A) * ρ) = ntr(ρ * (B * A))
    rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  simpa [Complex.star_def, Complex.conj_re] using congr_arg Complex.re key

/-- `ev` commutes on PSD operators (convenience wrapper). -/
theorem ev_mul_comm_of_psd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ev ψ (A * B) = ev ψ (B * A) :=
  ev_mul_comm_of_hermitian ψ A B
    (Matrix.nonneg_iff_posSemidef.mp hA).isHermitian.eq
    (Matrix.nonneg_iff_posSemidef.mp hB).isHermitian.eq

/-- Cross-term identity: `ev ψ (Bᴴ * A) = ev ψ (Aᴴ * B)`. -/
theorem ev_conjTranspose_mul_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    ev ψ (Bᴴ * A) = ev ψ (Aᴴ * B) := by
  simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    using (ev_conjTranspose ψ (Aᴴ * B))

/-- Cauchy-Schwarz for the state-weighted inner product:
`(ev ψ (Aᴴ * B))² ≤ ev ψ (Aᴴ * A) * ev ψ (Bᴴ * B)`. -/
theorem ev_cauchy_schwarz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    (ev ψ (Aᴴ * B)) ^ 2 ≤ ev ψ (Aᴴ * A) * ev ψ (Bᴴ * B) := by
  have hcross : ev ψ (Bᴴ * A) = ev ψ (Aᴴ * B) := ev_conjTranspose_mul_comm ψ A B
  -- Scalar expansion helpers
  have hscale_r : ∀ (t : ℝ) (X : MIPStarRE.Quantum.Op ι),
      ev ψ (((↑t : ℂ) • Bᴴ) * X) = t * ev ψ (Bᴴ * X) := by
    intro t X
    rw [show ((↑t : ℂ) • Bᴴ) * X = (↑t : ℂ) • (Bᴴ * X) from smul_mul_assoc _ _ _]
    exact ev_scale ψ t (Bᴴ * X)
  have hscale_l : ∀ (t : ℝ) (X : MIPStarRE.Quantum.Op ι),
      ev ψ (X * ((↑t : ℂ) • B)) = t * ev ψ (X * B) := by
    intro t X
    rw [show X * ((↑t : ℂ) • B) = (↑t : ℂ) • (X * B) from mul_smul_comm _ _ _]
    exact ev_scale ψ t (X * B)
  -- Quadratic: for all t, ev((A + tB)ᴴ(A + tB)) ≥ 0 expands to a quadratic
  have hquad : ∀ t : ℝ, 0 ≤ ev ψ (Bᴴ * B) * (t * t) +
      (2 * ev ψ (Aᴴ * B)) * t + ev ψ (Aᴴ * A) := by
    intro t
    have expand : ev ψ ((A + (↑t : ℂ) • B)ᴴ * (A + (↑t : ℂ) • B)) =
        ev ψ (Aᴴ * A) + t * ev ψ (Aᴴ * B) + (t * ev ψ (Bᴴ * A) +
        t * (t * ev ψ (Bᴴ * B))) := by
      have hstar_t : star (↑t : ℂ) = (↑t : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hstar_t]
      rw [add_mul, mul_add, mul_add]
      rw [ev_add, ev_add, ev_add]
      rw [hscale_l t Aᴴ, hscale_r t A]
      rw [show
          (↑t : ℂ) • Bᴴ * ((↑t : ℂ) • B) =
            (↑t : ℂ) • ((↑t : ℂ) • (Bᴴ * B))
        from by rw [smul_mul_assoc, mul_smul_comm]]
      rw [ev_scale, ev_scale]
    rw [show ev ψ (Bᴴ * B) * (t * t) + (2 * ev ψ (Aᴴ * B)) * t + ev ψ (Aᴴ * A) =
        ev ψ (Aᴴ * A) + t * ev ψ (Aᴴ * B) + (t * ev ψ (Bᴴ * A) +
        t * (t * ev ψ (Bᴴ * B))) by rw [hcross]; ring]
    rw [← expand]
    exact ev_adjoint_self_nonneg ψ (A + (↑t : ℂ) • B)
  -- Apply quadratic discriminant
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  nlinarith

/-- Absolute-value form of Cauchy-Schwarz for `ev`. -/
theorem ev_abs_mul_le_sqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    |ev ψ (A * B)| ≤
      Real.sqrt (ev ψ (A * Aᴴ)) * Real.sqrt (ev ψ (Bᴴ * B)) := by
  have hsq :
      (ev ψ (A * B)) ^ 2 ≤ ev ψ (A * Aᴴ) * ev ψ (Bᴴ * B) := by
    simpa using ev_cauchy_schwarz ψ Aᴴ B
  have hA_nonneg : 0 ≤ ev ψ (A * Aᴴ) := by
    simpa using ev_adjoint_self_nonneg ψ Aᴴ
  have hB_nonneg : 0 ≤ ev ψ (Bᴴ * B) := ev_adjoint_self_nonneg ψ B
  refine abs_le_of_sq_le_sq' ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.2
  calc
    |ev ψ (A * B)| ^ 2 = (ev ψ (A * B)) ^ 2 := by rw [sq_abs]
    _ ≤ ev ψ (A * Aᴴ) * ev ψ (Bᴴ * B) := hsq
    _ = (Real.sqrt (ev ψ (A * Aᴴ)) * Real.sqrt (ev ψ (Bᴴ * B))) ^ 2 := by
          rw [sq]
          ring_nf
          rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]

/-- AM-GM for the quadratic form:
`2 * ev ψ (Aᴴ * B) ≤ ev ψ (Aᴴ * A) + ev ψ (Bᴴ * B)`. -/
theorem ev_cross_term_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    2 * ev ψ (Aᴴ * B) ≤ ev ψ (Aᴴ * A) + ev ψ (Bᴴ * B) := by
  have h := ev_adjoint_self_nonneg ψ (A - B)
  rw [Matrix.conjTranspose_sub] at h
  have hexp : ev ψ ((Aᴴ - Bᴴ) * (A - B)) =
      ev ψ (Aᴴ * A) - ev ψ (Aᴴ * B) -
        ev ψ (Bᴴ * A) + ev ψ (Bᴴ * B) := by
    rw [sub_mul, mul_sub, mul_sub, ev_sub, ev_sub, ev_sub]
    ring
  rw [hexp] at h
  linarith [ev_conjTranspose_mul_comm ψ A B]

/-- Jensen inequality for the quadratic form: for a finite family of operators,
`ev ψ ((∑ Xᵢ)ᴴ * (∑ Xᵢ)) ≤ n * ∑ ev ψ (XᵢᴴXᵢ)`. -/
theorem ev_sum_conjTranspose_mul_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) {α : Type*} [Fintype α]
    (X : α → MIPStarRE.Quantum.Op ι) :
    ev ψ ((∑ a, X a)ᴴ * (∑ a, X a)) ≤
      (Fintype.card α : ℝ) * ∑ a, ev ψ ((X a)ᴴ * X a) := by
  -- Expand LHS to double sum: ev((∑Xi)ᴴ(∑Xi)) = ∑_i ∑_j ev(XiᴴXj)
  have hexpand : ev ψ ((∑ a, X a)ᴴ * (∑ a, X a)) =
      ∑ i : α, ∑ j : α, ev ψ ((X i)ᴴ * X j) := by
    rw [Matrix.conjTranspose_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum, ev_finset_sum]
  rw [hexpand]
  -- Apply cross-term bound to each pair, then simplify double sum
  calc ∑ i : α, ∑ j : α, ev ψ ((X i)ᴴ * X j)
      ≤ ∑ i : α, ∑ j : α,
          (ev ψ ((X i)ᴴ * X i) + ev ψ ((X j)ᴴ * X j)) / 2 :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => by
            linarith [ev_cross_term_le ψ (X i) (X j)]
    _ = (Fintype.card α : ℝ) * ∑ a, ev ψ ((X a)ᴴ * X a) :=
        by
          let f : α → ℝ := fun a => ev ψ ((X a)ᴴ * X a)
          change ∑ i : α, ∑ j : α, (f i + f j) / 2 =
            (Fintype.card α : ℝ) * ∑ a : α, f a
          have inner : ∀ i, ∑ j : α, (f i + f j) / 2 =
              (Fintype.card α : ℝ) * (f i / 2) + (∑ j : α, f j) / 2 := by
            intro i
            simp_rw [add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul, Finset.sum_div]
          simp_rw [inner]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          simp_rw [show ∀ x, (Fintype.card α : ℝ) * (f x / 2) =
            (Fintype.card α : ℝ) / 2 * f x from fun _ => by ring]
          rw [← Finset.mul_sum]
          ring

/-! ### Bipartite-tensor sandwich Cauchy–Schwarz

The lemmas below give the operator/real Cauchy–Schwarz step for expectations of
sandwiched products lifted to a bipartite tensor space. They are a reusable
primitive toward the raw `Q₂ → Q₃` and `Q₃ → Q₄` Cauchy–Schwarz estimates of
`self_improvement.tex`, lines 306–311 and 326–332 (the
`eq:change-one-cauchy-schwarz` and `eq:change-another` displays), where the
bilinear form is `⟨X, Y⟩_{M, T} := ev ψ (opTensor (Xᴴ · M · Y) T)` with PSD
`M`, `T`. -/

/-- Bipartite-tensor Cauchy–Schwarz for state expectations.

For PSD operators `M`, `T` and arbitrary operators `X`, `Y`,
`(ev ψ (opTensor (Xᴴ M Y) T))² ≤ ev ψ (opTensor (Xᴴ M X) T) *
ev ψ (opTensor (Yᴴ M Y) T)`.

The proof factors `M = √M · √M`, `T = √T · √T` (continuous functional calculus
square roots) and applies `ev_cauchy_schwarz` to
`opTensor (√M · X) √T` and `opTensor (√M · Y) √T`. -/
theorem ev_opTensor_sandwich_cauchy_schwarz
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (X Y M : MIPStarRE.Quantum.Op ι₁)
    (T : MIPStarRE.Quantum.Op ι₂)
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    (ev ψ (opTensor (Xᴴ * M * Y) T)) ^ 2 ≤
      ev ψ (opTensor (Xᴴ * M * X) T) * ev ψ (opTensor (Yᴴ * M * Y) T) := by
  classical
  have hsM_self : CFC.sqrt M * CFC.sqrt M = M := CFC.sqrt_mul_sqrt_self M hM
  have hsT_self : CFC.sqrt T * CFC.sqrt T = T := CFC.sqrt_mul_sqrt_self T hT
  have hsM_herm : (CFC.sqrt M)ᴴ = CFC.sqrt M :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian.eq
  have hsT_herm : (CFC.sqrt T)ᴴ = CFC.sqrt T :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)).isHermitian.eq
  set A : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
    opTensor (CFC.sqrt M * X) (CFC.sqrt T) with hA_def
  set B : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
    opTensor (CFC.sqrt M * Y) (CFC.sqrt T) with hB_def
  have hA_adj : Aᴴ = opTensor (Xᴴ * CFC.sqrt M) (CFC.sqrt T) := by
    rw [hA_def, conjTranspose_opTensor, Matrix.conjTranspose_mul, hsM_herm, hsT_herm]
  have hB_adj : Bᴴ = opTensor (Yᴴ * CFC.sqrt M) (CFC.sqrt T) := by
    rw [hB_def, conjTranspose_opTensor, Matrix.conjTranspose_mul, hsM_herm, hsT_herm]
  have hAB : Aᴴ * B = opTensor (Xᴴ * M * Y) T := by
    rw [hA_adj, hB_def, opTensor_mul]
    congr 1
    · calc Xᴴ * CFC.sqrt M * (CFC.sqrt M * Y)
          = Xᴴ * (CFC.sqrt M * CFC.sqrt M) * Y := by noncomm_ring
        _ = Xᴴ * M * Y := by rw [hsM_self]
  have hAA : Aᴴ * A = opTensor (Xᴴ * M * X) T := by
    rw [hA_adj, hA_def, opTensor_mul]
    congr 1
    · calc Xᴴ * CFC.sqrt M * (CFC.sqrt M * X)
          = Xᴴ * (CFC.sqrt M * CFC.sqrt M) * X := by noncomm_ring
        _ = Xᴴ * M * X := by rw [hsM_self]
  have hBB : Bᴴ * B = opTensor (Yᴴ * M * Y) T := by
    rw [hB_adj, hB_def, opTensor_mul]
    congr 1
    · calc Yᴴ * CFC.sqrt M * (CFC.sqrt M * Y)
          = Yᴴ * (CFC.sqrt M * CFC.sqrt M) * Y := by noncomm_ring
        _ = Yᴴ * M * Y := by rw [hsM_self]
  have hcs := ev_cauchy_schwarz ψ A B
  rw [hAB, hAA, hBB] at hcs
  exact hcs

/-- Diagonal sandwich expectation `ev ψ (opTensor (Xᴴ M X) T)` is nonneg
when `M`, `T` are PSD. -/
private theorem ev_opTensor_sandwich_diag_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (X M : MIPStarRE.Quantum.Op ι₁)
    (T : MIPStarRE.Quantum.Op ι₂)
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 ≤ ev ψ (opTensor (Xᴴ * M * X) T) :=
  ev_nonneg_of_psd ψ _
    (opTensor_nonneg
      (by
        simpa [Matrix.star_eq_conjTranspose] using
          star_left_conjugate_nonneg hM X)
      hT)

/-- Absolute-value form of the bipartite-tensor sandwich Cauchy–Schwarz. -/
theorem ev_opTensor_sandwich_abs_le_sqrt
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState (ι₁ × ι₂))
    (X Y M : MIPStarRE.Quantum.Op ι₁)
    (T : MIPStarRE.Quantum.Op ι₂)
    (hM : 0 ≤ M) (hT : 0 ≤ T) :
    |ev ψ (opTensor (Xᴴ * M * Y) T)| ≤
      Real.sqrt (ev ψ (opTensor (Xᴴ * M * X) T)) *
        Real.sqrt (ev ψ (opTensor (Yᴴ * M * Y) T)) := by
  have hsq := ev_opTensor_sandwich_cauchy_schwarz ψ X Y M T hM hT
  have hX_nonneg := ev_opTensor_sandwich_diag_nonneg ψ X M T hM hT
  have hY_nonneg := ev_opTensor_sandwich_diag_nonneg ψ Y M T hM hT
  refine abs_le_of_sq_le_sq' ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.2
  calc
    |ev ψ (opTensor (Xᴴ * M * Y) T)| ^ 2
        = (ev ψ (opTensor (Xᴴ * M * Y) T)) ^ 2 := by rw [sq_abs]
    _ ≤ ev ψ (opTensor (Xᴴ * M * X) T) * ev ψ (opTensor (Yᴴ * M * Y) T) := hsq
    _ = (Real.sqrt (ev ψ (opTensor (Xᴴ * M * X) T)) *
            Real.sqrt (ev ψ (opTensor (Yᴴ * M * Y) T))) ^ 2 := by
          rw [sq]
          ring_nf
          rw [Real.sq_sqrt hX_nonneg, Real.sq_sqrt hY_nonneg]

end MIPStarRE.LDT

end

end LIDT


