-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
-- name    : GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:30.769625+00:00
-- url     : https://prove2.me/theorems/3a7958cc-3142-4da8-97e7-84df18c6ff4e
-- title:
--   Second Kind Statements
-- statement:
--   Definitions and structural lemmas for Second Kind Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LieCoordinates/SecondKindStatements.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace SecondKind
abbrev MatProd {f : ℕ} (p q : Fin f → ℕ) : Type :=
  (τ : Fin f) → Matrix (Fin (p τ) ⊕ Fin (q τ)) (Fin (p τ) ⊕ Fin (q τ)) ℂ
def lieProd {f : ℕ} (p q : Fin f → ℕ) : Submodule ℝ (MatProd p q) :=
  Submodule.pi Set.univ fun τ => indefiniteUnitaryLieAlgebra (p τ) (q τ)
def hsInner {f : ℕ} {p q : Fin f → ℕ} (X X' : MatProd p q) : ℝ :=
  ∑ τ, (trace (X τ * (X' τ)ᴴ)).re
structure OrthoFrame where

  f : ℕ

  r : ℕ
  f_pos : 1 ≤ f
  r_pos : 1 ≤ r

  p : Fin f → ℕ

  q : Fin f → ℕ
  sig : ∀ τ, p τ + q τ = r

  place : Fin (f * r ^ 2) → Fin f

  E : Fin (f * r ^ 2) → MatProd p q
  span : Submodule.span ℝ (Set.range E) = lieProd p q
  orthonormal : ∀ k l, hsInner (E k) (E l) = if k = l then 1 else 0
  supp : ∀ l τ, τ ≠ place l → E l τ = 0
namespace OrthoFrame
variable (F : OrthoFrame)
abbrev dim : ℕ := F.f * F.r ^ 2
def side (n : ℕ) : ℝ := 1 / (16 * (n : ℝ) ^ 3)
def cube (n : ℕ) : Set (Fin F.dim → ℝ) :=
  Set.univ.pi fun _ => Set.Icc 0 (side n)
def coordMap (y : Fin F.dim → ℝ) : MatProd F.p F.q := fun τ =>
  ((List.ofFn fun l : Fin F.dim => NormedSpace.exp (y l • F.E l τ)).reverse).prod
def io (v : Fin F.dim → ℝ) : MatProd F.p F.q := ∑ l, v l • F.E l
def dCoord (y v : Fin F.dim → ℝ) : MatProd F.p F.q :=
  fun τ i j => fderiv ℝ (fun z : Fin F.dim → ℝ => F.coordMap z τ i j) y v
def logDeriv (y v : Fin F.dim → ℝ) : MatProd F.p F.q :=
  fun τ => (F.coordMap y τ)⁻¹ * F.dCoord y v τ
def jac (y : Fin F.dim → ℝ) : Matrix (Fin F.dim) (Fin F.dim) ℝ :=
  fun k l => hsInner (F.E k) (F.logDeriv y (Pi.single l 1))
end OrthoFrame
def IoIsometry.Statement : Prop :=
  ∀ F : OrthoFrame, ∀ v w : Fin F.dim → ℝ, hsInner (F.io v) (F.io w) = ∑ l, v l * w l
def Factors.Statement : Prop :=
  ∀ F : OrthoFrame,
    (∀ k l, F.place k ≠ F.place l → ∀ s t : ℝ,
      NormedSpace.exp (s • F.E k) * NormedSpace.exp (t • F.E l) =
        NormedSpace.exp (t • F.E l) * NormedSpace.exp (s • F.E k)) ∧
    ∀ τ, Fintype.card {l // F.place l = τ} = F.r ^ 2
def JacobianBound.Statement : Prop :=
  ∀ F : OrthoFrame, ∀ n : ℕ, max F.r 2 ≤ n → ∀ y ∈ F.cube n,
    (∀ v : Fin F.dim → ℝ, F.logDeriv y v = F.io (F.jac y *ᵥ v)) ∧
    (∀ k l, F.place k ≠ F.place l → F.jac y k l = 0) ∧
    (∀ i < F.dim, 3 / 4 ≤ (toEuclideanLin (F.jac y)).singularValues i ∧
      (toEuclideanLin (F.jac y)).singularValues i ≤ 5 / 4) ∧
    (3 / 4 : ℝ) ^ F.dim ≤ |(F.jac y).det| ∧ |(F.jac y).det| ≤ (5 / 4 : ℝ) ^ F.dim
def CoordInjective.Statement : Prop :=
  ∀ F : OrthoFrame, ∀ n : ℕ, max F.r 2 ≤ n → Set.InjOn F.coordMap (F.cube n)
def CoordNormBound.Statement : Prop :=
  ∀ F : OrthoFrame, ∀ n : ℕ, max F.r 2 ≤ n → ∀ y ∈ F.cube n, ∀ τ : Fin F.f,
    ‖F.coordMap y τ‖ ≤ Real.exp (OrthoFrame.side n * (F.r : ℝ) ^ 2) ∧
    ‖(F.coordMap y τ)⁻¹‖ ≤ Real.exp (OrthoFrame.side n * (F.r : ℝ) ^ 2) ∧
    Real.exp (OrthoFrame.side n * (F.r : ℝ) ^ 2) ≤ Real.exp (1 / 16)
def Statement : Prop :=
  JacobianBound.Statement ∧ CoordInjective.Statement ∧ CoordNormBound.Statement
def m2 (a b c d : ℂ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  Matrix.of fun i j => match i, j with
    | .inl _, .inl _ => a
    | .inl _, .inr _ => b
    | .inr _, .inl _ => c
    | .inr _, .inr _ => d
@[simp] theorem block_entry_inl_inl (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inl i) (.inl j) = a := rfl
@[simp] theorem block_entry_inl_inr (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inl i) (.inr j) = b := rfl
@[simp] theorem block_entry_inr_inl (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inr i) (.inl j) = c := rfl
@[simp] theorem block_entry_inr_inr (a b c d : ℂ) (i j : Fin 1) : m2 a b c d (.inr i) (.inr j) = d := rfl
theorem mem_unitaryOneOne_iff (X : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) :
    X ∈ indefiniteUnitaryLieAlgebra 1 1 ↔
      starRingEnd ℂ (X (.inl 0) (.inl 0)) + X (.inl 0) (.inl 0) = 0 ∧
      X (.inl 0) (.inr 0) = starRingEnd ℂ (X (.inr 0) (.inl 0)) ∧
      starRingEnd ℂ (X (.inr 0) (.inr 0)) + X (.inr 0) (.inr 0) = 0 := by
  show Xᴴ * indefJ 1 1 + indefJ 1 1 * X = 0 ↔ _
  constructor
  · intro h
    have e1 := congrFun (congrFun h (.inl 0)) (.inl 0)
    have e2 := congrFun (congrFun h (.inl 0)) (.inr 0)
    have e3 := congrFun (congrFun h (.inr 0)) (.inr 0)
    simp [indefJ, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply] at e1 e2 e3
    refine ⟨e1, ?_, ?_⟩
    · linear_combination e2
    · linear_combination -e3
  · rintro ⟨h1, h2, h3⟩
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j] <;>
      simp [indefJ, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply]
    · exact h1
    · linear_combination h2
    · rw [h2, Complex.conj_conj]; ring
    · linear_combination -h3
theorem block_mem_unitaryOneOne (a b c d : ℂ) (ha : starRingEnd ℂ a + a = 0) (hb : b = starRingEnd ℂ c)
    (hd : starRingEnd ℂ d + d = 0) :
    m2 a b c d ∈ indefiniteUnitaryLieAlgebra 1 1 :=
  (mem_unitaryOneOne_iff _).2 ⟨ha, hb, hd⟩
theorem trace_block_mul_conjTranspose (a b c d a' b' c' d' : ℂ) :
    trace (m2 a b c d * (m2 a' b' c' d')ᴴ) =
      a * star a' + b * star b' + c * star c' + d * star d' := by
  simp [trace, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply]
  ring
def s2 : ℝ := (Real.sqrt 2)⁻¹
theorem inv_sqrt_two_mul_self : s2 * s2 = 1 / 2 := by
  rw [s2, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]
theorem sqrt_two_mul_inv_sqrt_two : Real.sqrt 2 * s2 = 1 :=
  mul_inv_cancel₀ (by positivity)
def unitaryOneOneBasis : Fin 4 → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  ![m2 Complex.I 0 0 0, m2 0 0 0 Complex.I, m2 0 (s2 : ℂ) (s2 : ℂ) 0,
    m2 0 (Complex.I * s2) (-(Complex.I * s2)) 0]
def unitaryOneOneFrame : OrthoFrame where
  f := 1
  r := 2
  f_pos := le_rfl
  r_pos := by norm_num
  p := fun _ => 1
  q := fun _ => 1
  sig := fun _ => rfl
  place := fun _ => 0
  E := fun l _ => unitaryOneOneBasis l
  span := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, lieProd, Submodule.mem_pi]
      intro τ _
      fin_cases l <;> simp only [unitaryOneOneBasis] <;> apply block_mem_unitaryOneOne <;>
        simp [Complex.conj_ofReal]
    · intro X hX
      rw [lieProd, Submodule.mem_pi] at hX
      have h0 := (mem_unitaryOneOne_iff _).1 (hX 0 (Set.mem_univ _))
      obtain ⟨h1, h2, h3⟩ := h0
      have hX' : X = (X 0 (.inl 0) (.inl 0)).im • (fun _ => unitaryOneOneBasis 0) +
          (X 0 (.inr 0) (.inr 0)).im • (fun _ => unitaryOneOneBasis 1) +
          (Real.sqrt 2 * (X 0 (.inl 0) (.inr 0)).re) • (fun _ => unitaryOneOneBasis 2) +
          (Real.sqrt 2 * (X 0 (.inl 0) (.inr 0)).im) • (fun _ => unitaryOneOneBasis 3) := by
        have k1 : (X 0 (.inl 0) (.inl 0)).re = 0 := by
          have := congrArg Complex.re h1; simp at this; linarith
        have k3 : (X 0 (.inr 0) (.inr 0)).re = 0 := by
          have := congrArg Complex.re h3; simp at this; linarith
        have k2r : (X 0 (.inr 0) (.inl 0)).re = (X 0 (.inl 0) (.inr 0)).re := by
          have := congrArg Complex.re h2; simp at this; linarith
        have k2i : (X 0 (.inr 0) (.inl 0)).im = -(X 0 (.inl 0) (.inr 0)).im := by
          have := congrArg Complex.im h2; simp at this; linarith
        have hs' : ∀ x : ℝ, Real.sqrt 2 * x * s2 = x := fun x => by
          rw [mul_right_comm, sqrt_two_mul_inv_sqrt_two, one_mul]
        funext τ
        rw [Fin.fin_one_eq_zero τ]
        ext i j
        rcases i with i | i <;> rcases j with j | j <;>
          simp only [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j] <;>
          apply Complex.ext <;>
          simp [unitaryOneOneBasis, k1, k3, k2r, k2i, hs']
      rw [hX']
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
        apply Submodule.smul_mem <;> apply Submodule.subset_span
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  orthonormal := by
    intro k l
    simp only [hsInner, Fin.sum_univ_one]
    fin_cases k <;> fin_cases l <;>
      simp [unitaryOneOneBasis, trace_block_mul_conjTranspose, Complex.conj_ofReal] <;>
      rw [inv_sqrt_two_mul_self] <;> norm_num
  supp := fun _ τ h => absurd (Fin.fin_one_eq_zero τ) h
end SecondKind
end
end GroundTheory.Heights₂.Theta


