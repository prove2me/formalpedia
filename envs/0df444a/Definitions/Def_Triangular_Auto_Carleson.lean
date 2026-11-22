-- Prove2me | Definitions.Def_Triangular_Auto_Carleson
-- name    : Triangular_Auto_Carleson
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T18:24:30.769337+00:00
-- url     : https://prove2.me/theorems/a3a75deb-44a9-4b82-bb17-e277a7f89a98
-- title:
--   Carleson
-- statement:
--   Definitions and structural lemmas for Carleson, from Joris Roos's pinned The triangular Hilbert transform and Carleson’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/Carleson.lean

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
section Weight
def carlesonBump₀ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
def carlesonBump₁ : ContDiffBump (0 : ℝ) := ⟨8, 9, by norm_num, by norm_num⟩
def carlesonW (t u : ℝ) : ℝ :=
  carlesonBump₀ u * carlesonBump₁ (2 * u - t) * carlesonBump₁ (t - u)
def carlesonWeight (t : ℝ) : ℝ := ∫ u, carlesonW t u
def carlesonMass : ℝ := ∫ u, carlesonBump₀ u
end Weight
section Specialization
open Complex in
/-- First triangular input `a(x) e^{iσν(x)(x+y)} ρ₀(y + x/2)`. -/
def carlesonF₀ (a ν : ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ) : ℂ :=
  (a p.1 : ℂ) * exp ((σ * ν p.1 * (p.1 + p.2) : ℝ) * I) * (carlesonBump₀ (p.2 + p.1 / 2) : ℂ)
def carlesonF₁ (g : ℝ → ℂ) (p : ℝ × ℝ) : ℂ := g (-p.1 - p.2) * (carlesonBump₁ (p.1 - p.2) : ℂ)
open Complex in
/-- Third triangular input `a(x) e^{iσν(x)z} ρ₁(z + x/2)`, in the variables `(z, x)`. -/
def carlesonF₂ (a ν : ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ) : ℂ :=
  (a p.2 : ℂ) * exp ((σ * ν p.2 * p.1 : ℝ) * I) * (carlesonBump₁ (p.1 + p.2 / 2) : ℂ)
def carlesonBox (L : ℝ) : Set (ℝ × ℝ) := Icc (-(L + 9)) (L + 9) ×ˢ Icc (-(L + 9)) (L + 9)
def carlesonCoord : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun q := ((q.1.1, q.2 - q.1.1 / 2), q.1.2 - q.2 - q.1.1 / 2)
  invFun q := ((q.1.1, q.1.1 + q.1.2 + q.2), q.1.2 + q.1.1 / 2)
  left_inv q := by ext <;> simp; ring
  right_inv q := by ext <;> simp; ring
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
open Complex in
/-- The hard truncation in the coordinates `(x, t)`. -/
def carlesonH (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) (p : ℝ × ℝ) : ℂ :=
  if ε < |p.2| then
    (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) * exp ((σ * ν p.1 * p.2 : ℝ) * I) / (p.2 : ℂ)
  else 0
def carlesonTrunc (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  if ε < |q.1.1 + q.1.2 + q.2| then
    carlesonF₀ a ν σ q.1 * carlesonF₁ g (q.1.2, q.2) * carlesonF₂ a ν σ (q.2, q.1.1) /
      ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ) else 0
def carlesonForm (a ν : ℝ → ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
    ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ)
end Specialization
section Norms
end Norms
section Mollify
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def carlesonMollifier (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (k + 2), 2 / (k + 2), by positivity, by gcongr; norm_num⟩
def carlesonMoll (k : ℕ) (h : ℝ → E) : ℝ → E :=
  (carlesonMollifier k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h
end Mollify
section Rough
end Rough
section Fourier
open Real
def fourierCoeffOne (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f t * Complex.exp (-(2 * π * Complex.I * n * t))
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeffOne f n * Complex.exp (2 * π * Complex.I * n * x)
def dirichletKernel (N : ℕ) (s : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (2 * π * Complex.I * n * s)
lemma fourierPartialSum_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (N : ℕ)
    (x : ℝ) : fourierPartialSum (fun t => f t + g t) N x =
      fourierPartialSum f N x + fourierPartialSum g N x := by
  unfold fourierPartialSum fourierCoeffOne
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← add_mul, ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [add_mul]
lemma fourierPartialSum_smul (c : ℂ) (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    fourierPartialSum (fun t => c * f t) N x = c * fourierPartialSum f N x := by
  unfold fourierPartialSum fourierCoeffOne
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  ring
instance carleson_fact_one_pos : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
def trigSubmodule : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) where
  carrier := {F | ∃ K : ℕ, ∀ N ≥ K, ∀ x : ℝ,
    fourierPartialSum (fun t => F (t : AddCircle (1 : ℝ))) N x = F x}
  zero_mem' := ⟨0, fun N _ x => by simp [fourierPartialSum, fourierCoeffOne]⟩
  add_mem' := by
    rintro F G ⟨K₁, h₁⟩ ⟨K₂, h₂⟩
    refine ⟨max K₁ K₂, fun N hN x => ?_⟩
    have hF : Continuous fun t : ℝ => F t := F.continuous.comp continuous_quotient_mk'
    have hG : Continuous fun t : ℝ => G t := G.continuous.comp continuous_quotient_mk'
    simp only [ContinuousMap.add_apply]
    rw [fourierPartialSum_add hF hG, h₁ N (le_of_max_le_left hN), h₂ N (le_of_max_le_right hN)]
  smul_mem' := by
    rintro c F ⟨K, h⟩
    refine ⟨K, fun N hN x => ?_⟩
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [fourierPartialSum_smul, h N hN]
end Fourier
section Kernel
open Real
def carlesonOp (h : ℝ → ℂ) (ν : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∫ t, h (x - t) * ((carlesonWeight t * Real.sin (ν x * t) / t : ℝ) : ℂ)
end Kernel
section Maximal
open Real
def carlesonLin (T : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (lam : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => M 0
  | n + 1 => fun x => if lam < ‖T (n + 1) x‖ then M (n + 1) else carlesonLin T M lam n x
end Maximal
section Main
open Real
end Main
section Statements
end Statements
end
end Auto


