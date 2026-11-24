-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:31:16.666928+00:00
-- url     : https://prove2.me/theorems/2596428a-bf15-4ff8-8044-868addeb1d86
-- title:
--   Hermitian Form Factor
-- statement:
--   Definitions and structural lemmas for Hermitian Form Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
section Defs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def cm {m Q : Type} (Y : Q → m → ℂ) : Matrix m Q ℂ := fun i j => Y j i
structure Frame {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (Em : Matrix m Q ℂ) : Prop where
  pp : Epᴴ * Ep = 1
  mm : Emᴴ * Em = 1
  pm : Epᴴ * Em = 0
  sum : Ep * Epᴴ + Em * Emᴴ = 1
  diff : Ep * Epᴴ - Em * Emᴴ = H
def Tm {m Q : Type} [Fintype m] (H : Matrix m m ℂ) (Y : Matrix m Q ℂ) : Matrix Q Q ℂ := -(Yᴴ * H * Y)
def qf {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q] (T : Matrix Q Q ℂ) (B : Matrix P Q ℂ) : ℝ :=
  (Matrix.trace (B * T⁻¹ * Bᴴ)).re
def bet {m P Q : Type} [Fintype m] [Fintype P] [Fintype Q] (Ep : Matrix m P ℂ) (Em : Matrix m Q ℂ) (g : Matrix m m ℂ) : ℝ :=
  (Matrix.trace ((Epᴴ * g * Em) * (Epᴴ * g * Em)ᴴ)).re
end Defs
section Alg
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Frame
end Frame
namespace Frame
end Frame
end Alg
section Shear
section gramsec
variable {Q : Type} [Fintype Q] [DecidableEq Q]
def gram (X : Q → Q → ℂ) : Matrix Q Q ℂ := (cm X)ᴴ * cm X
end gramsec
section rankone
variable {Q : Type} [Fintype Q] [DecidableEq Q]
end rankone
section rankone2
variable {Q : Type} [Fintype Q] [DecidableEq Q]
def colL (n : Q → ℂ) (c : ℂ) (i₀ : Q) : (Q → ℂ) →ₗ[ℝ] (Q → ℂ) where
  toFun x := x + (c * x i₀) • (n - Pi.single i₀ 1)
  map_add' x y := by
    funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  map_smul' a x := by
    funext l; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul]; ring
def rmulL (A : Matrix Q Q ℂ) : (Q → Q → ℂ) →ₗ[ℝ] (Q → Q → ℂ) where
  toFun X := fun j i => (cm X * A) i j
  map_add' X Y := by
    funext j i; simp [cm, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a X := by
    funext j i; simp [cm, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
end rankone2
section shearsec
variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq Q]
end shearsec
end Shear
section Core
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
theorem isAddHaarMeasure_matrix_volume {A B : Type} [Fintype A] [Fintype B] : (volume : Measure (A → B → ℂ)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (B → ℂ)).IsAddHaarMeasure := by
    rw [MeasureTheory.volume_pi]
    first
    | infer_instance
    | exact MeasureTheory.Measure.pi.isAddHaarMeasure _
  rw [MeasureTheory.volume_pi]
  first
  | infer_instance
  | exact MeasureTheory.Measure.pi.isAddHaarMeasure _
attribute [local instance] isAddHaarMeasure_matrix_volume
theorem haar_prod2 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] :
    ((volume : Measure (A → B → ℂ)).prod (volume : Measure (C → D → ℂ))).IsAddHaarMeasure := by
  haveI := (isAddHaarMeasure_matrix_volume : (volume : Measure (A → B → ℂ)).IsAddHaarMeasure)
  haveI := (isAddHaarMeasure_matrix_volume : (volume : Measure (C → D → ℂ)).IsAddHaarMeasure)
  first
  | infer_instance
  | exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
attribute [local instance] haar_prod2
def coordE (F : Frame H Ep Em) : (Q → m → ℂ) ≃ₗ[ℝ] (Q → P → ℂ) × (Q → Q → ℂ) where
  toFun Y := (fun j => Epᴴ *ᵥ Y j, fun j => Emᴴ *ᵥ Y j)
  invFun p := fun j => Ep *ᵥ p.1 j + Em *ᵥ p.2 j
  map_add' Y Y' := by
    ext j i <;> simp [Matrix.mulVec_add]
  map_smul' c Y := by
    ext j i <;> simp [Matrix.mulVec_smul]
  left_inv Y := by
    funext j
    simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, F.sum, Matrix.one_mulVec]
  right_inv p := by
    have hmp : Emᴴ * Ep = 0 := by
      have := congrArg Matrix.conjTranspose F.pm
      simpa using this
    ext j i
    · simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, F.pp, F.pm, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    · simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, F.mm, hmp, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]
def Kset (P Q : Type) [Fintype P] [Fintype Q] [DecidableEq Q] (ρ : ℝ) : Set ((Q → Q → ℂ) × (Q → P → ℂ)) :=
  {p | (Matrix.of p.1).PosDef ∧ (Matrix.trace (Matrix.of p.1)).re ≤ 1 ∧ qf (Matrix.of p.1) (cm p.2) ≤ ρ ^ 2}
def Kf (P Q : Type) [Fintype P] [Fintype Q] [DecidableEq Q] (ρ : ℝ) : (Q → Q → ℂ) × (Q → P → ℂ) → ℝ≥0∞ :=
  (Kset P Q ρ).indicator 1
def tb (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (Y : Q → m → ℂ) : (Q → Q → ℂ) × (Q → P → ℂ) :=
  (Tm H (cm Y), fun j => Epᴴ *ᵥ Y j)
def act (g : m → m → ℂ) (Y : Q → m → ℂ) : Q → m → ℂ := fun j => Matrix.of g *ᵥ Y j
def adjF (g : m → m → ℂ) : m → m → ℂ := (Matrix.of g).adjugate
def invF (g : m → m → ℂ) : m → m → ℂ := ((Matrix.of g)⁻¹ : Matrix m m ℂ)
def lmF (a : Matrix m m ℂ) (x : m → m → ℂ) : m → m → ℂ := a * Matrix.of x
def rmF (a : Matrix m m ℂ) (x : m → m → ℂ) : m → m → ℂ := Matrix.of x * a
def Ff (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (ρ : ℝ) (Y : Q → m → ℂ) : ℝ≥0∞ := Kf P Q ρ (tb H Ep Y)
def Bset (Ep : Matrix m P ℂ) (Em : Matrix m Q ℂ) (ρ : ℝ) : Set (m → m → ℂ) := {x | bet Ep Em (Matrix.of x) ≤ ρ ^ 2}
def Lv (H : Matrix m m ℂ) (Ep : Matrix m P ℂ) (Q : Type) [Fintype Q] [DecidableEq Q] (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ Y : Q → m → ℂ, Ff H Ep ρ Y
open scoped Pointwise
def Sl (P : Type) [Fintype P] (T : Q → Q → ℂ) (σ : ℝ) : Set (Q → P → ℂ) := {B | qf (Matrix.of T) (cm B) ≤ σ ^ 2}
def gramF (X : Q → Q → ℂ) : Q → Q → ℂ := gram X
def Mv (P Q : Type) [Fintype P] [Fintype Q] [DecidableEq Q] (ρ : ℝ) : ℝ≥0∞ :=
  ∫⁻ X : Q → Q → ℂ, ∫⁻ B : Q → P → ℂ, Kf P Q ρ (gramF X, B)
def swapBlockPair (p : (Q → P → ℂ) × (Q → Q → ℂ)) : (Q → Q → ℂ) × (Q → P → ℂ) :=
  (gram p.2 - (cm p.1)ᴴ * cm p.1, p.1)
end Core
end Formalism.FourierDecayAlt.P.HermitianFormFactor
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


