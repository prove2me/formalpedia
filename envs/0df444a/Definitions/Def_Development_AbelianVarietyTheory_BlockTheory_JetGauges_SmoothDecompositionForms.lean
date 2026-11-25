-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_SmoothDecompositionForms
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:34.725554+00:00
-- url     : https://prove2.me/theorems/e3c0eb10-cce9-46e6-9b6a-fe3d1b3089ef
-- title:
--   Smooth Decomposition Forms
-- statement:
--   Definitions and structural lemmas for Smooth Decomposition Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SmoothDecompositionForms.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Theorems.Thm_PI_HwUniqW_Hpk_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1)
abbrev Mx (k r : ℕ) := Matrix (Ix k r) (Ix k r) ℂ
def Kmax (k r : ℕ) : Set (Mx k r) := UH (Hpk k r) ∩ (Matrix.unitaryGroup (Ix k r) ℂ : Set _)
structure HRep (k r : ℕ) : Type 1 where

  H : Type
  [instNorm : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℂ H]
  [instComplete : CompleteSpace H]

  σ : Mx k r → (H →L[ℂ] H)
  isURep : IsURepOn (UH (Hpk k r)) σ
attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete
variable {k r : ℕ}
def HRep.smooth (R : HRep k r) : Set R.H := smoothVecs (k := k) (r := r) R.σ
def HRep.IsDiscrete (R : HRep k r) (ε : Ix k r → Bool) (μ : Ix k r → ℝ) : Prop :=
  IsHCParam μ ∧ IsDSHpk k r ε μ R.σ
def LieWord (k r : ℕ) (w : List (Mx k r)) : Prop := ∀ X ∈ w, InLieHpk k r X
def HRep.semi (R : HRep k r) (Ws : List (List (Mx k r))) (v : R.H) : ℝ :=
  (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum
structure IsSmoothMap (R₁ R₂ : HRep k r) (A : R₁.H → R₂.H) : Prop where
  maps : ∀ v ∈ R₁.smooth, A v ∈ R₂.smooth
  map_add : ∀ v ∈ R₁.smooth, ∀ w ∈ R₁.smooth, A (v + w) = A v + A w
  map_smul : ∀ (a : ℂ), ∀ v ∈ R₁.smooth, A (a • v) = a • A v
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ v ∈ R₁.smooth, ‖dsigW (k := k) (r := r) R₂.σ w (A v)‖ ≤ C * R₁.semi Ws v
section Tensor
variable {ι : Type} [Fintype ι]
def tensSmooth (ι : Type) (R : HRep k r) : Set (ι → R.H) := {x | ∀ c, x c ∈ R.smooth}
def tensAct (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) (g : Mx k r) (x : ι → R.H) : ι → R.H :=
  fun c => ∑ d, ρ g c d • R.σ g (x d)
def pureT {E : Type} [AddCommGroup E] [Module ℂ E] (a : ι → ℂ) (v : E) : ι → E := fun c => a c • v
def tensForm (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : ι → H) : ℂ :=
  ∑ c, ∑ d, A c d * ⟪y c, x d⟫_ℂ
def flat (A : Matrix ι ι ℂ) (y : ι → ℂ) : ι → ℂ := star y ᵥ* A
def contr (A : Matrix ι ι ℂ) (ω : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (x : ι → E) : E :=
  ∑ d, flat A ω d • x d
def IsSmoothMapInto (R₁ R : HRep k r) (A : R₁.H → ι → R.H) : Prop :=
  ∀ c, IsSmoothMap R₁ R fun v => A v c
structure IsSmoothMapFrom (R R₂ : HRep k r) (A : (ι → R.H) → R₂.H) : Prop where
  maps : ∀ x ∈ tensSmooth ι R, A x ∈ R₂.smooth
  map_add : ∀ x ∈ tensSmooth ι R, ∀ y ∈ tensSmooth ι R, A (x + y) = A x + A y
  map_smul : ∀ (a : ℂ), ∀ x ∈ tensSmooth ι R, A (a • x) = a • A x
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ x ∈ tensSmooth ι R, ‖dsigW (k := k) (r := r) R₂.σ w (A x)‖ ≤ C * ∑ c, R.semi Ws (x c)
structure IsSmoothDecomp (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J] (Rs : J → HRep k r)
    (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) : Prop where
  io_cont : ∀ j, IsSmoothMapInto (Rs j) R (io j)
  p_cont : ∀ j, IsSmoothMapFrom R (Rs j) (p j)
  io_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ v ∈ (Rs j).smooth, io j ((Rs j).σ g v) = tensAct ρ R g (io j v)
  p_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ x ∈ tensSmooth ι R, p j (tensAct ρ R g x) = (Rs j).σ g (p j x)
  p_io : ∀ j, ∀ v ∈ (Rs j).smooth, p j (io j v) = v
  p_io_ne : ∀ i j, i ≠ j → ∀ v ∈ (Rs j).smooth, p i (io j v) = 0
  sum_io_p : ∀ x ∈ tensSmooth ι R, ∑ j, io j (p j x) = x
structure IsSignedDecomp (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J]
    (Rs : J → HRep k r) (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) (ep : J → ℝ) : Prop
    extends IsSmoothDecomp ρ R Rs io p where
  sign : ∀ j, ep j = 1 ∨ ep j = -1
  form_eq : ∀ j, ∀ x ∈ (Rs j).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io j x) (io j y) = (ep j : ℂ) * ⟪y, x⟫_ℂ
  orth : ∀ i j, i ≠ j → ∀ x ∈ (Rs i).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io i x) (io j y) = 0
variable [DecidableEq ι]
structure IsFormRep (k r : ℕ) (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (l : ℕ) : Prop where
  map_one : ρ 1 = 1
  map_mul : ∀ g ∈ UH (Hpk k r), ∀ g' ∈ UH (Hpk k r), ρ (g * g') = ρ g * ρ g'
  smooth : ∀ c d, SmoothOnH (Hpk k r) fun g => ρ g c d
  herm : Aᴴ = A
  sq : A * A = 1
  inv : ∀ g ∈ UH (Hpk k r), (ρ g)ᴴ * A * ρ g = A
  unitK : ∀ g ∈ Kmax k r, ρ g ∈ Matrix.unitaryGroup ι ℂ
  growth : ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ∀ c d, ‖ρ g c d‖ ≤ C * Real.sqrt (hs g) ^ l
def dualRep (ρ : Mx k r → Matrix ι ι ℂ) (g : Mx k r) : Matrix ι ι ℂ := (ρ g⁻¹)ᵀ
def dualGram (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := (A⁻¹)ᵀ
end Tensor
def stdRep (k r : ℕ) (g : Mx k r) : Mx k r := g
def stdDualRep (k r : ℕ) : Mx k r → Mx k r := dualRep (stdRep k r)
abbrev Sub (n l : ℕ) := {I : Finset (Fin n) // I.card = l}
def Sub.enum {n l : ℕ} (I : Sub n l) : Fin l → Fin n := I.1.orderEmbOfFin I.2
def wedgeMat {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n l) (Sub n l) ℂ :=
  Matrix.of fun I I' => (g.submatrix I.enum I'.enum).det
def wedgeVec {n l : ℕ} (x : Fin l → Fin n → ℂ) : Sub n l → ℂ :=
  fun I => (Matrix.of fun a b : Fin l => x b (I.enum a)).det
def wedgeRep (k r l : ℕ) (g : Mx k r) : Matrix (Sub (2 * r + k + 1) l) (Sub (2 * r + k + 1) l) ℂ := wedgeMat l g
def wedgeGram (k r l : ℕ) : Matrix (Sub (2 * r + k + 1) l) (Sub (2 * r + k + 1) l) ℂ := wedgeMat l (Hpk k r)
def flagVec (k r : ℕ) (z : Ix k r → ℂ) (a : Fin (r + 1)) : Ix k r → ℂ :=
  if h : a.val < r then bvec (eI k r ⟨a.val, h⟩) else z
def flagWedge {k r l : ℕ} (hl : l ≤ r + 1) (f : Fin (r + 1) → Ix k r → ℂ) : Sub (2 * r + k + 1) l → ℂ :=
  wedgeVec fun a => f (Fin.castLE hl a)
def flatV (k r : ℕ) (f : Ix k r → ℂ) : Ix k r → ℂ := flat (Hpk k r) f
def shiftUp {n : ℕ} (μ : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ := fun a => μ a + if a ∈ I then 1 else 0
def shiftDown {n : ℕ} (μ : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ := fun a => μ a - if a ∈ I then 1 else 0
section Checks
variable {ι : Type} [Fintype ι]
theorem norm_det_of_mem {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : ‖g.det‖ = 1 := by
  have h0 : (Hpk k r).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (PI.HwUniqW.Hpk_mul_self (k := k) (r := r))
    simp [h] at this
  have h1 := congrArg Matrix.det (show gᴴ * Hpk k r * g = Hpk k r from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ h0
    linear_combination h1
  have h3 := congrArg norm h2
  rw [norm_mul, norm_star, norm_one] at h3
  nlinarith [norm_nonneg g.det]
def detRep (k r : ℕ) : HRep k r where
  H := ℂ
  σ g := g.det • ContinuousLinearMap.id ℂ ℂ
  isURep := by
    refine ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
    · ext; simp
    · ext; simp [mul_comm]
    · simp [norm_det_of_mem hg]
    · refine Continuous.continuousOn ?_
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      exact (continuous_id.matrix_det).mul continuous_const
end Checks
end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms
end


