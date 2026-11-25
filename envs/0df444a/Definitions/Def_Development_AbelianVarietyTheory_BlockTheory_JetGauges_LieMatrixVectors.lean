-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:41.058802+00:00
-- url     : https://prove2.me/theorems/63af01bb-ae7b-4a47-8672-0b0d0091f82e
-- title:
--   Lie Matrix Vectors
-- statement:
--   Definitions and structural lemmas for Lie Matrix Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/LieMatrixVectors.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.QuantumDeterminants (inWb Tz UWset eI esI wI bvec)
open PI.UpqRep (IsHCParam IsHCTypeU IsCayleyU IsDS IsLowUnit IsKStableOn UJset)
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixVectors
abbrev MatV (k r : ℕ) : Type := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def negVec (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))
def embW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : MatV k r := fun i j =>
  if hij : (r ≤ i.val ∧ i.val < r + k) ∧ (r ≤ j.val ∧ j.val < r + k) then
    h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j then 1 else 0
def IsFrameFor (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : MatV k r) : Prop :=
  γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    (∀ a : Fin r, γ *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ γ *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    γ *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • negVec k r) = z
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : MatV k r → (H →L[ℂ] H)) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ IsHCParam u ∧
    ∃ γ : MatV k r, IsFrameFor k r z γ ∧ IsHCTypeU k u (fun h => π (γ * embW k r h * γ⁻¹))
def IsLowUnitG (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : MatV k r → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P : MatV k r, IsCayleyU k r ε P ∧ IsDS ε lam (fun g => σ (P⁻¹ * g * P)) ∧
    IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w
def IsLowUnitAdapted (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (σ : MatV k r → (H →L[ℂ] H)) (w : H) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧
    ∃ γ : MatV k r, IsFrameFor k r z γ ∧ IsLowUnitG k r ε lam (fun g => σ (γ * g * γ⁻¹)) w
end Rep
def lieG (k r : ℕ) : Submodule ℝ (MatV k r) where
  carrier := {X | Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]
def formAdj (k r : ℕ) (Y : MatV k r) : MatV k r := Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r
def lieRe (k r : ℕ) (Y : MatV k r) : MatV k r := (1 / 2 : ℂ) • (Y - formAdj k r Y)
def lieIm (k r : ℕ) (Y : MatV k r) : MatV k r := (-Complex.I / 2 : ℂ) • (Y + formAdj k r Y)
section Derived
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def HasDerived (σ : MatV k r → (H →L[ℂ] H)) (X : MatV k r) (v w : H) : Prop :=
  X ∈ lieG k r ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) w 0
def dAct (σ : MatV k r → (H →L[ℂ] H)) (X : MatV k r) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0
def dWord (σ : MatV k r → (H →L[ℂ] H)) (L : List (MatV k r)) (v : H) : H :=
  L.foldr (dAct σ) v
inductive HasDerivedWord (σ : MatV k r → (H →L[ℂ] H)) (v : H) : List (MatV k r) → H → Prop
  | nil : HasDerivedWord σ v [] v
  | cons {X : MatV k r} {L : List (MatV k r)} {x w : H} :
      HasDerivedWord σ v L x → HasDerived σ X x w → HasDerivedWord σ v (X :: L) w
def dActC (σ : MatV k r → (H →L[ℂ] H)) (Y : MatV k r) (v : H) : H :=
  dAct σ (lieRe k r Y) v + Complex.I • dAct σ (lieIm k r Y) v
def dWordC (σ : MatV k r → (H →L[ℂ] H)) (L : List (MatV k r)) (v : H) : H :=
  L.foldr (dActC σ) v
end Derived
section Diagonal
variable {n : ℕ} {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
def IsKFinJ (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S
def UnitEquivJ (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ v : H, U (σ g v) = σ' g (U v)
end Diagonal
lemma Tz_negVec (k r : ℕ) : Tz k r (negVec k r) = 1 := by
  unfold Tz Formalism.QuantumDeterminants.herm negVec bvec
  rw [Matrix.mulVec_single_one, ← Pi.single_star, star_one, single_one_dotProduct]
  simp [Formalism.QuantumDeterminants.Hpk, wI]
lemma isFrameFor_negVec (k r : ℕ) :
    inWb k r (negVec k r) ∧ 0 < Tz k r (negVec k r) ∧ IsFrameFor k r (negVec k r) 1 := by
  refine ⟨?_, by rw [Tz_negVec]; exact one_pos, ?_, ?_, ?_⟩
  · intro i hi
    unfold negVec bvec
    apply Pi.single_eq_of_ne
    intro h
    have := congrArg Fin.val h
    simp [wI] at this
    omega
  · simp [Formalism.QuantumDeterminants.UH]
  · intro a; simp
  · simp [Tz_negVec]
lemma isHCTypeU_trivial (k : ℕ) :
    IsHCTypeU k (PI.UpqRep.rhoC (PI.UpqRep.allPos k))
      (fun _ => (1 : ℂ →L[ℂ] ℂ)) := by
  have hlow : PI.UpqRep.lowK (PI.UpqRep.allPos k) (PI.UpqRep.rhoC (PI.UpqRep.allPos k)) = 0 := by
    funext a
    simp [PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.allPos]
  refine ⟨inferInstance, inferInstance, ⟨⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl,
    fun _ => continuousOn_const⟩, inferInstance, fun _ _ _ _ => trivial,
    fun S _ _ => eq_bot_or_eq_top S, ⟨1, trivial, one_ne_zero, ?_⟩, ?_⟩
  · intro θ _
    simp [hlow]
  · intro μ v _ hv hw
    refine ⟨0, by simp, ?_⟩
    have hμ : μ = 0 := by
      funext a
      by_contra ha
      have ha' : μ a ≠ 0 := ha
      have hmem : Matrix.diagonal (fun b => Complex.exp
          ((((Pi.single a (Real.pi / μ a) : Fin k → ℝ) b : ℝ) : ℂ) * Complex.I)) ∈
          PI.UpqRep.Kset (PI.UpqRep.allPos k) := by
        refine ⟨?_, ?_⟩
        · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
            Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext b
          rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
            Complex.norm_exp_ofReal_mul_I]
          norm_num
        · simp [PI.UpqRep.Jm, PI.UpqRep.allPos]
      have h := hw _ hmem
      have hs : ∑ b, μ b * (Pi.single a (Real.pi / μ a) : Fin k → ℝ) b = Real.pi := by
        rw [Finset.sum_eq_single a]
        · simp; field_simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · simp
      rw [hs, Complex.exp_pi_mul_I] at h
      apply hv
      have h2 : v = -v := by simpa using h
      linear_combination h2 / 2
    simp [hlow, hμ]
example (r : ℕ) : IsHCTypeW 1 r (negVec 1 r) (PI.UpqRep.rhoC (PI.UpqRep.allPos 1))
    (fun _ => (1 : ℂ →L[ℂ] ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := isFrameFor_negVec 1 r
  refine ⟨h1, h2, ⟨Subsingleton.strictAnti _, fun a => ⟨0, ?_⟩⟩, 1, h3, isHCTypeU_trivial 1⟩
  obtain rfl : a = 0 := Subsingleton.elim _ _
  simp [PI.UpqRep.rhoC]
end GlobalTheory.IndefiniteRowSideFullHecke.LieMatrixVectors
end


