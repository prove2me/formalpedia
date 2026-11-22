-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:51:11.990119+00:00
-- url     : https://prove2.me/theorems/7e42ba03-f44f-4464-8c0c-a21db5c75cdb
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicBound/Development.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.GGMirBoundW
open Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
def D (F : Type) [Fintype F] (m : ℕ) : ℕ := ∏ i ∈ Finset.Ico 1 m, (Fintype.card F ^ i - 1)
section Defs
variable {F : Type} [Field F] [Fintype F]
def blkM {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
def blkHom (F : Type) [Field F] (n : ℕ) : Matrix (Fin n) (Fin n) F →* Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun := blkM
  map_one' := by
    simp only [blkM, Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' A B := by
    simp only [blkM]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
def E (F : Type) [Field F] (n : ℕ) : GL (Fin n) F →* GL (Fin (n + 1)) F := Units.map (blkHom F n)
def colM {n : ℕ} (x : Fin n → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  (Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) => x i) 0 (1 : Matrix (Fin 1) (Fin 1) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
theorem colM_mul {n : ℕ} (x y : Fin n → F) : colM x * colM y = colM (x + y) := by
  simp only [colM]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [add_comm]
  · simp
  · simp
theorem colM_zero {n : ℕ} : colM (0 : Fin n → F) = 1 := by
  simp only [colM]
  have : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → F) i) = 0 := by ext; simp
  rw [this, Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _
def col {n : ℕ} (x : Fin n → F) : GL (Fin (n + 1)) F where
  val := colM x
  inv := colM (-x)
  val_inv := by rw [colM_mul, add_neg_cancel, colM_zero]
  inv_val := by rw [colM_mul, neg_add_cancel, colM_zero]
def LastRowE {n : ℕ} (g : GL (Fin (n + 1)) F) : Prop :=
  ∀ j, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = if j = Fin.last n then 1 else 0
end Defs
def Claim (F : Type) [Field F] [Fintype F] (n : ℕ) : Prop :=
  ∀ (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) F) V)
      (ℓ : Module.Dual ℂ V), ℓ ≠ 0 → IsWhit ψ₀ π ℓ →
      ∃ p : Fin (D F (n + 1)) → GL (Fin (n + 1)) F,
        (∀ i, LastRowE (p i)) ∧ LinearIndependent ℂ (fun i => ℓ ∘ₗ π (p i))
def BaseProp : Prop := ∀ (F : Type) [Field F] [Fintype F], Claim F 0
def StepProp : Prop := ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), Claim F n → Claim F (n + 1)
def UnitriangularBlockExtension : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (u : GL (Fin n) F), IsUni n u →
    IsUni (n + 1) (E F n u) ∧
      superdiag (n + 1) (E F n u : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
        superdiag n (u : Matrix (Fin n) (Fin n) F)
def ColFacts : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (x : Fin (n + 1) → F),
    IsUni (n + 2) (col x) ∧
      superdiag (n + 2) (col x : Matrix (Fin (n + 2)) (Fin (n + 2)) F) = x (Fin.last n)
def ConjCol : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (A : GL (Fin n) F) (x : Fin n → F),
    E F n A * col x = col ((A : Matrix (Fin n) (Fin n) F) *ᵥ x) * E F n A
def RowExists : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (r : Fin (n + 1) → F), r ≠ 0 →
    ∃ g : GL (Fin (n + 1)) F, ∀ j, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = r j
def CharOrth : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (m : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 → ∀ r s : Fin m → F,
    (∑ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x))) = if r = s then (Fintype.card F : ℂ) ^ m else 0
def SepLemma : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X R ι : Type) [Fintype X] [Fintype R] [Fintype ι]
    (T : X → W →ₗ[ℂ] W) (χ χ' : R → X → ℂ) (N : ℂ), N ≠ 0 →
    (∀ r s, ∑ x, χ r x * χ' s x = if r = s then N else 0) →
    ∀ f : R × ι → W, (∀ x r i, T x (f (r, i)) = χ r x • f (r, i)) →
      (∀ r, LinearIndependent ℂ (fun i => f (r, i))) → LinearIndependent ℂ f
def StepOf : Prop := UnitriangularBlockExtension → ColFacts → ConjCol → RowExists → CharOrth → SepLemma → StepProp
end
end PI.GGMirBoundW


