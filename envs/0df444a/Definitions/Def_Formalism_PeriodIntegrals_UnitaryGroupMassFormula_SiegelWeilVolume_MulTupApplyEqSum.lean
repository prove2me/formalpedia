-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:23.906751+00:00
-- url     : https://prove2.me/theorems/455958b8-6994-4a92-bd31-107a6fccebb2
-- title:
--   Mul Tup Apply Eq Sum
-- statement:
--   Definitions and structural lemmas for Mul Tup Apply Eq Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix
section Alg
variable {K : Type} [CommRing K] {n M : ℕ}
def mulTup (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) : Fin n → Fin M → K :=
  fun j i => ∑ k, D k j * X k i
end Alg
section Herm
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n M : ℕ}
def conjT (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (D.map (sigR R σ))ᵀ
theorem conjT_mul (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (A * B) = conjT R σ B * conjT R σ A := by
  unfold conjT
  rw [Matrix.map_mul, Matrix.transpose_mul]
theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
theorem conjT_conjT (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    conjT R σ (conjT R σ A) = A := by
  ext i j
  simp [conjT, sigR_sigR R σ hσ]
theorem mem_herm_iff (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    S ∈ HermR R σ n ↔ conjT R σ S = S := by
  constructor
  · intro h
    have h' : ∀ a b, sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = S a b := h
    ext a b
    exact h' a b
  · intro h
    have h' : ∀ a b, sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = S a b := by
      intro a b
      have := congrFun (congrFun h a) b
      simpa [conjT] using this
    exact h'
def hermMap (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) :
    HermR R σ n :=
  ⟨conjT R σ D * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * D, by
    rw [mem_herm_iff, conjT_mul, conjT_mul, conjT_conjT R σ hσ, (mem_herm_iff R σ _).1 S.2,
      Matrix.mul_assoc]⟩
def tupS (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin M) (R ⊗[F] E) :=
  Matrix.of fun a i => sigR R σ (X a i)
def tupT (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  Matrix.of fun i b => X b i
def jM (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  Matrix.of fun i j => inclR R (J i j)
end Herm
def GramMulTup : Prop := ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
  [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
  (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E),
  gramR R σ J (mulTup D X) = conjT R σ D * gramR R σ J X * D
end PI.DegenerateSiegelWeil.Scale


