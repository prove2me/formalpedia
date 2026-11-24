-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:10.188112+00:00
-- url     : https://prove2.me/theorems/3534e4e4-940a-4c85-adaf-dafe9a4f1e4d
-- title:
--   Same Partition Statement
-- statement:
--   Definitions and structural lemmas for Same Partition Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
namespace GlobalTheory.CompanionTheory.TyFinSamePart
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
def bd (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) : Matrix ι ι K :=
  fun i j => if h : b j = b i then L (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0
theorem bd_blk (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (c : Fin s) :
    blk K b c (bd b L) = L c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  subst hi
  simp [blk, bd, hj]
theorem bd_off (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) {i j : ι}
    (h : b j ≠ b i) : bd b L i j = 0 := dif_neg h
theorem eq_bd (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) {M : Matrix ι ι K}
    (h1 : ∀ c, blk K b c M = L c) (h2 : ∀ i j, b j ≠ b i → M i j = 0) : M = bd b L := by
  ext i j
  by_cases h : b j = b i
  · have := congrFun (congrFun (h1 (b i)) ⟨i, rfl⟩) ⟨j, h⟩
    simpa [bd, h, blk] using this
  · rw [bd_off b L h, h2 i j h]
theorem isBlockUT_bd {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) :
    IsBlockUT K b' (bd b L) := fun i j h => bd_off b L (hb i j h)
theorem bd_one (b : ι → Fin s) : bd b (fun c => (1 : Matrix {i // b i = c} {i // b i = c} K)) = 1 := by
  symm
  apply eq_bd
  · intro c
    exact Matrix.submatrix_one _ Subtype.val_injective
  · intro i j h
    exact Matrix.one_apply_ne fun e => h (by rw [e])
theorem bd_mul (b : ι → Fin s) (L L' : ∀ c, Matrix {i // b i = c} {i // b i = c} K) :
    bd b (fun c => L c * L' c) = bd b L * bd b L' := by
  have hut : ∀ M : ∀ c, Matrix {i // b i = c} {i // b i = c} K, IsBlockUT K b (bd b M) := fun M =>
    isBlockUT_bd b b (fun i j h e => by rw [e] at h; exact lt_irrefl _ h) M
  symm
  apply eq_bd
  · intro c
    rw [blk_mul b c (hut L) (hut L'), bd_blk, bd_blk]
  · intro i j h
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : b k = b i
    · rw [bd_off b L' (i := k) (j := j) (by rw [hk]; exact h), mul_zero]
    · rw [bd_off b L hk, zero_mul]
def dGL (b : ι → Fin s) (L : ∀ c, GL {i // b i = c} K) : GL ι K where
  val := bd b fun c => (L c : Matrix _ _ K)
  inv := bd b fun c => ((L c)⁻¹ : GL _ K).1
  val_inv := by
    rw [← bd_mul]
    simp only [Units.mul_inv]
    exact bd_one b
  inv_val := by
    rw [← bd_mul]
    simp only [Units.inv_mul]
    exact bd_one b
def leviHom (b : ι → Fin s) : parab K b →* ∀ c, GL {i // b i = c} K where
  toFun p c := levi K b c p
  map_one' := by
    funext c
    apply Units.ext
    exact Matrix.submatrix_one _ Subtype.val_injective
  map_mul' p q := by
    funext c
    apply Units.ext
    exact blk_mul b c p.2.1 q.2.1
abbrev ren {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) :
    {i // b i = c} ≃ {i // (π ∘ b) i = π c} :=
  Equiv.subtypeEquivRight (p := fun i => b i = c) (q := fun i => (π ∘ b) i = π c)
    fun _ => π.injective.eq_iff.symm
def ell {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    (parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)) →* ∀ c, GL {i // b i = c} K :=
  (leviHom b).comp (Subgroup.inclusion inf_le_left)
end GlobalTheory.CompanionTheory.TyFinSamePart


