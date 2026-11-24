-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TruncMatMemSubalgebra
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TruncMatMemSubalgebra
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:38:45.555961+00:00
-- url     : https://prove2.me/theorems/2b0cc3b2-d4cc-42c3-a154-08d458fb7cfc
-- title:
--   Trunc Mat Mem Subalgebra
-- statement:
--   Definitions and structural lemmas for Trunc Mat Mem Subalgebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TruncMatMemSubalgebra.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
namespace GlobalTheory.FlagPts
def truncMat {R : Type} [CommRing R] {d : ℕ} (m : ℕ) (M : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin d) (Fin d) R :=
  fun c e => if (c : ℕ) < m ∧ (e : ℕ) < m then M c e else if c = e then 1 else 0
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def frameMat (b g : Frames k V) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c e => (b i).repr (g i e) c
def lowMat (b g : Frames k V) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => (frameMat b g i * (truncMat ((a : ℕ) + 1) (frameMat b g i))⁻¹) c a
open Classical in

def flagLow (b : Frames k V) (F : Flags k V) (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => if h : ∃! v : V i, v ∈ F.step i ((a : ℕ) + 1) ∧ (b i).repr v a = 1 ∧
      ∀ c' : Fin (finrank k (V i)), c' < a → (b i).repr v c' = 0
    then (b i).repr h.exists.choose c else 0
def coordOf (j : ℕ) (L : ∀ i, Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k) :
    LocIdx k V j → k :=
  fun x => if ((x.2.1.2 : ℕ) < j ↔ (x.2.1.1 : ℕ) < j) then L x.1 x.2.1.1 x.2.1.2
    else (L x.1 * (truncMat j (L x.1)).adjugate) x.2.1.1 x.2.1.2
def chartInv (j : ℕ) (b : Frames k V) (F : Flags k V) : LocIdx k V j → k := coordOf j (flagLow b F)
def cellDisc [Fintype ι] (b g : Frames k V) : k :=
  ∏ i, ∏ m : Fin (finrank k (V i) + 1), (truncMat (m : ℕ) (frameMat b g i)).det
theorem det_mem_subalgebra {X : Type} {n : Type} [Fintype n] [DecidableEq n]
    (A : Subalgebra k (X → k)) (M : X → Matrix n n k) (h : ∀ c e, (fun x => M x c e) ∈ A) :
    (fun x => (M x).det) ∈ A := by
  simp only [Matrix.det_apply]
  have : (fun x => ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ c, M x (σ c) c) =
      ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ c, (fun x => M x (σ c) c) := by
    ext x
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun c _ => h _ _) _
theorem frameMat_mem_regFns (b : Frames k V) (i : ι) (c e : Fin (finrank k (V i))) :
    (fun g : Frames k V => frameMat b g i c e) ∈ regFns k V :=
  Algebra.subset_adjoin (.inl ⟨i, (b i).coord c, e, rfl⟩)
theorem truncMat_mem_subalgebra {X : Type} {d : ℕ} (A : Subalgebra k (X → k)) (m : ℕ)
    (M : X → Matrix (Fin d) (Fin d) k) (h : ∀ c e, (fun x => M x c e) ∈ A) (c e : Fin d) :
    (fun x => truncMat m (M x) c e) ∈ A := by
  simp only [truncMat]
  split_ifs
  · exact h c e
  · exact (show (fun _ : X => (1 : k)) = 1 from rfl) ▸ one_mem A
  · exact (show (fun _ : X => (0 : k)) = 0 from rfl) ▸ zero_mem A
theorem cellDisc_mem_regFns [Fintype ι] (b : Frames k V) : (fun g => cellDisc b g) ∈ regFns k V := by
  have : (fun g => cellDisc b g) = ∏ i, ∏ m : Fin (finrank k (V i) + 1),
      (fun g : Frames k V => (truncMat (m : ℕ) (frameMat b g i)).det) := by
    ext g
    simp [cellDisc, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun i _ => Subalgebra.prod_mem _ fun m _ =>
    det_mem_subalgebra _ _ (truncMat_mem_subalgebra _ _ _ (frameMat_mem_regFns b i))
def fracAlg [Fintype ι] (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ R ∈ regFns k V, ∃ K : ℕ, ∀ g, cellDisc b g ≠ 0 → f g * cellDisc b g ^ K = R g}
  mul_mem' := by
    rintro f₁ f₂ ⟨R₁, hR₁, K₁, h₁⟩ ⟨R₂, hR₂, K₂, h₂⟩
    refine ⟨R₁ * R₂, mul_mem hR₁ hR₂, K₁ + K₂, fun g hg => ?_⟩
    simp only [Pi.mul_apply, ← h₁ g hg, ← h₂ g hg]
    ring
  add_mem' := by
    rintro f₁ f₂ ⟨R₁, hR₁, K₁, h₁⟩ ⟨R₂, hR₂, K₂, h₂⟩
    have hD := cellDisc_mem_regFns b
    refine ⟨R₁ * (fun g => cellDisc b g) ^ K₂ + R₂ * (fun g => cellDisc b g) ^ K₁,
      add_mem (mul_mem hR₁ (pow_mem hD _)) (mul_mem hR₂ (pow_mem hD _)), K₁ + K₂, fun g hg => ?_⟩
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, ← h₁ g hg, ← h₂ g hg]
    ring
  algebraMap_mem' := fun r =>
    ⟨algebraMap k _ r, Subalgebra.algebraMap_mem _ r, 0, fun g _ => by simp⟩
example [Fintype ι] (b : Frames k V) : cellDisc b b = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun m _ => ?_
  have : truncMat (m : ℕ) (frameMat b b i) = 1 := by
    ext c e
    simp only [truncMat, frameMat, Basis.repr_self, Matrix.one_apply]
    by_cases h : e = c
    · subst h; simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  rw [this, Matrix.det_one]
end GlobalTheory.FlagPts


