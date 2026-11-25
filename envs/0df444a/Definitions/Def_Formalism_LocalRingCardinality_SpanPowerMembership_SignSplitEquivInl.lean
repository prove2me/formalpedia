-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:54.060952+00:00
-- url     : https://prove2.me/theorems/8853ba0a-b0a0-4554-9efe-8e6d6d0d8a72
-- title:
--   Sign Split Equiv Inl
-- statement:
--   Definitions and structural lemmas for Sign Split Equiv Inl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/SignSplitEquivInl.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_coeMatrix_left_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
section One
variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
abbrev re : MM P Q ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Matrix.reindexAlgEquiv ℂ ℂ e
theorem re_star (X : MM P Q) : re e Xᴴ = (re e X)ᴴ := by
  simp [re, Matrix.reindexAlgEquiv_apply, Matrix.conjTranspose_reindex]
include h1 h2 in
theorem re_J : re e (Formalism.UG.Jpq P Q) = Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [re, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply, e.injective.eq_iff, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, h1, h2] <;> split_ifs <;> simp
include h1 h2 in
theorem re_mem (M : MM P Q) : inUJ ε (re e M) ↔ Mᴴ * Formalism.UG.Jpq P Q * M = Formalism.UG.Jpq P Q := by
  unfold inUJ
  rw [← re_J ε e h1 h2, ← re_star, ← map_mul, ← map_mul]
  exact (re e).injective.eq_iff
def ofMatJ (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h) : UJ ε :=
  ⟨⟨h, Jm ε * hᴴ * Jm ε, mul_eq_one_comm.mp (coeMatrix_left_inv ε h hh), coeMatrix_left_inv ε h hh⟩, hh⟩
def ofMatU (h : MM P Q) (hh : hᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q) : UpqT P Q :=
  (exists_of_mem P Q h hh).choose
theorem mat_ofMatU (h : MM P Q) (hh : hᴴ * Formalism.UG.Jpq P Q * h = Formalism.UG.Jpq P Q) :
    UpqT.mat (ofMatU h hh) = h := (exists_of_mem P Q h hh).choose_spec
include h1 h2 in
theorem symm_mem (a : UJ ε) : ((re e).symm (coeMatrixAlt ε a))ᴴ * Formalism.UG.Jpq P Q * (re e).symm (coeMatrixAlt ε a) =
    Formalism.UG.Jpq P Q :=
  (re_mem ε e h1 h2 _).mp (by rw [AlgEquiv.apply_symm_apply]; exact a.2)
def phi : UpqT P Q ≃* UJ ε where
  toFun g := ofMatJ ε (re e (UpqT.mat g)) ((re_mem ε e h1 h2 _).mpr (mat_mem P Q g))
  invFun a := ofMatU ((re e).symm (coeMatrixAlt ε a)) (symm_mem ε e h1 h2 a)
  left_inv g := mat_injective P Q (by
    rw [mat_ofMatU]
    exact (re e).symm_apply_apply _)
  right_inv a := Subtype.ext (Units.ext
    ((congrArg (re e) (mat_ofMatU _ (symm_mem ε e h1 h2 a))).trans
      ((re e).apply_symm_apply _)))
  map_mul' g g' := Subtype.ext (Units.ext (map_mul (re e) _ _))
def TR (P Q : ℕ) (R : ℝ) : Set (UpqT P Q) := {g | ∑ i, ∑ j, ‖UpqT.mat g i j‖ ^ 2 ≤ R}
end One
def rad (n : ℕ) : ℝ := hs (1 : Matrix (Fin n) (Fin n) ℂ) + 1
def nT {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ε i = true}
def nF {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ¬ ε i = true}
def e0 {n : ℕ} (ε : Fin n → Bool) : Fin (nT ε) ⊕ Fin (nF ε) ≃ Fin n :=
  (Equiv.sumCongr (Fintype.equivFin {i // ε i = true}).symm
    (Fintype.equivFin {i // ¬ ε i = true}).symm).trans (Equiv.sumCompl fun i => ε i = true)
variable (C : CDHaar)
def cdScaleOf (n : ℕ) (ε : Fin n → Bool) : ℝ≥0 :=
  (C.cd (nT ε) (nF ε) (TR (nT ε) (nF ε) (rad n)) / muG ε {a | hsG a ≤ rad n}).toNNReal
end Formalism.BasicNotions.Examples₂.CD


