-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:32.752796+00:00
-- url     : https://prove2.me/theorems/bd520e1c-6ff3-4014-ab44-ee344548873a
-- title:
--   Diag Mat Lower
-- statement:
--   Definitions and structural lemmas for Diag Mat Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DiagMatLower.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
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
def zar (k σ : Type) [Field k] : TopologicalSpace (σ → k) :=
  .generateFrom {s | ∃ p : MvPolynomial σ k, s = {x | MvPolynomial.eval x p ≠ 0}}
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def Cut (j d : ℕ) (c a : Fin d) : Prop := (a : ℕ) < j ∧ j ≤ (c : ℕ) ∧ ((a : ℕ) = 0 ∨ (c : ℕ) + 1 = d)
instance (j d : ℕ) (c a : Fin d) : Decidable (Cut j d c a) := by unfold Cut; infer_instance
variable (k V) in

def LocIdx (j : ℕ) : Type :=
  Σ i, {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1 ∧ ¬ Cut j _ p.1 p.2}
instance [Fintype ι] (j : ℕ) : Fintype (LocIdx k V j) := by
  unfold LocIdx
  infer_instance
def LocIdx.ent {j : ℕ} (u : LocIdx k V j → k) (i : ι) (c a : Fin (finrank k (V i))) : k :=
  if h : a < c ∧ ¬ Cut j _ c a then u ⟨i, (c, a), h⟩ else 0
theorem LocIdx.ent_eq_zero {j : ℕ} (u : LocIdx k V j → k) {i : ι} {c a : Fin (finrank k (V i))}
    (h : ¬ (a < c ∧ ¬ Cut j _ c a)) : LocIdx.ent u i c a = 0 := dif_neg h
def offMat {j : ℕ} (u : LocIdx k V j → k) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => if c = a then 1 else if (a : ℕ) < j ∧ j ≤ (c : ℕ) then LocIdx.ent u i c a else 0
def diagMat {j : ℕ} (u : LocIdx k V j → k) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun c a => if c = a then 1 else if ((a : ℕ) < j ↔ (c : ℕ) < j) then LocIdx.ent u i c a else 0
theorem offMat_lower {j : ℕ} (u : LocIdx k V j → k) (i : ι) :
    (offMat u i).BlockTriangular OrderDual.toDual := by
  intro c a h
  have h' : c < a := h
  simp only [offMat, if_neg (ne_of_lt h')]
  split_ifs
  · exact LocIdx.ent_eq_zero u fun h2 => absurd h2.1 (not_lt.2 h'.le)
  · rfl
theorem diagMat_lower {j : ℕ} (u : LocIdx k V j → k) (i : ι) :
    (diagMat u i).BlockTriangular OrderDual.toDual := by
  intro c a h
  have h' : c < a := h
  simp only [diagMat, if_neg (ne_of_lt h')]
  split_ifs
  · exact LocIdx.ent_eq_zero u fun h2 => absurd h2.1 (not_lt.2 h'.le)
  · rfl
theorem det_chartMat {j : ℕ} (u : LocIdx k V j → k) (i : ι) : (offMat u i * diagMat u i).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_of_lowerTriangular _ (offMat_lower u i),
    Matrix.det_of_lowerTriangular _ (diagMat_lower u i)]
  simp [offMat, diagMat]
def chartGL {j : ℕ} (u : LocIdx k V j → k) (i : ι) : GL (Fin (finrank k (V i))) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (offMat u i * diagMat u i) (by rw [det_chartMat]; exact one_ne_zero)
def locChart (j : ℕ) (b : Frames k V) (u : LocIdx k V j → k) : Flags k V :=
  Frames.flags (show Frames k V from fun i => GlobalTheory.basisMulGL (b i) (chartGL u i))
def bigCell (b : Frames k V) : Set (Flags k V) :=
  {F | ∀ i (m : ℕ), Disjoint (F.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)}))}
def Adapted (A B : ∀ i, Submodule k (V i)) (b : Frames k V) : Prop :=
  ∀ i (a : Fin (finrank k (V i))), ((a : ℕ) = 0 → b i a ∈ A i) ∧ ((a : ℕ) + 1 < finrank k (V i) → b i a ∈ B i)
example (j : ℕ) (b : Frames k V) : locChart j b 0 = b.flags := by
  have h0 (i : ι) (c a : Fin (finrank k (V i))) : LocIdx.ent (0 : LocIdx k V j → k) i c a = 0 := by
    unfold LocIdx.ent; split_ifs <;> rfl
  have h1 (i : ι) : offMat (0 : LocIdx k V j → k) i = 1 := by
    ext c a; simp only [offMat, h0, Matrix.one_apply]; split_ifs <;> rfl
  have h2 (i : ι) : diagMat (0 : LocIdx k V j → k) i = 1 := by
    ext c a; simp only [diagMat, h0, Matrix.one_apply]; split_ifs <;> rfl
  have h (i : ι) : chartGL (0 : LocIdx k V j → k) i = 1 :=
    Units.ext (by simp [chartGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, h1, h2])
  unfold locChart
  simp only [h, GlobalTheory.basisMulGL_one]
end GlobalTheory.FlagPts


