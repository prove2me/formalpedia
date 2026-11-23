-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
-- name    : ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:13.991802+00:00
-- url     : https://prove2.me/theorems/806b9de9-06c4-4d8c-bf55-0c23f49bab8c
-- title:
--   Sq Char A
-- statement:
--   Definitions and structural lemmas for Sq Char A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/SqCharA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
def sq_Intl {k : ℕ} (f : Fin k → Fin k → ℕ) : Prop :=
  ∀ l j : Fin k, j.val = l.val + 1 → ∀ a : Fin k,
    (∑ b : Fin k with b ≤ a, f b j) ≤ ∑ b : Fin k with b < a, f b l
def sq_SSZ (k : ℕ) (κ : Fin k → ℤ) : Type :=
  {g : Fin k → Fin k → ℕ // sq_Intl g ∧ ∀ s, ((∑ a, g a s : ℕ) : ℤ) = κ s}
def sq_rowSum {k : ℕ} (g : Fin k → Fin k → ℕ) (a : Fin k) : ℕ := ∑ s, g a s
def sq_mono {K : Type*} [Field K] {k : ℕ} (t : Fin k → K) (g : Fin k → Fin k → ℕ) : K :=
  ∏ a, t a ^ sq_rowSum g a
theorem sq_sum_le_castSucc {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b ≤ a.castSucc, F b) = ∑ b : Fin k with b ≤ a, F b.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp
theorem sq_sum_lt_castSucc {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b < a.castSucc, F b) = ∑ b : Fin k with b < a, F b.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  have : ¬ (Fin.last k < a.castSucc) := not_lt.2 (Fin.le_last _)
  simp [this]
theorem sq_sum_le_last {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b ≤ Fin.last k, F b) = ∑ b, F b := by
  rw [Finset.sum_filter]
  simp [Fin.le_last]
theorem sq_sum_lt_last {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b < Fin.last k, F b) = ∑ b : Fin k, F b.castSucc := by
  rw [Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_lt_last]
theorem sq_mem_interl {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) :
    κ ∈ interl μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  simp [interl, Fintype.mem_piFinset, Finset.mem_Icc]
def sq_restr {k : ℕ} (f : Fin (k + 1) → Fin (k + 1) → ℕ) : Fin k → Fin k → ℕ :=
  fun a t => f a.castSucc t.castSucc
def sq_UU (k : ℕ) (μ : Fin (k + 1) → ℤ) : Type :=
  {g : Fin k → Fin k → ℕ // sq_Intl g ∧ (fun t => ((∑ a, g a t : ℕ) : ℤ)) ∈ interl μ}
theorem sq_restr_mem {k : ℕ} (μ : Fin (k + 1) → ℤ) (f : sq_SSZ (k + 1) μ) :
    sq_Intl (sq_restr f.1) ∧ (fun t => ((∑ a, sq_restr f.1 a t : ℕ) : ℤ)) ∈ interl μ := by
  obtain ⟨f, hI, hs⟩ := f
  refine ⟨?_, ?_⟩
  · intro l j hlj a
    have h := hI l.castSucc j.castSucc (by simpa using hlj) a.castSucc
    rw [sq_sum_le_castSucc, sq_sum_lt_castSucc] at h
    exact h
  · rw [sq_mem_interl]
    intro i
    constructor
    · have h := hI i.castSucc i.succ (by simp) (Fin.last k)
      rw [sq_sum_le_last, sq_sum_lt_last] at h
      rw [← hs i.succ]
      exact_mod_cast h
    · rw [← hs i.castSucc, Fin.sum_univ_castSucc]
      simp only [sq_restr]
      push_cast
      have : (0 : ℤ) ≤ (f (Fin.last k) i.castSucc : ℤ) := Int.natCast_nonneg _
      linarith
def sq_rho {k : ℕ} (μ : Fin (k + 1) → ℤ) (f : sq_SSZ (k + 1) μ) : sq_UU k μ :=
  ⟨sq_restr f.1, sq_restr_mem μ f⟩
def sq_ext {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) : Fin (k + 1) → Fin (k + 1) → ℕ :=
  fun a t => Fin.lastCases (motive := fun _ => ℕ)
    (Fin.lastCases (motive := fun _ => ℕ) (μ (Fin.last k)).toNat
      (fun t' => (μ t'.castSucc - ((∑ b, g b t' : ℕ) : ℤ)).toNat) t)
    (fun a' => Fin.lastCases (motive := fun _ => ℕ) 0 (fun t' => g a' t') t) a
def sq_fibEquiv {k : ℕ} (μ : Fin (k + 1) → ℤ) : sq_UU k μ ≃ Σ κ : ↥(interl μ), sq_SSZ k κ.1 where
  toFun g := ⟨⟨_, g.2.2⟩, ⟨g.1, g.2.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.1, x.2.2.1, by
    have : (fun t => ((∑ a, x.2.1 a t : ℕ) : ℤ)) = x.1.1 := funext x.2.2.2
    rw [this]; exact x.1.2⟩
  left_inv g := rfl
  right_inv x := by
    obtain ⟨⟨κ, hκ⟩, ⟨g, hI, hs⟩⟩ := x
    have : (fun t => ((∑ a, g a t : ℕ) : ℤ)) = κ := funext hs
    subst this
    rfl
end ReciprocityTheory.ChartRestriction.TR.Weyl


