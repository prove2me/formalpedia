-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviRadicalProductLengthOfLatticeSteps
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviRadicalProductLengthOfLatticeSteps
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:05.049152+00:00
-- url     : https://prove2.me/theorems/9301f8fd-e65a-4803-bbdd-bf75111748eb
-- title:
--   Levi Radical Product Length Of Lattice Steps
-- statement:
--   Definitions and structural lemmas for Levi Radical Product Length Of Lattice Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeviRadicalProductLengthOfLatticeSteps.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_len_eq
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_hasLen_of_latLen
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
theorem exists_eq_exp_of_ne {x : WithZero (Multiplicative ℤ)} (h : x ≠ 0) : ∃ m : ℤ, x = WithZero.exp m :=
  ⟨x.log, (WithZero.exp_log h).symm⟩
theorem exp_mul_le_exp_iff {x : WithZero (Multiplicative ℤ)} {s k : ℤ} :
    WithZero.exp s * x ≤ WithZero.exp k ↔ x ≤ WithZero.exp (k - s) := by
  by_cases h : x = 0
  · subst h; simp
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega
theorem exp_succ_le_of_not_le {x : WithZero (Multiplicative ℤ)} {k : ℤ} (h : ¬ x ≤ WithZero.exp k) :
    WithZero.exp (k + 1) ≤ x := by
  by_cases h0 : x = 0
  · subst h0; exact absurd zero_le h
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    rw [WithZero.exp_le_exp] at h ⊢
    omega
theorem exists_le_exp_add (x : WithZero (Multiplicative ℤ)) (k₀ : ℤ) : ∃ e : ℕ, x ≤ WithZero.exp (k₀ + e) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    exact ⟨(m - k₀).toNat, WithZero.exp_le_exp.2 (by omega)⟩
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
theorem v_pow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul]; congr 1; simp
theorem v_zpow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; congr 1; simp
theorem pow_mul_mem_intL_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) (x : L) :
    ϖ ^ k * x ∈ intL L ↔ Valued.v x ≤ WithZero.exp (k : ℤ) := by
  show Valued.v (ϖ ^ k * x) ≤ 1 ↔ _
  rw [map_mul, v_pow_unif hϖ, ← WithZero.exp_zero, exp_mul_le_exp_iff]
  simp
section Entries
variable {σ : L →+* L} {N : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem leviElt_mul_rad_entries {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m u : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m)
    (hu : u ∈ radQ σ N) :
    mat (m * u) 0 0 = ϖ ^ a ∧ (∀ j, mat (m * u) 0 (mid j) = ϖ ^ a * rowOf u j) ∧
    mat (m * u) 0 (Fin.last (N + 1)) = ϖ ^ a * cornerOf u ∧
    (∀ i, mat (m * u) (mid i) 0 = 0) ∧ (∀ i j, mat (m * u) (mid i) (mid j) = mat g₀ i j) ∧
    (∀ i, mat (m * u) (mid i) (Fin.last (N + 1)) = (mat g₀ *ᵥ colOf u) i) ∧
    mat (m * u) (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, mat (m * u) (Fin.last (N + 1)) (mid j) = 0) ∧
    mat (m * u) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := by
  obtain ⟨hmz, h00, hll, hmm⟩ := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hmz
  have hu' : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  have m0m : ∀ j, mat m 0 (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have m0l : mat m 0 (Fin.last (N + 1)) = 0 := hmz' _ _ (by simp)
  have mm0 : ∀ i, mat m (mid i) 0 = 0 := fun i => hmz' _ _ (by simp)
  have mml : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0 := fun i => hmz' _ _ (by simp)
  have ml0 : mat m (Fin.last (N + 1)) 0 = 0 := hmz' _ _ (by simp)
  have mlm : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have u00 : mat u 0 0 = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  have um0 : ∀ i, mat u (mid i) 0 = 0 := fun i => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  have ul0 : mat u (Fin.last (N + 1)) 0 = 0 := by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  have hu_mm : ∀ i j, mat u (mid i) (mid j) = if i = j then 1 else 0 := fun i j => by
    rw [hu' _ _ (by simp), Matrix.one_apply]; simp [mid_injective.eq_iff]
  have ulm : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0 := fun j => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (fun h => mid_ne_last j h.symm)]
  have ull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  simp only [mat_mul, Matrix.mul_apply, sum_idx]
  refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩ <;>
    simp [m0m, m0l, mm0, mml, ml0, mlm, u00, um0, ul0, hu_mm, ulm, ull, h00, hll, hmm, rowOf, colOf, cornerOf,
      Matrix.mulVec, dotProduct]
end Entries
theorem pointwise_of_steps (hA : AddVec) (hD : Dual) (hS : SpanEq) (hH : Heis) : Pointwise := by
  intro L _ _ ϖ σ q N hU a g₀ m hm U V C l hf hl u hu
  classical
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨e00, e0m, e0l, em0, emm, eml, el0, elm, ell⟩ := leviElt_mul_rad_entries hm hu
  have hrb : ∀ j, rowOf u j = -σ (colOf u j.rev) := ((hH L ϖ σ q N hU).1 u hu).1

  let Q : ℕ → Prop := fun e => ∀ j, Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)
  have hQD : ∀ e, Q e ↔
      (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∧
      ∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun e => by
    have := hD L ϖ σ q N hU g₀ U V C hf (rowOf u) (colOf u) (ϖ ^ (a.toNat + e)) hrb
    simp only [pow_mul_mem_intL_iff hϖ] at this
    exact this
  have hQex : ∃ e, Q e := by
    choose f hf' using fun j => exists_le_exp_add (Valued.v ((rowOf u ᵥ* C) j)) (a.toNat : ℤ)
    obtain ⟨M, hM⟩ := Finite.exists_le f
    exact ⟨M, fun j => (hf' j).trans (WithZero.exp_le_exp.2 (by have := hM j; push_cast; omega))⟩
  let e := Nat.find hQex
  have hQe : Q e := Nat.find_spec hQex
  have hQmono : ∀ e', Q e' ↔ e ≤ e' := fun e' =>
    ⟨fun h => Nat.find_min' hQex h, fun h j => (hQe j).trans (WithZero.exp_le_exp.2 (by push_cast; omega))⟩
  have hnQ : 0 < e → ¬ Q (e - 1) := fun he h => by have := (hQmono _).1 h; omega
  have hsucc : 0 < e → ((a.toNat + (e - 1) : ℕ) : ℤ) + 1 = ((a.toNat + e : ℕ) : ℤ) := fun he => by omega
  have hQsharp : 0 < e → ∃ j, Valued.v ((rowOf u ᵥ* C) j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun he => by
    obtain ⟨j, hj⟩ := not_forall.1 (hnQ he)
    refine ⟨j, le_antisymm (hQe j) ?_⟩
    have := exp_succ_le_of_not_le hj
    rwa [hsucc he] at this

  let y : L := ϖ ^ (-((a.toNat + e : ℕ) : ℤ))
  have hy : Valued.v y = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := by rw [v_zpow_unif hϖ, neg_neg]
  obtain ⟨h2, h3⟩ := (hQD e).1 hQe
  have h4 : Valued.v y = WithZero.exp (a.toNat : ℤ) ∨
      (∃ i, Valued.v y = Valued.v (((C * V * mat g₀) *ᵥ colOf u) i)) ∨
      ∃ i, Valued.v y = Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) := by
    rcases Nat.eq_zero_or_pos e with he | he
    · left; rw [hy, he]; rfl
    · right
      have hn := hnQ he
      rw [hQD] at hn
      rcases not_and_or.1 hn with hn | hn
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inl ⟨i, by rw [hy]; exact le_antisymm this (h2 i)⟩
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inr ⟨i, by rw [hy]; exact le_antisymm this (h3 i)⟩
  obtain ⟨P, ρ, hPdet, hρ0, hρm, hρl, hlat⟩ :=
    hS L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u) (colOf u) (cornerOf u) y hϖ hf e00 e0m e0l em0 emm eml el0 elm
      ell (by rw [hy, WithZero.exp_le_exp]; push_cast; omega) (fun i => by rw [hy]; exact h2 i)
      (fun i => by rw [hy]; exact h3 i) h4
  obtain ⟨c', hc'⟩ : ∃ c', c' = cornerOf u - rowOf u ⬝ᵥ ((C * V * mat g₀) *ᵥ colOf u) := ⟨_, rfl⟩
  rw [← hc'] at hρl
  have hPdet' : Valued.v P.det = WithZero.exp ((a.natAbs + l + e : ℕ) : ℤ) := by
    rw [hPdet, hl, hy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1; simp only [Nat.cast_add]; omega
  have hvm : ∀ j (k : ℤ), Valued.v (ρ (mid j)) ≤ WithZero.exp k ↔
      Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp (k + a.toNat) := fun j k => by
    rw [hρm, map_mul, v_pow_unif hϖ, exp_mul_le_exp_iff, sub_neg_eq_add]
  have hvl : Valued.v (ρ (Fin.last (N + 1))) = WithZero.exp (-((2 * a.toNat + e : ℕ) : ℤ)) * Valued.v c' := by
    rw [hρl, map_div₀, map_mul, v_pow_unif hϖ, hy, div_eq_mul_inv, ← WithZero.exp_neg, mul_comm, ← mul_assoc,
      ← WithZero.exp_add]
    congr 2; push_cast; ring
  have hvl' : ∀ k : ℤ, Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp k ↔
      Valued.v c' ≤ WithZero.exp (k + ((2 * a.toNat + e : ℕ) : ℤ)) := fun k => by
    rw [hvl, exp_mul_le_exp_iff, sub_neg_eq_add]

  let R : ℕ → Prop := fun e₂ => e ≤ e₂ ∧ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp (e₂ : ℤ)
  have hRex : ∃ e₂, R e₂ := by
    obtain ⟨k, hk⟩ := exists_le_exp_add (Valued.v (ρ (Fin.last (N + 1)))) (e : ℤ)
    exact ⟨e + k, by omega, by rwa [Nat.cast_add]⟩
  let e₂ := Nat.find hRex
  have hRe₂ : R e₂ := Nat.find_spec hRex
  have hbound : ∀ i, Valued.v (ρ i) ≤ WithZero.exp (e₂ : ℤ) := fun i => by
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · rw [hρ0, map_zero]; exact zero_le
    · rw [hvm]
      exact (hQe j).trans (WithZero.exp_le_exp.2 (by have := hRe₂.1; push_cast; omega))
    · exact hRe₂.2
  have hsharp : e₂ = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e₂ : ℤ) := by
    by_cases h : e₂ = e
    · rcases Nat.eq_zero_or_pos e with he | he
      · left; omega
      · right
        obtain ⟨j, hj⟩ := hQsharp he
        refine ⟨mid j, ?_⟩
        rw [hρm, map_mul, v_pow_unif hϖ, hj, ← WithZero.exp_add, h]
        congr 1; push_cast; ring
    · right
      have hlt : e < e₂ := lt_of_le_of_ne hRe₂.1 (Ne.symm h)
      have hn : ¬ R (e₂ - 1) := Nat.find_min hRex (by omega)
      have hn' : ¬ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp ((e₂ - 1 : ℕ) : ℤ) := fun h' =>
        hn ⟨by omega, h'⟩
      refine ⟨Fin.last (N + 1), le_antisymm hRe₂.2 ?_⟩
      have := exp_succ_le_of_not_le hn'
      rwa [show ((e₂ - 1 : ℕ) : ℤ) + 1 = (e₂ : ℤ) by omega] at this
  have hLat := hA L (N + 2) P ((a.natAbs + l + e : ℕ) : ℤ) ρ e₂ hPdet' hbound hsharp
  rw [← hlat] at hLat
  have hlen : len (mat (m * u)) = a.natAbs + l + e + e₂ :=
    (hasLen_of_latLen (k := a.natAbs + l + e + e₂) (by convert hLat using 1; push_cast; ring)).len_eq
  rw [hlen]
  refine ⟨by omega, fun j => ?_⟩
  have hsm : Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔
      e ≤ j / 2 ∧ Valued.v c' ≤ WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ) := by
    unfold Small
    rw [← hc']
    simp only [pow_mul_mem_intL_iff hϖ]
    exact and_congr (hQmono (j / 2)) Iff.rfl
  rw [hsm]
  constructor
  · intro h
    have h1 := hRe₂.1
    refine ⟨by omega, ?_⟩
    refine ((hvl' _).1 hRe₂.2).trans (WithZero.exp_le_exp.2 ?_)
    push_cast; omega
  · rintro ⟨h1, h2⟩
    have hR : R (j - e) := ⟨by omega, (hvl' _).2 (h2.trans_eq (by congr 1; push_cast; omega))⟩
    have := Nat.find_min' hRex hR
    omega
example : AddVec → Dual → SpanEq → Heis → Pointwise := pointwise_of_steps
end GlobalTheory.InertZeta


