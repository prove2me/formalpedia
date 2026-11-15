-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV5
-- name    : RPLib_S3_EllW2MV5
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:27:15.456195+00:00
-- url     : https://prove2.me/theorems/674d2698-82b6-44db-924b-aa79b5eb6992
-- title:
--   The Eichler-Selberg trace formula in weight two: counting an arithmetic progression
-- statement:
--   Counting an arithmetic progression.
--
--   * `cntI m a r I = #{i ∈ [1, I] : a i ≡ r (mod m)}`.
--   * `cntI_add_eq` (`a ⊥ m`): `cntI + ε₁ = (I+1)/m + ε₂` with `ε₁, ε₂ ≤ 1` (`Nat.count_modEq_card`).
--   * **`abs_cntI_sub_le`** (`a ⊥ m`): `|cntI m a r I − I/m| ≤ 2`.
--   * `tendsto_div_of_abs_sub_le`: `|f N − c N| ≤ C` for all `N` gives `f N / N → c`.
--   * **`tendsto_cntI_div`** (`a ⊥ m`, `0 < b`): `cntI m a r (N/b) / N → 1/(b m)`.
--   * `card_dvd_filter_eq` (`0 < j`): `#{k ∈ [1,K] : j ∣ k ∧ h k ≡ r} = cntI m (h j) r (K/j)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib

/-!
# S3-ES-Wt2 (O6, file MV5): counting an arithmetic progression

* `cntI m a r I = #{i ∈ [1, I] : a i ≡ r (mod m)}`.
* `cntI_add_eq` (`a ⊥ m`): `cntI + ε₁ = (I+1)/m + ε₂` with `ε₁, ε₂ ≤ 1` (`Nat.count_modEq_card`).
* **`abs_cntI_sub_le`** (`a ⊥ m`): `|cntI m a r I − I/m| ≤ 2`.
* `tendsto_div_of_abs_sub_le`: `|f N − c N| ≤ C` for all `N` gives `f N / N → c`.
* **`tendsto_cntI_div`** (`a ⊥ m`, `0 < b`): `cntI m a r (N/b) / N → 1/(b m)`.
* `card_dvd_filter_eq` (`0 < j`): `#{k ∈ [1,K] : j ∣ k ∧ h k ≡ r} = cntI m (h j) r (K/j)`.
-/

open Finset Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- `#{i ∈ [1, I] : a i ≡ r (mod m)}`. -/
def cntI (m a : ℕ) (r : ZMod m) (I : ℕ) : ℕ := #{i ∈ Icc 1 I | ((a * i : ℕ) : ZMod m) = r}

lemma card_Icc_filter_add (P : ℕ → Prop) [DecidablePred P] (I : ℕ) :
    #{i ∈ Icc 1 I | P i} + (if P 0 then 1 else 0) = #{i ∈ range (I + 1) | P i} := by
  have hR : range (I + 1) = insert 0 (Icc 1 I) := by
    ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hR, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]

lemma cntI_add_eq {m : ℕ} [NeZero m] {a : ℕ} (ha : a.Coprime m) (r : ZMod m) (I : ℕ) :
    ∃ e₁ e₂ : ℕ, e₁ ≤ 1 ∧ e₂ ≤ 1 ∧ cntI m a r I + e₁ = (I + 1) / m + e₂ := by
  set s : ℕ := (((ZMod.unitOfCoprime a ha)⁻¹ : (ZMod m)ˣ) * r : ZMod m).val with hs
  have hu : ((ZMod.unitOfCoprime a ha : (ZMod m)ˣ) : ZMod m) = a := ZMod.coe_unitOfCoprime a ha
  have hP : ∀ i : ℕ, ((a * i : ℕ) : ZMod m) = r ↔ i ≡ s [MOD m] := by
    intro i
    rw [← ZMod.natCast_eq_natCast_iff, hs, ZMod.natCast_zmod_val, Nat.cast_mul]
    constructor
    · intro h; rw [← h, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h; rw [h, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨if ((a * 0 : ℕ) : ZMod m) = r then 1 else 0, if s % m < (I + 1) % m then 1 else 0,
    by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
  rw [cntI, card_Icc_filter_add (fun i => ((a * i : ℕ) : ZMod m) = r),
    ← Nat.count_modEq_card (I + 1) (NeZero.pos m) s, Nat.count_eq_card_filter_range]
  congr 1
  ext i
  simp only [Finset.mem_filter, hP]

/-- **MV5**: `|#{i ∈ [1, I] : a i ≡ r (m)} − I/m| ≤ 2` for `a ⊥ m`. -/
theorem abs_cntI_sub_le {m : ℕ} [NeZero m] {a : ℕ} (ha : a.Coprime m) (r : ZMod m) (I : ℕ) :
    |(cntI m a r I : ℝ) - I / m| ≤ 2 := by
  obtain ⟨e1, e2, h1, h2, h⟩ := cntI_add_eq ha r I
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.one_le
  set Q := (I + 1) / m with hQ
  have hQ1 : Q * m ≤ I + 1 := Nat.div_mul_le_self _ _
  have hQ2 : I + 1 < (Q + 1) * m := by
    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (NeZero.pos m)
  have hc : (cntI m a r I : ℝ) = Q + e2 - e1 := by
    have h' : ((cntI m a r I + e1 : ℕ) : ℝ) = ((Q + e2 : ℕ) : ℝ) := by rw [h]
    push_cast at h'; linarith
  have hQ1' : (Q : ℝ) * m ≤ I + 1 := by exact_mod_cast hQ1
  have hQ2' : (I : ℝ) + 1 < (Q + 1) * m := by exact_mod_cast hQ2
  have he1 : (e1 : ℝ) ≤ 1 := by exact_mod_cast h1
  have he2 : (e2 : ℝ) ≤ 1 := by exact_mod_cast h2
  have he1' : (0 : ℝ) ≤ e1 := Nat.cast_nonneg _
  have he2' : (0 : ℝ) ≤ e2 := Nat.cast_nonneg _
  have hlo : (I : ℝ) / m < Q + 1 := by rw [div_lt_iff₀ hm]; linarith
  have hhi : (Q : ℝ) - 1 ≤ I / m := by rw [le_div_iff₀ hm, sub_mul, one_mul]; linarith
  rw [hc, abs_le]
  constructor <;> linarith

lemma tendsto_div_of_abs_sub_le {f : ℕ → ℝ} {c C : ℝ} (h : ∀ N : ℕ, |f N - c * N| ≤ C) :
    Tendsto (fun N : ℕ => f N / N) atTop (𝓝 c) := by
  have h1 : Tendsto (fun N : ℕ => (f N - c * N) / N) atTop (𝓝 0) := by
    have hC : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [eventually_gt_atTop 0] with N _
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (h N) (Nat.cast_nonneg _)
  have h2 : ∀ᶠ N : ℕ in atTop, (f N - c * N) / N + c = f N / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    first | (field_simp; ring) | field_simp
  have h3 := h1.add_const c
  rw [zero_add] at h3
  exact h3.congr' h2

/-- `cntI m a r (N/b) / N → 1/(b m)` for `a ⊥ m`, `0 < b`. -/
theorem tendsto_cntI_div {m : ℕ} [NeZero m] {a : ℕ} (ha : a.Coprime m) (r : ZMod m) {b : ℕ}
    (hb : 0 < b) :
    Tendsto (fun N : ℕ => (cntI m a r (N / b) : ℝ) / N) atTop (𝓝 (1 / (b * m))) := by
  refine tendsto_div_of_abs_sub_le (C := 3) fun N => ?_
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.one_le
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := abs_cntI_sub_le ha r (N / b)
  have hD1 : ((N / b : ℕ) : ℝ) * b ≤ N := by exact_mod_cast Nat.div_mul_le_self N b
  have hD2 : (N : ℝ) < ((N / b : ℕ) + 1 : ℝ) * b := by
    have : N < (N / b + 1) * b := by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hb
    exact_mod_cast this
  have hE : |((N / b : ℕ) : ℝ) / m - 1 / (b * m) * N| ≤ 1 := by
    have he : ((N / b : ℕ) : ℝ) / m - 1 / (b * m) * N = (((N / b : ℕ) : ℝ) * b - N) / (b * m) := by
      first | (field_simp; ring) | field_simp
    rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < b * m), div_le_one (by positivity),
      abs_le]
    have hbm : (b : ℝ) ≤ b * m := le_mul_of_one_le_right hb'.le hm1
    constructor <;> nlinarith
  calc |(cntI m a r (N / b) : ℝ) - 1 / (b * m) * N|
      = |((cntI m a r (N / b) : ℝ) - ((N / b : ℕ) : ℝ) / m) +
          (((N / b : ℕ) : ℝ) / m - 1 / (b * m) * N)| := by congr 1; ring
    _ ≤ |(cntI m a r (N / b) : ℝ) - ((N / b : ℕ) : ℝ) / m| +
          |((N / b : ℕ) : ℝ) / m - 1 / (b * m) * N| := abs_add_le _ _
    _ ≤ 2 + 1 := add_le_add h1 hE
    _ = 3 := by norm_num

/-- Multiples of `j` in `[1, K]`, in a residue class. -/
lemma card_dvd_filter_eq (m h j K : ℕ) (hj : 0 < j) (r : ZMod m) :
    #{k ∈ Icc 1 K | j ∣ k ∧ ((h * k : ℕ) : ZMod m) = r} = cntI m (h * j) r (K / j) := by
  rw [cntI]
  refine Finset.card_nbij' (fun k => k / j) (fun i => j * i) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨h1, h2⟩, ⟨t, rfl⟩, h3⟩ := hk
    rw [Nat.mul_div_cancel_left t hj]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos t with ht | ht
      · rw [ht, mul_zero] at h1; omega
      · exact ht
    · rw [Nat.le_div_iff_mul_le hj, mul_comm]; exact h2
    · rw [mul_assoc]; exact h3
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hi
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
      dvd_mul_right j i, ?_⟩
    · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hj).1 h2
    · rw [← mul_assoc]; exact h3
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter] at hk
    exact Nat.mul_div_cancel' hk.2.1
  · intro i _
    exact Nat.mul_div_cancel_left i hj

end RamanujanPetersson.EllW2


