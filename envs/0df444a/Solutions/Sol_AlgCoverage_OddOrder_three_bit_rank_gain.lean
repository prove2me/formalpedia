-- Prove2me | solution 1 for AlgCoverage.OddOrder.three_bit_rank_gain
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T04:13:48.589025+00:00
-- url     : https://prove2.me/submissions/86768078-78ab-403f-be87-002c410ee400

import Mathlib

abbrev CubeAdj (ε ε' : Fin 3 → Bool) : Prop :=
  ∃ i : Fin 3, ε i ≠ ε' i ∧ ∀ j : Fin 3, j ≠ i → ε j = ε' j

def v000 : Fin 3 → Bool := ![false, false, false]
def v001 : Fin 3 → Bool := ![false, false, true]
def v010 : Fin 3 → Bool := ![false, true, false]
def v011 : Fin 3 → Bool := ![false, true, true]
def v100 : Fin 3 → Bool := ![true, false, false]
def v101 : Fin 3 → Bool := ![true, false, true]
def v110 : Fin 3 → Bool := ![true, true, false]
def v111 : Fin 3 → Bool := ![true, true, true]

def P0 : Finset (Fin 3 → Bool) := {v000, v011, v101, v110}
def P1 : Finset (Fin 3 → Bool) := {v001, v010, v100, v111}

theorem solution {F : Type*} [Field F] (hF : Odd (ringChar F))
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (d r : ℕ)
    (C : W →ₗ[F] (Fin d → F)) (B : Fin 3 → W →ₗ[F] (Fin d → F))
    (hB : ∀ i, r ≤ Module.finrank F (LinearMap.range (B i))) :
    Nat.card {ε : Fin 3 → Bool //
        (Module.finrank F (LinearMap.range (C + ∑ i, if ε i then B i else 0)) : ℝ) < (r : ℝ) / 4}
      ≤ 3 ∧
    (5 : ℝ) / 8 ≤
      (Nat.card {ε : Fin 3 → Bool //
          (r : ℝ) / 4 ≤ (Module.finrank F W : ℝ) -
            Module.finrank F (LinearMap.ker (C + ∑ i, if ε i then B i else 0))} : ℝ) / 8 := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    intro hzero
    have hdvd : ringChar F ∣ 2 := (ringChar.spec F 2).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2c
    · have h1z : (1 : F) = 0 := by
        have := (ringChar.spec F 1).mpr (by rw [h1])
        simpa using this
      exact one_ne_zero h1z
    · rw [h2c] at hF
      exact absurd hF (by decide)
  let V : (Fin 3 → Bool) → W →ₗ[F] (Fin d → F) :=
    fun ε => C + ∑ i, if ε i then B i else 0
  change Nat.card {ε : Fin 3 → Bool //
      (Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4} ≤ 3 ∧
    (5 : ℝ) / 8 ≤
      (Nat.card {ε : Fin 3 → Bool //
          (r : ℝ) / 4 ≤ (Module.finrank F W : ℝ) -
            Module.finrank F (LinearMap.ker (V ε))} : ℝ) / 8
  have hdiff : ∀ (ε ε' : Fin 3 → Bool) (i : Fin 3), (∀ j : Fin 3, j ≠ i → ε j = ε' j) →
      ε i ≠ ε' i → V ε - V ε' = (if ε i then B i else -B i) := by
    intro ε ε' i hoff hne
    show C + (∑ j, if ε j then B j else 0) - (C + ∑ j, if ε' j then B j else 0) = _
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · cases hε : ε i <;> cases hε' : ε' i <;> simp_all
    · intro j _ hji
      rw [hoff j hji]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hrange : ∀ (ε ε' : Fin 3 → Bool) (i : Fin 3), (∀ j : Fin 3, j ≠ i → ε j = ε' j) →
      ε i ≠ ε' i → LinearMap.range (V ε - V ε') = LinearMap.range (B i) := by
    intro ε ε' i hoff hne
    rw [hdiff ε ε' i hoff hne]
    cases hε : ε i
    · simp only [hε, Bool.false_eq_true, if_false]
      exact LinearMap.range_neg (B i)
    · simp only [hε, if_true]
  have hchain : ∀ (ε ε' : Fin 3 → Bool) (i : Fin 3), (∀ j : Fin 3, j ≠ i → ε j = ε' j) →
      ε i ≠ ε' i →
      (r : ℝ) ≤ (Module.finrank F (LinearMap.range (V ε)) : ℝ) +
        Module.finrank F (LinearMap.range (V ε')) := by
    intro ε ε' i hoff hne
    have hrange' := hrange ε ε' i hoff hne
    have hle : LinearMap.range (V ε - V ε') ≤
        (LinearMap.range (V ε) ⊔ LinearMap.range (V ε')) := by
      rintro x ⟨y, rfl⟩
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
        (Submodule.mem_sup_right ⟨y, rfl⟩)
    have hnat : r ≤ Module.finrank F (LinearMap.range (V ε)) +
        Module.finrank F (LinearMap.range (V ε')) := by
      have h1 : r ≤ Module.finrank F (LinearMap.range (B i)) := hB i
      rw [← hrange'] at h1
      have h2 : Module.finrank F (LinearMap.range (V ε - V ε')) ≤
          Module.finrank F ↥(LinearMap.range (V ε) ⊔ LinearMap.range (V ε')) :=
        Submodule.finrank_mono hle
      have h3 : Module.finrank F ↥(LinearMap.range (V ε) ⊔ LinearMap.range (V ε')) ≤
          Module.finrank F (LinearMap.range (V ε)) + Module.finrank F (LinearMap.range (V ε')) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      omega
    exact_mod_cast hnat
  set S : Finset (Fin 3 → Bool) :=
    Finset.univ.filter (fun ε => (Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4)
    with hSdef
  have hSrank : ∀ ε ∈ S, (Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4 := by
    intro ε hε
    rw [hSdef] at hε
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hε
  have hindep : ∀ ε ∈ S, ∀ ε' ∈ S, ¬ CubeAdj ε ε' := by
    intro ε hε ε' hε' hadj
    obtain ⟨i, hne, hoff⟩ := hadj
    have hc := hchain ε ε' i hoff hne
    have h1 := hSrank ε hε
    have h2 := hSrank ε' hε'
    linarith
  have hcube : (Finset.univ.filter (fun S : Finset (Fin 3 → Bool) =>
      (∀ ε ∈ S, ∀ ε' ∈ S, ¬ CubeAdj ε ε') ∧ 4 ≤ S.card)) =
      ({P0, P1} : Finset (Finset (Fin 3 → Bool))) := by
    decide
  have hclass : S.card ≤ 3 ∨ S = P0 ∨ S = P1 := by
    by_cases hc : S.card ≤ 3
    · exact Or.inl hc
    · push Not at hc
      have hmem : S ∈ Finset.univ.filter (fun S : Finset (Fin 3 → Bool) =>
          (∀ ε ∈ S, ∀ ε' ∈ S, ¬ CubeAdj ε ε') ∧ 4 ≤ S.card) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hindep, hc⟩
      rw [hcube] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      exact Or.inr hmem
  have hV000 : V v000 = C := by
    simp [V, v000, Fin.sum_univ_three]
  have hV001 : V v001 = C + B 2 := by
    simp [V, v001, Fin.sum_univ_three]
  have hV010 : V v010 = C + B 1 := by
    simp [V, v010, Fin.sum_univ_three]
  have hV100 : V v100 = C + B 0 := by
    simp [V, v100, Fin.sum_univ_three]
  have hV011 : V v011 = C + B 1 + B 2 := by
    simp [V, v011, Fin.sum_univ_three]
    abel
  have hV101 : V v101 = C + B 0 + B 2 := by
    simp [V, v101, Fin.sum_univ_three]
    abel
  have hV110 : V v110 = C + B 0 + B 1 := by
    simp [V, v110, Fin.sum_univ_three]
    abel
  have hV111 : V v111 = C + B 0 + B 1 + B 2 := by
    simp [V, v111, Fin.sum_univ_three]
    abel
  have hcontra : ∀ (ε1 ε2 ε3 ε4 : Fin 3 → Bool) (i : Fin 3),
      (2 : F) • B i = V ε1 - V ε2 - V ε3 + V ε4 →
      ε1 ∈ S → ε2 ∈ S → ε3 ∈ S → ε4 ∈ S → False := by
    intro ε1 ε2 ε3 ε4 i hid h1 h2m h3 h4
    have hr1 := hSrank ε1 h1
    have hr2 := hSrank ε2 h2m
    have hr3 := hSrank ε3 h3
    have hr4 := hSrank ε4 h4
    set M := LinearMap.range (V ε1) ⊔ LinearMap.range (V ε2) ⊔ LinearMap.range (V ε3) ⊔
      LinearMap.range (V ε4) with hM
    have hle : LinearMap.range ((2 : F) • B i) ≤ M := by
      rw [hM]
      rintro x ⟨y, rfl⟩
      have hy : ((2 : F) • B i) y = V ε1 y + (-(V ε2 y)) + (-(V ε3 y)) + V ε4 y := by
        rw [hid]
        simp only [LinearMap.sub_apply, LinearMap.add_apply]
        abel
      rw [hy]
      exact Submodule.add_mem_sup
        (Submodule.add_mem_sup (Submodule.add_mem_sup ⟨y, rfl⟩ ⟨-y, by simp⟩) ⟨-y, by simp⟩)
        ⟨y, rfl⟩
    have hfr : Module.finrank F (LinearMap.range ((2 : F) • B i)) =
        Module.finrank F (LinearMap.range (B i)) := by
      rw [LinearMap.range_smul _ _ h2]
    have hlow : r ≤ Module.finrank F M := by
      have hb := hB i
      rw [← hfr] at hb
      exact le_trans hb (Submodule.finrank_mono hle)
    have hupper : Module.finrank F M ≤
        Module.finrank F (LinearMap.range (V ε1)) + Module.finrank F (LinearMap.range (V ε2)) +
          Module.finrank F (LinearMap.range (V ε3)) + Module.finrank F (LinearMap.range (V ε4)) := by
      rw [hM]
      have a1 := Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range (V ε1) ⊔ LinearMap.range (V ε2) ⊔ LinearMap.range (V ε3))
        (LinearMap.range (V ε4))
      have a2 := Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range (V ε1) ⊔ LinearMap.range (V ε2)) (LinearMap.range (V ε3))
      have a3 := Submodule.finrank_add_le_finrank_add_finrank
        (LinearMap.range (V ε1)) (LinearMap.range (V ε2))
      omega
    have hlow' : (r : ℝ) ≤ (Module.finrank F M : ℝ) := by exact_mod_cast hlow
    have hupper' : (Module.finrank F M : ℝ) ≤
        (Module.finrank F (LinearMap.range (V ε1)) : ℝ) + Module.finrank F (LinearMap.range (V ε2)) +
          Module.finrank F (LinearMap.range (V ε3)) + Module.finrank F (LinearMap.range (V ε4)) := by
      exact_mod_cast hupper
    linarith
  have hP0 : S ≠ P0 := by
    intro hS
    refine hcontra v110 v000 v011 v101 0 ?_ ?_ ?_ ?_ ?_
    · rw [hV110, hV000, hV011, hV101]
      simp only [two_smul]
      abel
    · rw [hS]; decide
    · rw [hS]; decide
    · rw [hS]; decide
    · rw [hS]; decide
  have hP1 : S ≠ P1 := by
    intro hS
    refine hcontra v111 v001 v100 v010 1 ?_ ?_ ?_ ?_ ?_
    · rw [hV111, hV001, hV100, hV010]
      simp only [two_smul]
      abel
    · rw [hS]; decide
    · rw [hS]; decide
    · rw [hS]; decide
    · rw [hS]; decide
  have hScard : S.card ≤ 3 := by
    rcases hclass with h | h | h
    · exact h
    · exact absurd h hP0
    · exact absurd h hP1
  constructor
  · have hcard : Nat.card {ε : Fin 3 → Bool //
        (Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4} = S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hSdef]
    rw [hcard]
    exact hScard
  · have hpred : ∀ ε : Fin 3 → Bool,
        ((r : ℝ) / 4 ≤ (Module.finrank F W : ℝ) - Module.finrank F (LinearMap.ker (V ε))) ↔
          ¬ ((Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4) := by
      intro ε
      have h := LinearMap.finrank_range_add_finrank_ker (V ε)
      have h' : (Module.finrank F W : ℝ) = (Module.finrank F (LinearMap.range (V ε)) : ℝ) +
          (Module.finrank F (LinearMap.ker (V ε)) : ℝ) := by
        rw [← h]
        push_cast
        ring
      rw [show (Module.finrank F W : ℝ) - (Module.finrank F (LinearMap.ker (V ε)) : ℝ) =
          (Module.finrank F (LinearMap.range (V ε)) : ℝ) by linarith]
      exact not_lt.symm
    have hpcard : Nat.card {ε : Fin 3 → Bool //
        (Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4} = S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hSdef]
    have hqq : Nat.card {ε : Fin 3 → Bool //
        (r : ℝ) / 4 ≤ (Module.finrank F W : ℝ) - Module.finrank F (LinearMap.ker (V ε))} =
        8 - Nat.card {ε : Fin 3 → Bool //
          (Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4} := by
      have hq : Nat.card {ε : Fin 3 → Bool //
          (r : ℝ) / 4 ≤ (Module.finrank F W : ℝ) - Module.finrank F (LinearMap.ker (V ε))} =
          Nat.card {ε : Fin 3 → Bool //
            ¬ ((Module.finrank F (LinearMap.range (V ε)) : ℝ) < (r : ℝ) / 4)} := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun ε => hpred ε)
      rw [hq, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Nat.card_eq_fintype_card]
      congr 1
    rw [hqq, hpcard]
    have h5 : 5 ≤ 8 - S.card := by omega
    have h5' : (5 : ℝ) ≤ ((8 - S.card : ℕ) : ℝ) := by exact_mod_cast h5
    linarith
