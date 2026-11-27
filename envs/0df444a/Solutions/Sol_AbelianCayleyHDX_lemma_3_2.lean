-- Prove2me | solution 1 for AbelianCayleyHDX.lemma_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:43:02.104832+00:00
-- url     : https://prove2.me/submissions/70c488c6-bb22-4ef8-97d8-e220e47e76a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AbelianCayleyHDX_tower_evaluation_data
import Theorems.Thm_AbelianCayleyHDX_lemma_4_5
import Theorems.Thm_AbelianCayleyHDX_binomial_bounds
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_Delta
import Definitions.Def_AbelianCayleyHDX_affineSpace
import Definitions.Def_AbelianCayleyHDX_encFVec
import Definitions.Def_HMBinPacking_OutputsWithin
open Filter RSListDecodingCapacity.AllRates

open AbelianCayleyHDX in
theorem solution (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧ (∀ j, 1 ≤ t j) ∧
      ∃ D : ∀ j, Finset (PG (t j) F),
        (∀ j, IsSpanning (D j) ∧ ((D j).card : ℝ) ≤ C * (t j : ℝ) ∧
          ((2 : ℝ) ^ h - 5) * ((D j).card : ℝ) ≤ ((2 : ℝ) ^ h - 2) * (Delta (D j) : ℝ) ∧
          (2 : ℝ) ^ ((t j : ℝ) / 3) ≤ (Module.finrank F (affineSpace (D j)) : ℝ)) ∧
        ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
          ∃ p : Polynomial ℕ, ∀ j, ∃ reps : List (Fin (t j) → F),
            reps.length = (D j).card ∧
            (∀ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha ∈ D j) ∧
            (∀ d ∈ D j, ∃ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha = d) ∧
            HMBinPacking.OutputsWithin M (encNat j) (encNat (t j) ++ encList (encFVec enc) reps)
              (p.eval (t j)) := by
  classical
  obtain ⟨hbin1, g₀, hg₀⟩ := binomial_bounds
  obtain ⟨g, hg, hgge, e, L, hprop, hmach⟩ := tower_evaluation_data h hq F hF g₀
  have hne : ∀ j a, e j a ≠ 0 := fun j => (hprop j).2.1
  let D : ∀ j, Finset (PG (2 * g j + 1) F) := fun j =>
    Finset.univ.image fun a => Projectivization.mk F (e j a) (hne j a)
  have hinj : ∀ j, Function.Injective fun a => Projectivization.mk F (e j a) (hne j a) := by
    intro j a b hab
    by_contra hab'
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F _ _ (hne j a) (hne j b)).1 hab
    exact (hprop j).2.2.1 a b hab' c hc.symm
  have hcardD : ∀ j, (D j).card = (2 ^ h - 2) * g j := by
    intro j; simp only [D]
    rw [Finset.card_image_of_injective _ (hinj j), Finset.card_univ, Fintype.card_fin]
  -- representatives
  have hrep : ∀ j a, ∃ u : Fˣ, (Projectivization.mk F (e j a) (hne j a)).rep = (u : F) • e j a := by
    intro j a
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep F (e j a) (hne j a)
    exact ⟨u, by rw [← hu, Units.smul_def]⟩
  have h8 : (8 : ℝ) ≤ 2 ^ h := by exact_mod_cast hq
  refine ⟨2 ^ h, by positivity, fun j => 2 * g j + 1, ?_, fun j => by show 1 ≤ 2 * g j + 1; omega, D, fun j => ?_, ?_⟩
  · -- `t_j → ∞`
    exact tendsto_atTop_mono (fun j => by omega) hg
  · obtain ⟨hspan, -, -, hzero, hrank, hli⟩ := hprop j
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- spanning
      unfold IsSpanning
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      obtain ⟨u, hu⟩ := hrep j a
      have hmem : (Projectivization.mk F (e j a) (hne j a)).rep ∈
          Submodule.span F ((fun d : PG (2 * g j + 1) F => d.rep) '' (D j : Set _)) :=
        Submodule.subset_span ⟨_, by simp [D], rfl⟩
      rw [hu] at hmem
      have := Submodule.smul_mem _ ((u : F)⁻¹) hmem
      rwa [smul_smul, inv_mul_cancel₀ u.ne_zero, one_smul] at this
    · -- size
      rw [hcardD]
      push_cast
      rw [Nat.cast_sub (by omega)]
      push_cast
      have : (0 : ℝ) ≤ g j := by positivity
      nlinarith
    · -- relative distance
      have hΔ : (2 ^ h - 5) * g j ≤ Delta (D j) := by
        apply le_csInf
        · refine ⟨_, LinearMap.proj (R := F) (φ := fun _ : Fin (2 * g j + 1) => F) ⟨0, by omega⟩,
            ?_, rfl⟩
          intro h0
          have := LinearMap.congr_fun h0 (Pi.single ⟨0, by omega⟩ 1)
          simp at this
        · rintro k ⟨c, hc, rfl⟩
          have hfilt : ((D j).filter (fun d => c d.rep ≠ 0)).card =
              (Finset.univ.filter fun a => c (e j a) ≠ 0).card := by
            simp only [D]
            rw [Finset.filter_image, Finset.card_image_of_injective _ (hinj j)]
            congr 1
            ext a
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
            obtain ⟨u, hu⟩ := hrep j a
            rw [hu, map_smul, smul_eq_mul]
            exact ⟨fun h1 h2 => h1 (by rw [h2, mul_zero]), fun h1 h2 => h1
              ((mul_eq_zero.1 h2).resolve_left u.ne_zero)⟩
          rw [hfilt]
          have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
            (fun a : Fin ((2 ^ h - 2) * g j) => c (e j a) = 0)
          simp only [Finset.card_univ, Fintype.card_fin] at hsplit
          have hz := hzero c hc
          have : (2 ^ h - 5) * g j + 3 * g j = (2 ^ h - 2) * g j := by
            rw [← add_mul]; congr 1; omega
          have e2 : (Finset.univ.filter fun a => c (e j a) ≠ 0) =
              Finset.univ.filter fun a => ¬ c (e j a) = 0 := rfl
          rw [e2]
          omega
      rw [hcardD]
      have hΔr : (((2 ^ h - 5) * g j : ℕ) : ℝ) ≤ Delta (D j) := by exact_mod_cast hΔ
      push_cast at hΔr ⊢
      rw [Nat.cast_sub (by omega)] at hΔr ⊢
      push_cast at hΔr ⊢
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ h - 2 := by linarith
      calc ((2 : ℝ) ^ h - 5) * (((2 : ℝ) ^ h - 2) * g j)
          = ((2 : ℝ) ^ h - 2) * (((2 : ℝ) ^ h - 5) * g j) := by ring
        _ ≤ ((2 : ℝ) ^ h - 2) * (Delta (D j) : ℝ) := mul_le_mul_of_nonneg_left hΔr h0
    · -- many affine functions
      have hmemA : ∀ J : {J : Finset (Fin (3 * (g j / 4))) // J.card = g j / 4},
          (fun x : Fin (2 * g j + 1) → F =>
            (Matrix.of fun i l => L j i (J.1.orderEmbOfFin J.2 l) x).det) ∈ affineSpace (D j) := by
        intro J
        apply (lemma_4_5 (L j)).2 (D j) _ J.1 J.2
        intro d hd
        simp only [D, Finset.mem_image, Finset.mem_univ, true_and] at hd
        obtain ⟨a, rfl⟩ := hd
        obtain ⟨u, z, huz⟩ := hrank a
        exact ⟨e j a, hne j a, u, z, rfl, huz⟩
      let fam : {J : Finset (Fin (3 * (g j / 4))) // J.card = g j / 4} → affineSpace (D j) :=
        fun J => ⟨_, hmemA J⟩
      have hli' : LinearIndependent F fam := by
        apply LinearIndependent.of_comp (affineSpace (D j)).subtype
        exact hli
      have hcard := hli'.fintype_card_le_finrank
      rw [Fintype.card_finset_len, Fintype.card_fin] at hcard
      have hb := hg₀ (g j) (hgge j)
      have hb1 := hbin1 (g j / 4)
      have hc : ((Nat.choose (3 * (g j / 4)) (g j / 4) : ℕ) : ℝ) ≤
          (Module.finrank F (affineSpace (D j)) : ℝ) := by exact_mod_cast hcard
      calc (2 : ℝ) ^ (((2 * g j + 1 : ℕ) : ℝ) / 3)
          ≤ (27 / 4 : ℝ) ^ (g j / 4) / (3 * ((g j / 4 : ℕ) : ℝ) + 1) := hb
        _ ≤ _ := hb1
        _ ≤ _ := hc
  · -- explicitness
    intro enc
    obtain ⟨M, p, hM⟩ := hmach enc
    refine ⟨M, p, fun j => ⟨List.ofFn (e j), ?_, ?_, ?_, hM j⟩⟩
    · rw [List.length_ofFn, hcardD]
    · intro a ha
      rw [List.mem_ofFn] at ha
      obtain ⟨i, rfl⟩ := ha
      exact ⟨hne j i, by simp [D]⟩
    · intro d hd
      simp only [D, Finset.mem_image, Finset.mem_univ, true_and] at hd
      obtain ⟨a, rfl⟩ := hd
      exact ⟨e j a, List.mem_ofFn.2 ⟨a, rfl⟩, hne j a, rfl⟩
