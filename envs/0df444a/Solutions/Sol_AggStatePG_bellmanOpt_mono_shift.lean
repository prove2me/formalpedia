-- Prove2me | solution 1 for AggStatePG.bellmanOpt_mono_shift
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T18:29:41.746798+00:00
-- url     : https://prove2.me/submissions/89380300-fe90-4ad5-83bd-fa72fe8285b9

import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_AggStatePG_bellmanOpt

noncomputable section
open FoundationsML.ReinforcementLearning PolicyGradTheory.ProjGA
namespace AggStatePG.BellmanProof

variable {A : Type*} [Fintype A] [Nonempty A]

lemma distributions_nonempty : ({d : A → ℝ | IsDist d} : Set (A → ℝ)).Nonempty := by
  classical
  let a₀ : A := Classical.arbitrary A
  refine ⟨fun a => if a = a₀ then 1 else 0, ?_⟩
  constructor
  · intro a; dsimp only; split <;> norm_num
  · simp

lemma score_image_nonempty (z : A → ℝ) :
    ((fun d : A → ℝ => ∑ a, d a * z a) '' {d | IsDist d}).Nonempty :=
  distributions_nonempty.image _

lemma score_image_bddAbove (z : A → ℝ) :
    BddAbove ((fun d : A → ℝ => ∑ a, d a * z a) '' {d | IsDist d}) := by
  classical
  let M := Finset.univ.sup' (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) z
  refine ⟨M, ?_⟩
  rintro y ⟨d,hd,rfl⟩
  calc
    ∑ a, d a * z a ≤ ∑ a, d a * M := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' z ha) (hd.1 a)
    _ = M := by rw [← Finset.sum_mul, hd.2, one_mul]

end AggStatePG.BellmanProof

open AggStatePG
set_option autoImplicit false

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ V W : S → ℝ, (∀ s, V s ≤ W s) → ∀ s, bellmanOpt P r γ V s ≤ bellmanOpt P r γ W s) ∧
    (∀ (V : S → ℝ) (c : ℝ) (s : S),
        bellmanOpt P r γ (fun s' => V s' + c) s = bellmanOpt P r γ V s + γ * c) := by
  classical
  constructor
  · intro V W hVW s
    apply csSup_le (BellmanProof.score_image_nonempty _)
    rintro y ⟨d,hd,rfl⟩
    apply le_trans _ (le_csSup (BellmanProof.score_image_bddAbove _) (Set.mem_image_of_mem _ hd))
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (hd.1 a)
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ hγ0.le
    apply Finset.sum_le_sum
    intro s' hs'
    exact mul_le_mul_of_nonneg_left (hVW s') ((hP s a).1 s')
  · intro V c s
    have hscore (d : A → ℝ) (hd : IsDist d) :
        (∑ a, d a * (r s a + γ * ∑ s', P s a s' * (V s' + c))) =
          (∑ a, d a * (r s a + γ * ∑ s', P s a s' * V s')) + γ*c := by
      have ha (a : A) :
          r s a + γ * (∑ s', P s a s' * (V s' + c)) =
          (r s a + γ * ∑ s', P s a s' * V s') + γ*c := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (hP s a).2, one_mul]
        ring
      simp_rw [ha, mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hd.2, one_mul]
    apply le_antisymm
    · apply csSup_le (BellmanProof.score_image_nonempty _)
      rintro y ⟨d,hd,rfl⟩
      dsimp only
      rw [hscore d hd]
      exact add_le_add (le_csSup (BellmanProof.score_image_bddAbove _)
        (Set.mem_image_of_mem _ hd)) le_rfl
    · have h : bellmanOpt P r γ V s ≤ bellmanOpt P r γ (fun s' => V s' + c) s - γ*c := by
        apply csSup_le (BellmanProof.score_image_nonempty _)
        rintro y ⟨d,hd,rfl⟩
        have hle := le_csSup (BellmanProof.score_image_bddAbove
          (fun a => r s a + γ * ∑ s', P s a s' * (V s' + c)))
          (Set.mem_image_of_mem (fun d : A → ℝ =>
            ∑ a, d a * (r s a + γ * ∑ s', P s a s' * (V s' + c))) hd)
        rw [hscore d hd] at hle
        exact (le_sub_iff_add_le).mpr hle
      linarith

