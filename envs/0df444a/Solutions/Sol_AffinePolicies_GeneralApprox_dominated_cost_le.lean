-- Prove2me | solution 1 for AffinePolicies.GeneralApprox.dominated_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:22:06.694802+00:00
-- url     : https://prove2.me/submissions/bb0cb6e6-ea83-41d1-b264-8644f23d41a5

import Mathlib
import Definitions.Def_AffinePolicies_GeneralApprox_Setting

open Matrix in
theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (V W : Set (Fin m → ℝ)) (hdom : ∀ b ∈ W, ∃ b' ∈ V, b ≤ b')
    (xt : Fin n₁ → ℝ) (yt : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hopt : AffinePolicies.Simplex.IsOptimalAdapt A B c d V xt yt) (hfin : ∃ t : ℝ, AffinePolicies.Simplex.CostLE c d V xt yt t) :
    ∀ b ∈ W, ∃ y : Fin n₂ → ℝ, 0 ≤ y ∧ b ≤ A *ᵥ xt + B *ᵥ y ∧
      c ⬝ᵥ xt + d ⬝ᵥ y ≤ AffinePolicies.Simplex.zAdapt A B c d V := by
  intro b hb
  obtain ⟨b', hb'V, hbb'⟩ := hdom b hb
  obtain ⟨hfeas, hbest⟩ := hopt
  obtain ⟨t0, ht0⟩ := hfin
  refine ⟨yt b', (hfeas.2 b' hb'V).1, le_trans hbb' (hfeas.2 b' hb'V).2, ?_⟩
  unfold AffinePolicies.Simplex.zAdapt
  apply le_csInf
  · exact ⟨t0, xt, yt, hfeas, ht0⟩
  · rintro t ⟨x', y', hf', hc'⟩
    exact hbest x' y' t hf' hc' b' hb'V
