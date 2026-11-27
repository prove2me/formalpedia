-- Prove2me | solution 1 for AbelianCayleyHDX.section_2_4_relation_complex
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:27:23.227613+00:00
-- url     : https://prove2.me/submissions/cbebe3e6-8b17-4c85-a70f-2538b0f1158d

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
import Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_linkVerts
import Definitions.Def_AbelianCayleyHDX_linkWeight
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)
open AbelianCayleyHDX



theorem solution : ¬ (∀ {ι : Type} {κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) (_hH : IsGoodRelationMatrix H ρ)
    (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n) (_hφ : Function.Surjective φ)
    (_hker : LinearMap.ker φ = rowspan H),
    (∀ i : κ, φ (Pi.single i 1) ≠ 0) ∧
    Function.Injective (fun i : κ => φ (Pi.single i 1)) ∧
    Submodule.span (ZMod 2) (Set.range fun i : κ => φ (Pi.single i 1)) = ⊤ ∧
    n = Module.finrank (ZMod 2) (kerF2 H) ∧
    (∀ r : ι, ∑ i ∈ Finset.univ.filter (fun i => H r i ≠ 0), φ (Pi.single i 1) = 0) ∧
    (∀ r r' : ι, r ≠ r' →
      ((Finset.univ.filter fun i => H r i ≠ 0) ∩ (Finset.univ.filter fun i => H r' i ≠ 0)).card ≤ 1) ∧
    IsCayleyComplex (Finset.univ.image fun i : κ => φ (Pi.single i 1)) (relationComplex H φ) ∧
    IsTranslationInvariant (relationComplex H φ) ∧
    (Finset.univ.image fun i : κ => φ (Pi.single i 1)).card = Fintype.card κ ∧
    (∀ e ∈ edges (relationComplex H φ), triCount (relationComplex H φ) e = 2 * ρ) ∧
    linkVerts (relationComplex H φ) 0 = Finset.univ.image (fun i : κ => φ (Pi.single i 1)) ∧
    (∀ u ∈ linkVerts (relationComplex H φ) 0,
      ∑ w ∈ linkVerts (relationComplex H φ) 0, linkWeight (relationComplex H φ) 0 u w = 2 * (ρ : ℝ)) ∧
    (∀ i j : κ, linkWeight (relationComplex H φ) 0 (φ (Pi.single i 1)) (φ (Pi.single j 1)) =
      ((Htilde H).transpose * Htilde H - (ρ : ℝ) • (1 : Matrix κ κ ℝ)) i j)) := by
  intro h
  let H : Matrix PEmpty.{1} PEmpty.{1} (ZMod 2) := fun r _ => r.elim
  have hH : IsGoodRelationMatrix H 1 := by
    refine ⟨fun r => r.elim, fun r => r.elim, Nat.one_pos, fun c => c.elim, ?_⟩
    intro w _ hw
    exact absurd (funext fun c => c.elim) hw
  let φ : (PEmpty.{1} → ZMod 2) →ₗ[ZMod 2] Vec 0 := 0
  have hφ : Function.Surjective φ := fun y => ⟨0, funext fun i => i.elim0⟩
  have hker : LinearMap.ker φ = rowspan H := by
    apply Subsingleton.elim
  obtain ⟨-, -, -, -, -, -, hC, -⟩ := h H 1 hH φ hφ hker
  obtain ⟨-, hne, -⟩ := hC
  obtain ⟨x, hx⟩ := hne
  simp at hx
