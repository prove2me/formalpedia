-- Prove2me | solution 1 for AnosovPlugs.stronglyIsotopic_trans
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T09:09:51.501959+00:00
-- url     : https://prove2.me/submissions/a3267163-ad64-4471-8482-c7fdcee1ff9a

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

/-- Concatenation of two families that are continuous on their parameter domains. -/
theorem concat_continuousOn_aux {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (S T : ℝ → Set α) (f g : ℝ → α → β)
    (hf : ContinuousOn (fun p : ℝ × α => f p.1 p.2) {p | p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ S p.1})
    (hg : ContinuousOn (fun p : ℝ × α => g p.1 p.2) {p | p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ T p.1})
    (hST : S 1 = T 0) (hfg : ∀ x ∈ S 1, f 1 x = g 0 x) :
    ContinuousOn (fun p : ℝ × α => (if p.1 ≤ 1/2 then f (2*p.1) else g (2*p.1-1)) p.2)
      {p | p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ (if p.1 ≤ 1/2 then S (2*p.1) else T (2*p.1-1))} := by
  set D := {p : ℝ × α | p.1 ∈ Icc (0:ℝ) 1 ∧
    p.2 ∈ (if p.1 ≤ 1/2 then S (2*p.1) else T (2*p.1-1))} with hD
  set F := fun p : ℝ × α => (if p.1 ≤ 1/2 then f (2*p.1) else g (2*p.1-1)) p.2 with hF
  set A := D ∩ {p | p.1 ≤ 1/2} with hA'
  set B := D ∩ {p | 1/2 ≤ p.1} with hB'
  have hA : ContinuousOn F A := by
    have h1 : ContinuousOn (fun p : ℝ × α => f (2*p.1) p.2) A := by
      have : ContinuousOn (fun p : ℝ × α => ((2:ℝ)*p.1, p.2)) A := by fun_prop
      refine hf.comp this ?_
      rintro ⟨t, x⟩ ⟨⟨⟨ht0, ht1⟩, hx⟩, ht⟩
      simp only [mem_ofPred_eq] at ht hx ⊢
      rw [if_pos ht] at hx
      exact ⟨⟨by linarith, by linarith⟩, hx⟩
    refine h1.congr ?_
    rintro ⟨t, x⟩ ⟨_, ht⟩
    simp only [mem_ofPred_eq] at ht
    simp only [F, if_pos ht]
  have hB : ContinuousOn F B := by
    have h1 : ContinuousOn (fun p : ℝ × α => g (2*p.1-1) p.2) B := by
      have : ContinuousOn (fun p : ℝ × α => ((2:ℝ)*p.1-1, p.2)) B := by fun_prop
      refine hg.comp this ?_
      rintro ⟨t, x⟩ ⟨⟨⟨ht0, ht1⟩, hx⟩, ht⟩
      simp only [mem_ofPred_eq] at ht hx ⊢
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      split_ifs at hx with h
      · have h2 : t = 1/2 := le_antisymm h ht
        subst h2
        norm_num at hx ⊢
        rw [← hST]
        exact hx
      · exact hx
    refine h1.congr ?_
    rintro ⟨t, x⟩ ⟨⟨_, hx⟩, ht⟩
    simp only [mem_ofPred_eq] at ht hx
    simp only [F]
    split_ifs at hx ⊢ with h
    · have h2 : t = 1/2 := le_antisymm h ht
      subst h2
      norm_num at hx ⊢
      exact hfg x hx
    · rfl
  have hDAB : D = A ∪ B := by
    ext p
    simp only [A, B, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      rcases le_total p.1 (1/2) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hcA : IsClosed {p : ℝ × α | p.1 ≤ 1/2} := isClosed_le continuous_fst continuous_const
  have hcB : IsClosed {p : ℝ × α | 1/2 ≤ p.1} := isClosed_le continuous_const continuous_fst
  intro p hp
  rw [hDAB] at hp ⊢
  apply ContinuousWithinAt.union
  · by_cases hpA : p ∈ A
    · exact hA p hpA
    · apply continuousWithinAt_of_notMem_closure
      intro hcl
      have ha : p ∈ {p : ℝ × α | p.1 ≤ 1/2} :=
        hcA.closure_subset (closure_mono (show A ⊆ {p : ℝ × α | p.1 ≤ 1/2} from
          inter_subset_right) hcl)
      rcases hp with h | h
      · exact hpA h
      · exact hpA ⟨h.1, ha⟩
  · by_cases hpB : p ∈ B
    · exact hB p hpB
    · apply continuousWithinAt_of_notMem_closure
      intro hcl
      have hb : p ∈ {p : ℝ × α | 1/2 ≤ p.1} :=
        hcB.closure_subset (closure_mono (show B ⊆ {p : ℝ × α | 1/2 ≤ p.1} from
          inter_subset_right) hcl)
      rcases hp with h | h
      · exact hpB ⟨h.1, hb⟩
      · exact hpB h

theorem solution {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold AnosovPlugs.I3 ∞ U] [T2Space U] [CompactSpace U]
    {X₀ X₁ X₂ : (x : U) → TangentSpace AnosovPlugs.I3 x} {φ₀ φ₁ φ₂ : U → U}
    (h₀₁ : AnosovPlugs.StronglyIsotopic X₀ φ₀ X₁ φ₁)
    (h₁₂ : AnosovPlugs.StronglyIsotopic X₁ φ₁ X₂ φ₂) :
    AnosovPlugs.StronglyIsotopic X₀ φ₀ X₂ φ₂ := by
  obtain ⟨Xt, φt, hX0, hX1, hφ0, hφ1, hall, hcX, hcφ⟩ := h₀₁
  obtain ⟨Yt, χt, hY0, hY1, hχ0, hχ1, hall', hcY, hcχ⟩ := h₁₂
  refine ⟨fun t => if t ≤ 1/2 then Xt (2*t) else Yt (2*t-1),
    fun t => if t ≤ 1/2 then φt (2*t) else χt (2*t-1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [hX0]
  · norm_num [hY1]
  · intro x hx
    norm_num
    exact hφ0 x hx
  · intro x hx
    norm_num
    exact hχ1 x hx
  · intro t ht
    dsimp only
    split_ifs with h
    · exact hall _ ⟨by linarith [ht.1], by linarith⟩
    · exact hall' _ ⟨by linarith, by linarith [ht.2]⟩
  · set F : ℝ → TangentBundle AnosovPlugs.I3 U → TangentBundle AnosovPlugs.I3.tangent
        (TangentBundle AnosovPlugs.I3 U) := fun t v => tangentMap AnosovPlugs.I3
        AnosovPlugs.I3.tangent (fun x => (⟨x, Xt t x⟩ : TangentBundle AnosovPlugs.I3 U)) v with hF
    set G : ℝ → TangentBundle AnosovPlugs.I3 U → TangentBundle AnosovPlugs.I3.tangent
        (TangentBundle AnosovPlugs.I3 U) := fun t v => tangentMap AnosovPlugs.I3
        AnosovPlugs.I3.tangent (fun x => (⟨x, Yt t x⟩ : TangentBundle AnosovPlugs.I3 U)) v with hG
    have key := concat_continuousOn_aux (fun _ => univ) (fun _ => univ) F G hcX hcY rfl
      (by intro x _; simp only [F, G, hX1, hY0])
    refine (key.mono ?_).congr ?_
    · rintro ⟨t, x⟩ ⟨ht, -⟩
      exact ⟨ht, by split_ifs <;> trivial⟩
    · rintro ⟨t, x⟩ -
      by_cases h : t ≤ 1/2 <;> simp only [h, ↓reduceIte, F, G]
  · have key := concat_continuousOn_aux (fun t => AnosovPlugs.outBoundary (Xt t))
      (fun t => AnosovPlugs.outBoundary (Yt t)) φt χt hcφ hcχ (by simp only [hX1, hY0])
      (by
        intro x hx
        simp only [hX1] at hx
        exact (hφ1 x hx).trans (hχ0 x hx).symm)
    refine (key.mono ?_).congr ?_
    · rintro ⟨t, x⟩ ⟨ht, hx⟩
      refine ⟨ht, ?_⟩
      dsimp only at hx ⊢
      split_ifs at hx ⊢ <;> exact hx
    · rintro ⟨t, x⟩ -
      rfl
