-- Prove2me | solution 1 for AJOnline.tensor_tight_left
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:12:51.319288+00:00
-- url     : https://prove2.me/submissions/6d7c277c-375e-492a-9d66-bcf180c43813

import Mathlib
import Definitions.Def_AJOnline_CostedGame

open AJGames AJOnline
open scoped ENNReal NNReal

universe u

theorem projL_map_inl {α β : Type u} (s : List α) : projL (s.map (Sum.inl : α → α ⊕ β)) = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [ih]

theorem projR_map_inl {α β : Type u} (s : List α) : projR (s.map (Sum.inl : α → α ⊕ β)) = [] := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [ih]

/-- **The tensor cannot beat its left component.** -/
theorem solution (C D : CostedGame.{u}) (σ : Strategy C.G) (τ : Strategy D.G) (ρ b : ℝ≥0)
    (hD : D.opt [] = 0) (h : Competitive (C.tensor D) (tensorS σ τ) ρ b) :
    Competitive C σ ρ b := by
  intro s hs
  have hpos : s ∈ C.G.pos := σ.subset_pos hs
  have hmem : s.map Sum.inl ∈ (tensorS σ τ).carrier := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [List.isChain_map]
      exact (C.G.alt s hpos).imp fun a b hab => ⟨hab, Or.inl rfl⟩
    · rw [projL_map_inl]; exact hpos
    · rw [projR_map_inl]; exact D.G.nil_mem
    · rw [projL_map_inl]; exact hs
    · rw [projR_map_inl]; exact τ.nil_mem
  have h1 := h _ hmem
  change C.alg (projL (s.map Sum.inl)) + D.alg (projR (s.map Sum.inl)) ≤
    (ρ : ℝ≥0∞) * (C.opt (projL (s.map Sum.inl)) + D.opt (projR (s.map Sum.inl))) + b at h1
  rw [projL_map_inl, projR_map_inl, hD, add_zero] at h1
  exact le_trans le_self_add h1
