-- Prove2me | Definitions.Def_ManolescuPiccirillo_Movie
-- name    : ManolescuPiccirillo_Movie
-- status  : Definition
-- author  : @LG
-- created : 2026-11-16T18:50:56.845449+00:00
-- url     : https://prove2.me/theorems/55ea17d3-fcb9-4aac-8a8e-866cd8585ed3
-- title:
--   Manolescu–Piccirillo: Movie layer
-- statement:
--   Slice-disk movies: births, band merges and Reidemeister moves presenting a connected disk (A-B+C=1).
-- source:
--   Epoch AI FrontierMath, smooth 4D Poincaré conjecture, https://epoch.ai/frontiermath/open-problems/smooth-poincare-4d

import Mathlib
import Definitions.Def_ManolescuPiccirillo_PD
import Definitions.Def_ManolescuPiccirillo_Kirby

open Classical
noncomputable section

namespace ManolescuPiccirillo

structure MovieLink where
  pd : PD
  splitUnknots : ℕ

def MovieLink.totalComponents (L : MovieLink) : ℕ := L.pd.numComponents + L.splitUnknots

inductive MovieMove : MovieLink → MovieLink → Prop
  | birth (L : MovieLink) : MovieMove L ⟨L.pd, L.splitUnknots + 1⟩
  | band (L L' : MovieLink) : L.pd.IsBandMerge L'.pd →
      L.splitUnknots = L'.splitUnknots → MovieMove L L'
  | r1 (L L' : MovieLink) : L.pd.R1 L'.pd → L.splitUnknots = L'.splitUnknots → MovieMove L L'
  | r2 (L L' : MovieLink) : L.pd.R2 L'.pd → L.splitUnknots = L'.splitUnknots → MovieMove L L'
  | r3 (L L' : MovieLink) : L.pd.R3 L'.pd → L.splitUnknots = L'.splitUnknots → MovieMove L L'

inductive MovieSeq : MovieLink → MovieLink → Prop
  | refl (L : MovieLink) : MovieSeq L L
  | step (L L' L'' : MovieLink) : MovieMove L L' → MovieSeq L' L'' → MovieSeq L L''

def mergeGraph (births : ℕ) (merges : List (ℕ × ℕ)) : SimpleGraph (Fin (births + 1)) :=
  SimpleGraph.fromRel (fun a b =>
    (∃ p ∈ merges, (p.1 = a.val ∧ p.2 = b.val) ∨ (p.1 = b.val ∧ p.2 = a.val)) ∧ a ≠ b)

structure SliceMovie (K : PD) where
  final : MovieLink
  seq : MovieSeq ⟨K, 0⟩ final
  finalCrossingless : final.pd.crossings = []
  births : ℕ
  bands : ℕ
  euler : births - bands + final.totalComponents = 1
  bandMerges : List (ℕ × ℕ)
  mergesLen : bandMerges.length = bands
  mergesValid : ∀ p ∈ bandMerges, p.1 ≤ births ∧ p.2 ≤ births
  connected : (mergeGraph births bandMerges).Connected

def HasSliceMovie (K : PD) : Prop := Nonempty (SliceMovie K)

end ManolescuPiccirillo


