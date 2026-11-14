-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_Histogram
-- name    : InfoLossLAR_Native_AFT_Histogram
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:21:06.717816+00:00
-- url     : https://prove2.me/theorems/eaa57b96-b4c6-4851-aa2e-37674c0364fb
-- title:
--   Finite color histograms and position symmetrization
-- statement:
--   For a vector $x:\{0,\ldots,d-1\}\to C$, its histogram records $$h_x(c)=\#\{i:x(i)=c\}.$$ Each count is encoded as an integer between $0$ and $d$. Position permutations act on vectors, and averaging this action defines random relabeling and symmetrization of finite laws. The same interface includes the zero-sum subset when colors carry addition.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/Histogram.lean; migrated source SHA256 9d3ee194cbde3da95a4c528a9f96cb4d7393a95f5ca8329546f1925e383edbfa; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
import Mathlib


/-!
# Concrete histograms and uniform position relabeling

This is the finite combinatorial step of reference V7, Corollary 9.21.
Histograms count colors in actual vectors `Fin dimension → Color`. Equality
of histograms is proved equivalent to relabeling positions by a permutation.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

variable {dimension : ℕ} {Color : Type*}

/-- A finite encoding of color counts; every count lies between zero and the
number of positions. Invalid count vectors are permitted in this ambient type. -/
abbrev Histogram (dimension : ℕ) (Color : Type*) := Color → Fin (dimension + 1)

/-- The actual histogram of a vector, with counts defined by color fibers. -/
noncomputable def histogram (vector : Fin dimension → Color) : Histogram dimension Color := by
  classical
  exact fun color => ⟨Fintype.card {position // vector position = color}, by
    have h := Fintype.card_subtype_le (fun position => vector position = color)
    simpa only [Fintype.card_fin, Nat.lt_succ_iff] using h⟩

@[simp] theorem histogram_count (vector : Fin dimension → Color) (color : Color) :
    (histogram vector color : ℕ) = Fintype.card {position // vector position = color} := by
  classical
  rfl

/-- Reindex a vector by a permutation of positions. -/
def relabel (vector : Fin dimension → Color) (permutation : Equiv.Perm (Fin dimension)) :
    Fin dimension → Color := vector ∘ permutation

@[simp] theorem relabel_apply (vector : Fin dimension → Color)
    (permutation : Equiv.Perm (Fin dimension)) (position : Fin dimension) :
    relabel vector permutation position = vector (permutation position) := rfl





/-- Reindexing positions is an equivalence of the entire vector space. -/
def relabelEquiv (permutation : Equiv.Perm (Fin dimension)) :
    (Fin dimension → Color) ≃ (Fin dimension → Color) where
  toFun vector := relabel vector permutation
  invFun vector := relabel vector permutation.symm
  left_inv vector := by ext position; simp [relabel]
  right_inv vector := by ext position; simp [relabel]

variable [Fintype Color]

/-- Apply an independently uniform position permutation to a fixed vector. -/
noncomputable def randomRelabel (vector : Fin dimension → Color) :
    FiniteDist (Fin dimension → Color) :=
  (FiniteDist.uniform (Equiv.Perm (Fin dimension))).map (relabel vector)













namespace FiniteDist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Draw a deterministic image and then apply a kernel, or apply their
composition directly. -/
theorem mix_map (distribution : FiniteDist α) (image : α → β)
    (kernel : β → FiniteDist γ) :
    (distribution.map image).mix kernel =
      distribution.mix (fun input => kernel (image input)) := by
  ext output
  simp only [mix_weight, map_weight]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Deterministic pushforward commutes with a mixture. -/
theorem map_mix (distribution : FiniteDist α) (kernel : α → FiniteDist β)
    (image : β → γ) :
    (distribution.mix kernel).map image =
      distribution.mix (fun input => (kernel input).map image) := by
  ext output
  simp only [mix_weight, map_weight, Finset.mul_sum]
  trans ∑ candidate, ∑ input,
    if image candidate = output then distribution.weight input * (kernel input).weight candidate
      else 0
  · apply Finset.sum_congr rfl
    intro candidate _
    split_ifs <;> simp
  · rw [Finset.sum_comm]
    simp only [mul_ite, mul_zero]



end FiniteDist

/-- Relabel every sampled vector by independent fresh uniform randomness. -/
noncomputable def symmetrize (distribution : FiniteDist (Fin dimension → Color)) :
    FiniteDist (Fin dimension → Color) := distribution.mix randomRelabel







section HistogramKernel

variable [Nonempty Color]















end HistogramKernel

section ZeroSumReference

variable [AddCommMonoid Color]

/-- The concrete zero-sum endpoint set. -/
abbrev ZeroSumVectors (dimension : ℕ) (Color : Type*) [AddCommMonoid Color] :=
  {vector : Fin dimension → Color // ∑ position, vector position = 0}

instance zeroSumVectorsNonempty : Nonempty (ZeroSumVectors dimension Color) :=
  ⟨⟨fun _ => 0, by simp⟩⟩











end ZeroSumReference

end AFT


