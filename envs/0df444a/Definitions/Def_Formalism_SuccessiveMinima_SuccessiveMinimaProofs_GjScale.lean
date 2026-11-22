-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
-- name    : Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:33.006654+00:00
-- url     : https://prove2.me/theorems/fb0128b7-13f4-4991-ae5f-861b90226d42
-- title:
--   Gj Scale
-- statement:
--   Definitions and structural lemmas for Gj Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
namespace Formalism.FN
namespace GjScaling
def Zv (ι : Type*) : Set (ι → ℝ) := {k | ∀ i, ∃ m : ℤ, k i = m}
def Qv (ι : Type*) : Set (ι → ℝ) := {u | ∀ i, 0 ≤ u i ∧ u i < 1}
def tm {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) : ℝ≥0∞ := volume (Qv ι ∩ (B + Zv ι))
variable {ι : Type*} [Fintype ι]
section decomp
variable (n j : ℕ)
def emb (u : {i : Fin n // (i : ℕ) < j} → ℝ) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Fin n → ℝ :=
  fun i => if h : (i : ℕ) < j then u ⟨i, h⟩ else y ⟨i, h⟩
def fib (A : Set (Fin n → ℝ)) (y : {i : Fin n // ¬ (i : ℕ) < j} → ℝ) :
    Set ({i : Fin n // (i : ℕ) < j} → ℝ) :=
  {u | emb n j u y ∈ A}
end decomp
end GjScaling
end Formalism.FN


