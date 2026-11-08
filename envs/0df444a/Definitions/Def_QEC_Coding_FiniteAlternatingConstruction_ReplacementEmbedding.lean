-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
-- name    : QEC_Coding_FiniteAlternatingConstruction_ReplacementEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:37:16.588418+00:00
-- url     : https://prove2.me/theorems/eb5272ab-5e71-406a-b1a1-10be7338a319
-- title:
--   Replacement Embedding
-- statement:
--   Definitions and structural lemmas for Replacement Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/ReplacementEmbedding.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
namespace QEC.Coding.BDL26ReplacementEmbedding
open BDL26FiniteTannerSquare
abbrev PositiveCell (S : OddScale) := Two × (Fin S.ell × Fin S.ell)
abbrev SeamCell (S : OddScale) := Two × Fin S.ell
abbrev FlatCell (S : OddScale) := PositiveCell S ⊕ (SeamCell S ⊕ SeamCell S)
def lastStrip (S : OddScale) : Fin S.ell := ⟨S.ell - 1, by have := S.three_le; omega⟩
def charge (S : OddScale) : FlatCell S → PositiveCell S
  | .inl p => p
  | .inr (.inl h) => (h.1, h.2, lastStrip S)
  | .inr (.inr v) => (v.1, lastStrip S, v.2)
def chargeTag (S : OddScale) : FlatCell S → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2
def lower (S : OddScale) (i : Fin S.ell) : Fin (S.ell + 1) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩
def upper (S : OddScale) (i : Fin S.ell) : Fin (S.ell + 1) :=
  ⟨i.1 + 1, by omega⟩
section Images
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev GridMap (S : OddScale) (E : Type*) :=
  Fin (S.ell + 1) → Fin (S.ell + 1) → E
def positiveImage (S : OddScale) (p : GridMap S E) (c : PositiveCell S) : Set E :=
  convexHull ℝ {p (lower S c.2.1) (lower S c.2.2),
    p (upper S c.2.1) (lower S c.2.2), p (upper S c.2.1) (upper S c.2.2)} ∪
  convexHull ℝ {p (lower S c.2.1) (lower S c.2.2),
    p (upper S c.2.1) (upper S c.2.2), p (lower S c.2.1) (upper S c.2.2)}
def horizontalImage (S : OddScale) (p : GridMap S E) (c : SeamCell S) : Set E :=
  segment ℝ (p (lower S c.2) (lower S (lastStrip S)))
    (p (upper S c.2) (lower S (lastStrip S)))
def verticalImage (S : OddScale) (p : GridMap S E) (c : SeamCell S) : Set E :=
  segment ℝ (p (lower S (lastStrip S)) (lower S c.2))
    (p (lower S (lastStrip S)) (upper S c.2))
def cellImage (S : OddScale) (p : GridMap S E) : FlatCell S → Set E
  | .inl c => positiveImage S p c
  | .inr (.inl c) => horizontalImage S p c
  | .inr (.inr c) => verticalImage S p c
noncomputable def positiveHits (S : OddScale) (p : GridMap S E) (region : Set E) :
    Finset (PositiveCell S) := by
  classical
  exact Finset.univ.filter fun c => (positiveImage S p c ∩ region).Nonempty
noncomputable def allHits (S : OddScale) (p : GridMap S E) (region : Set E) :
    Finset (FlatCell S) := by
  classical
  exact Finset.univ.filter fun c => (cellImage S p c ∩ region).Nonempty
end Images
open scoped BigOperators
noncomputable def familyHits {ι E : Type*} [Fintype ι]
    (images : ι → Set E) (region : Set E) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (images i ∩ region).Nonempty
end QEC.Coding.BDL26ReplacementEmbedding


