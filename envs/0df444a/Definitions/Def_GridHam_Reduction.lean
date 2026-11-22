-- Prove2me | Definitions.Def_GridHam_Reduction
-- name    : GridHam_Reduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:31:35.450209+00:00
-- url     : https://prove2.me/theorems/ef38589c-8c5a-4a63-b310-2eca098b1732
-- title:
--   Reduction
-- statement:
--   Definitions and structural lemmas for Reduction, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
instance instDecG3 (m c0 c1 oc ps pt : ℕ) : Decidable (G3 m c0 c1 oc ps pt) := by
  unfold G3; infer_instance
instance instDecCornerA (w h x y : ℕ) : Decidable (cornerA w h x y) := by
  unfold cornerA; infer_instance
instance instDecF1A (w h sx sy tx ty : ℕ) : Decidable (F1A w h sx sy tx ty) := by
  unfold F1A; infer_instance
instance instDecF2A (w h sx sy tx ty : ℕ) : Decidable (F2A w h sx sy tx ty) := by
  unfold F2A; infer_instance
instance instDecF3A (w h sx sy tx ty : ℕ) : Decidable (F3A w h sx sy tx ty) := by
  unfold F3A; infer_instance
instance instDecForbA (w h sx sy tx ty : ℕ) : Decidable (ForbA w h sx sy tx ty) := by
  unfold ForbA; infer_instance
instance instDecAccA (w h sx sy tx ty : ℕ) : Decidable (AccA w h sx sy tx ty) := by
  unfold AccA; infer_instance
def CCA (w h sx sy tx ty : ℕ) : Prop :=
  (w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
  (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)
def EndsA (w sx sy tx ty : ℕ) : Prop :=
  (sx = 0 ∧ sy = 0 ∧ tx = w - 1 ∧ ty = 0) ∨ (sx = w - 1 ∧ sy = 0 ∧ tx = 0 ∧ ty = 0)
def EndsV (h sx sy tx ty : ℕ) : Prop :=
  (sx = 0 ∧ sy = 0 ∧ tx = 0 ∧ ty = h - 1) ∨ (sx = 0 ∧ sy = h - 1 ∧ tx = 0 ∧ ty = 0)
def NotPrime (w h : ℕ) : Prop :=
  ¬ ((w ≤ 3 ∧ h ≤ 3) ∨ (w = 4 ∧ h = 4) ∨ (w = 4 ∧ h = 5) ∨ (w = 5 ∧ h = 4))
instance instDecNotPrime (w h : ℕ) : Decidable (NotPrime w h) := by
  unfold NotPrime
  infer_instance
def FreeCol (c h sx sy tx ty : ℕ) : Prop :=
  (0 < h ∧ ¬ (sx = c ∧ sy = 0) ∧ ¬ (tx = c ∧ ty = 0)) ∨
  (1 < h ∧ ¬ (sx = c ∧ sy = 1) ∧ ¬ (tx = c ∧ ty = 1)) ∨
  (2 < h ∧ ¬ (sx = c ∧ sy = 2) ∧ ¬ (tx = c ∧ ty = 2))
instance instDecFreeCol (c h sx sy tx ty : ℕ) : Decidable (FreeCol c h sx sy tx ty) := by
  unfold FreeCol
  infer_instance
def rChoice (sx sy h : ℕ) : ℕ :=
  if (sx + sy) % 2 = 0 then 0 else if sx = 0 ∧ sy = 1 ∧ 1 < h - 1 then 3 else 1
def BConcl (w h sx sy tx ty r : ℕ) : Prop :=
  r < h ∧ ¬ (sx = 1 ∧ sy = r) ∧ ¬ (0 = tx - 2 ∧ r = ty) ∧
    AccA 2 h sx sy 1 r ∧ AccA (w - 2) h 0 r (tx - 2) ty
instance instDecBConcl (w h sx sy tx ty r : ℕ) : Decidable (BConcl w h sx sy tx ty r) := by
  unfold BConcl
  infer_instance
end GridHam


