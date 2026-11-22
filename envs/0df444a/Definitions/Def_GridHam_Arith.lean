-- Prove2me | Definitions.Def_GridHam_Arith
-- name    : GridHam_Arith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:25:13.087945+00:00
-- url     : https://prove2.me/theorems/391699d6-eda5-4cb7-9ae4-da25ac009d6e
-- title:
--   Arith
-- statement:
--   Definitions and structural lemmas for Arith, from zzyzek and contributors's pinned Hamiltonian paths in rectangular grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Arith.lean

module
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GridHam
def G3 (m c0 c1 oc ps pt : ℕ) : Prop :=
  m % 2 = 0 ∧ ps ≠ pt ∧
  ((oc = 1 ∧ c0 ≠ c1) ∨ (oc ≠ 1 ∧ (c0 + 1 < c1 ∨ c1 + 1 < c0))) ∧
  ((c1 < c0 ∧ ps ≠ 1) ∨ (¬ c1 < c0 ∧ ps ≠ 0))
def cornerA (w h x y : ℕ) : Prop := (x = 0 ∨ x = w - 1) ∧ (y = 0 ∨ y = h - 1)
def F1A (w h sx sy tx ty : ℕ) : Prop :=
  (w = 1 ∧ ¬ ((sx = 0 ∧ sy = 0 ∧ tx = 0 ∧ ty = h - 1) ∨ (sx = 0 ∧ sy = h - 1 ∧ tx = 0 ∧ ty = 0))) ∨
  (w ≠ 1 ∧ ¬ ((sx = 0 ∧ sy = 0 ∧ tx = w - 1 ∧ ty = 0) ∨ (sx = w - 1 ∧ sy = 0 ∧ tx = 0 ∧ ty = 0)))
def F2A (w h sx sy tx ty : ℕ) : Prop :=
  ¬ cornerA w h sx sy ∧ ¬ cornerA w h tx ty ∧ ((w = 2 ∧ sy = ty) ∨ (h = 2 ∧ sx = tx))
def F3A (w h sx sy tx ty : ℕ) : Prop :=
  (w = 3 ∧ G3 h sy ty sx ((sx + sy) % 2) ((tx + ty) % 2)) ∨
  (w ≠ 3 ∧ G3 w sx tx sy ((sx + sy) % 2) ((tx + ty) % 2))
def ForbA (w h sx sy tx ty : ℕ) : Prop :=
  ((w = 1 ∨ h = 1) ∧ F1A w h sx sy tx ty) ∨
  (¬ (w = 1 ∨ h = 1) ∧ (w = 2 ∨ h = 2) ∧ F2A w h sx sy tx ty) ∨
  (¬ (w = 1 ∨ h = 1) ∧ ¬ (w = 2 ∨ h = 2) ∧ (w = 3 ∨ h = 3) ∧ F3A w h sx sy tx ty)
def AccA (w h sx sy tx ty : ℕ) : Prop :=
  ((w % 2 = 1 ∧ h % 2 = 1 ∧ (sx + sy) % 2 = 0 ∧ (tx + ty) % 2 = 0) ∨
    (¬ (w % 2 = 1 ∧ h % 2 = 1) ∧ (sx + sy) % 2 ≠ (tx + ty) % 2)) ∧
  ¬ ForbA w h sx sy tx ty
end GridHam


