-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:56.883151+00:00
-- url     : https://prove2.me/theorems/a97de53a-ae81-452a-b216-2177987301c9
-- title:
--   Localizing Cech
-- statement:
--   Definitions and structural lemmas for Localizing Cech, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/LocalizingCech.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable (P) in

structure LocalizingAction (D : R → Opens X) where

  act : R → ∀ W : Opens X, P.obj (op W) →+ P.obj (op W)
  res_act : ∀ (r : R) {V W : Opens X} (h : V ≤ W) (x : P.obj (op W)),
    res P h (act r W x) = act r V (res P h x)
  act_mul : ∀ (a b : R) (W : Opens X) (x : P.obj (op W)), act (a * b) W x = act a W (act b W x)
  act_add : ∀ (a b : R) (W : Opens X) (x : P.obj (op W)), act (a + b) W x = act a W x + act b W x
  act_one : ∀ (W : Opens X) (x : P.obj (op W)), act 1 W x = x
  bijective : ∀ (g : R) (W : Opens X), W ≤ D g → Function.Bijective (act g W)
  kill : ∀ (s t : R) {W W' : Opens X}, W = D s → W' = D (s * t) → ∀ (h : W' ≤ W)
    (x : P.obj (op W)), res P h x = 0 → ∃ N : ℕ, act (t ^ N) W x = 0
  lift : ∀ (s t : R) {W W' : Opens X}, W = D s → W' = D (s * t) → ∀ (h : W' ≤ W)
    (y : P.obj (op W')), ∃ (N : ℕ) (x : P.obj (op W)), res P h x = act (t ^ N) W' y
  D_mul : ∀ s t : R, D (s * t) = D s ⊓ D t
  cover : ∀ (g : R) {ι : Type u} [Fintype ι] (h : ι → R) (N : ℕ), D g ≤ ⨆ i, D (h i) →
    ∃ (L : ℕ) (c : ι → R), g ^ L = ∑ i, c i * h i ^ N
variable {D : R → Opens X} (A : LocalizingAction P D)
namespace LocalizingAction
end LocalizingAction
variable {ι : Type u} (U : ι → Opens X)
def actC (r : R) (n : ℕ) : Cochain P U n →+ Cochain P U n where
  toFun σ i := A.act r _ (σ i)
  map_zero' := by funext i; exact map_zero _
  map_add' σ τ := by funext i; exact map_add _ _ _
variable (h : ι → R)
end GroundTheory.Arith.SchemeCoh


