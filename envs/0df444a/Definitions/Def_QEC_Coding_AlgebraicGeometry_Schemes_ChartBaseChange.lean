-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:11:56.563275+00:00
-- url     : https://prove2.me/theorems/88285b41-61bb-40ab-80d3-54309ac501b8
-- title:
--   Chart Base Change
-- statement:
--   Definitions and structural lemmas for Chart Base Change, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/ChartBaseChange.lean

import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C]
variable {P U V X Z T : C}
variable (a : P ⟶ U) (b : P ⟶ V) (i : U ⟶ X) (j : V ⟶ X)
variable (x : X ⟶ Z) (t : T ⟶ Z)
def firstOverlapOver : Over.mk (a ≫ i ≫ x) ⟶ Over.mk (i ≫ x) :=
  Over.homMk a rfl
def secondOverlapOver (h : IsPullback a b i j) :
    Over.mk (a ≫ i ≫ x) ⟶ Over.mk (j ≫ x) :=
  Over.homMk b (by
    change b ≫ (j ≫ x) = a ≫ i ≫ x
    simpa only [Category.assoc] using congrArg (fun k => k ≫ x) h.w.symm)
def leftChartOver : Over.mk (i ≫ x) ⟶ Over.mk x := Over.homMk i rfl
def rightChartOver : Over.mk (j ≫ x) ⟶ Over.mk x := Over.homMk j rfl
variable [HasPullbacks C]
def scalarFirstBaseChangedMap {A B : C} (f : A ⟶ Z) (g : B ⟶ Z)
    (u : A ⟶ B) (hu : u ≫ g = f) : pullback t f ⟶ pullback t g :=
  (pullbackSymmetry t f).hom ≫
    ((Over.pullback t).map (Over.homMk u hu : Over.mk f ⟶ Over.mk g)).left ≫ (pullbackSymmetry t g).inv
end
end QEC.Coding.AlgebraicGeometry.ChartBaseChange
namespace QEC.Coding.AlgebraicGeometry.ChartBaseChange
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B Z T : C} (t : T ⟶ Z)
end
end QEC.Coding.AlgebraicGeometry.ChartBaseChange


