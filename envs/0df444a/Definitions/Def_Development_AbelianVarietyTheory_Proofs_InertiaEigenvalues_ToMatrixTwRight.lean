-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:39.681411+00:00
-- url     : https://prove2.me/theorems/92b5a3c0-f082-4dcd-8e43-4863ceb0c942
-- title:
--   To Matrix Tw Right
-- statement:
--   Definitions and structural lemmas for To Matrix Tw Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
namespace GlobalTheory.CountId
open GlobalTheory.JR
section Map
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']
def mapGl (φ : k →+* k') (Y : Gl r k) : Gl r k' :=
  (Y.1.map φ, fun i => φ (Y.2.1 i), fun i => φ (Y.2.2.1 i), φ Y.2.2.2)
end Map
section Bas
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]
def Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) : Gl n E :=
  (LinearMap.toMatrix e e T, fun i => e.repr v i, fun j => l (e j), 0)
def tw (e : Basis (Fin n) E V) (γ : GL (Fin n) E) : Basis (Fin n) E V :=
  e.map (LinearEquiv.ofLinear (Matrix.toLin e e (γ⁻¹ : GL (Fin n) E)) (Matrix.toLin e e (γ : Matrix _ _ E))
    (by rw [← Matrix.toLin_mul]; simp) (by rw [← Matrix.toLin_mul]; simp))
variable (O : Type) [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
def lat (e : Basis (Fin n) E V) : Submodule O V := Submodule.span O (Set.range e)
variable [IsDomain O] [Module.IsTorsionFree O E]
end Bas
end GlobalTheory.CountId


