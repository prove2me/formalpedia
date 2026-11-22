-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
-- name    : Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:12.186286+00:00
-- url     : https://prove2.me/theorems/41607d7d-3653-4b70-9535-a2dad49532fa
-- title:
--   Decomp Of Normal Statement
-- statement:
--   Definitions and structural lemmas for Decomp Of Normal Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
namespace Formalism.IndefR.U2
variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
def eigPart (op : I → Module.End ℂ A) (c : I → ℂ) : Submodule ℂ A :=
  ⨅ i, LinearMap.ker (op i - c i • (1 : Module.End ℂ A))
structure OrthDecomp (op : I → Module.End ℂ A) (good : Submodule ℂ A) (Ix : Set (I → ℂ)) : Prop where

  span : good ≤ ⨆ c ∈ Ix, eigPart op c ⊓ good

  orth : ∀ c ∈ Ix, ∀ c' ∈ Ix, c ≠ c' → ∀ x ∈ eigPart op c ⊓ good, ∀ y ∈ eigPart op c' ⊓ good, ⟪x, y⟫_ℂ = 0
def Intw (θ : A →ₗ[ℂ] B) (op : I → Module.End ℂ A) (opB : I → Module.End ℂ B) : Prop :=
  ∀ i x, θ (op i x) = opB i (θ x)
def GoodIn (θ : A →ₗ[ℂ] B) (good : Submodule ℂ A) (goodB : Submodule ℂ B) : Prop :=
  ∀ x ∈ good, θ x ∈ goodB
def IsAdj (θ : A →ₗ[ℂ] B) (θa : B →ₗ[ℂ] A) : Prop :=
  ∀ x y, ⟪θ x, y⟫_ℂ = ⟪x, θa y⟫_ℂ
def Lifted (opB : I → Module.End ℂ B) (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) : Set (I → ℂ) :=
  {c | c ∈ Ix ∧ eigPart opB c ⊓ goodB ≠ ⊥}
def OntoParts (θa : B →ₗ[ℂ] A) (op : I → Module.End ℂ A) (opB : I → Module.End ℂ B) (good : Submodule ℂ A)
    (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) : Prop :=
  ∀ c ∈ Lifted opB goodB Ix, eigPart op c ⊓ good ≤ LinearMap.range θa
def LiftsFull (θ : A →ₗ[ℂ] B) (op : I → Module.End ℂ A) (opB : I → Module.End ℂ B) (good : Submodule ℂ A)
    (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) : Prop :=
  (LinearMap.ker θ)ᗮ ⊓ good = ⨆ c ∈ Lifted opB goodB Ix, eigPart op c ⊓ good
def LiftsTyp (opB : I → Module.End ℂ B) (goodB : Submodule ℂ B) (Ix : Set (I → ℂ)) (Ty : (I → ℂ) → Prop) : Prop :=
  ∀ c ∈ Lifted opB goodB Ix, Ty c
def OccTyp (opB : I → Module.End ℂ B) (goodB : Submodule ℂ B) (Ty : (I → ℂ) → Prop) : Prop :=
  ∀ c, eigPart opB c ⊓ goodB ≠ ⊥ → Ty c
variable {θ : A →ₗ[ℂ] B} {θa : B →ₗ[ℂ] A} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
  {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}
section FD
variable [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
def AdjClosed (op : I → Module.End ℂ A) : Prop := ∀ i, ∃ i', op i' = LinearMap.adjoint (op i)
def PairCommF (op : I → Module.End ℂ A) : Prop := ∀ i j, Commute (op i) (op j)
def Occ (op : I → Module.End ℂ A) (good : Submodule ℂ A) : Set (I → ℂ) := {c | eigPart op c ⊓ good ≠ ⊥}
end FD
def DecompOfNormalStatement : Prop :=
  ∀ (I A : Type) [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (op : I → Module.End ℂ A) (good : Submodule ℂ A),
    PairCommF op → AdjClosed op → (∀ i, ∀ x ∈ good, op i x ∈ good) → OrthDecomp op good (Occ op good)
end Formalism.IndefR.U2


