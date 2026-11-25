-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:52:35.536828+00:00
-- url     : https://prove2.me/theorems/6aa65b13-dfad-4ae7-b887-582c38b69b47
-- title:
--   Geometric Lemma Cell Surjective
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Cell Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
section Proportional
variable {G : Type*} [Group G] {W E : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup E]
  [Module ℂ E]
end Proportional
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section Bump
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
open Classical in

def bumpFun (x : GL (Fin n) F) (K : Subgroup (GL (Fin n) F)) (v : W) : GL (Fin n) F → W :=
  fun g => if h : ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k then
    inflateTwist F n β σ h.choose v else 0
variable {σ}
end Bump
section LeviProjLemmas
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
end LeviProjLemmas
section CellBump
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY
end CellBump
section CellBump2
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
include hYo hCY hYP
end CellBump2
section CellBump3
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYP hYQ
end CellBump3
section Range
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ
variable (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
include hYP
end Range
section Surjective
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYP hYQ
end Surjective
end Parabolic
end GroundTheory.Automorphic


