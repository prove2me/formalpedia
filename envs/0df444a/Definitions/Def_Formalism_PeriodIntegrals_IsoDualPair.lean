-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
-- name    : Formalism_PeriodIntegrals_IsoDualPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:47.943633+00:00
-- url     : https://prove2.me/theorems/5b8fbd92-b555-4288-b18d-451cc0fdef20
-- title:
--   Iso Dual Pair
-- statement:
--   Definitions and structural lemmas for Iso Dual Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/IsoDualPair.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.IsoDualPair
def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1
def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))
def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0
abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ
def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x
def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))
def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2
def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J
def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J
def IsoDualPair : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram),
    (∀ φ ∈ Vnu N nu, (∀ ψ ∈ Vnu N nu, ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ) ∧
      ∃ ψ ∈ Vnu N nu, l2 ψ = l2 φ ∧ prC φ ψ = (l2 φ : ℂ)) ∧
    ∀ Λ : Vnu N nu →ₗ[ℂ] ℂ, ∃ φ ∈ Vnu N nu, ∀ ψ : Vnu N nu, Λ ψ = prC φ (ψ : LaC N nu)
end PI.IsoDualPair


