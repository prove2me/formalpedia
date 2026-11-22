-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_StatementE
-- name    : Formalism_LogSumExpBounds_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:13.164307+00:00
-- url     : https://prove2.me/theorems/c78b96eb-75d7-487a-ae83-e668872d1859
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/StatementE.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.E
section
variable {K : Type*} [CommRing K] [StarRing K] {V : Type*} [AddCommGroup V] [Module K V]
def IsHerm (h : V →ₗ[K] V →ₗ⋆[K] K) : Prop := ∀ v w, h w v = star (h v w)
def tau (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V) (v : V) : V :=
  v + h v x • u - h v u • x
end
def TauIsom : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V),
    IsHerm h → h x x = 0 → h u u = 0 → h u x = 0 →
    ∀ v w, h (tau h x u v) (tau h x u w) = h v w
def TauInv : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V),
    IsHerm h → h x x = 0 → h u u = 0 → h u x = 0 →
    ∀ v, tau h x (-u) (tau h x u v) = v ∧ tau h x u (tau h x (-u) v) = v
def TauComp : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x x' u : V),
    IsHerm h → h x x = 0 → h x' x' = 0 → h u u = 0 → h u x = 0 → h u x' = 0 →
    ∀ v, tau h x u (tau h x' (-u) v)
      = v + h v (x - x') • u - h v u • (x - x') + (h v u * h x' x) • u
def TauLattice : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (O : Subring K) (abelian₂ : AddSubgroup V) (x x' u : V),
    IsHerm h → (∀ a ∈ O, star a ∈ O) →
    (∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂) →
    (∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O) →
    h x x = 0 → h x' x' = 0 → h u u = 0 → h u x = 0 → h u x' = 0 →
    x - x' ∈ abelian₂ → u ∈ abelian₂ → h x' x ∈ O →
    tau h x u '' (abelian₂ : Set V) = tau h x' u '' (abelian₂ : Set V)
def mass {C : Type*} [Fintype C] (wt : C → C → ℝ) (c : C) : ℝ := ∑ c', wt c c'
noncomputable def sway {C : Type*} [Fintype C] (om : C → ℂ) (wt : C → C → ℝ) (c : C) : ℂ :=
  (om c)⁻¹ * ∑ c', (wt c c' : ℂ) * om c'
def PhaseSum : Prop :=
  ∀ (C : Type) [Fintype C] (om : C → ℂ) (wt : C → C → ℝ) (C1 : Finset C) (m0 ep : ℝ),
    (∀ c, ‖om c‖ = 1) → (∀ c c', wt c c' = wt c' c) → (∀ c c', 0 ≤ wt c c') → 0 < m0 →
    (∀ c, c ∉ C1 → sway om wt c = (mass wt c : ℂ)) →
    (∀ c ∈ C1, |mass wt c - m0| ≤ ep * m0 ∧ ‖sway om wt c‖ ≤ ep * m0) →
    ‖∑ c ∈ C1, om c‖ ≤ 2 * ep * (C1.card : ℝ)
end Formalism.NuclearRankWeightBounds.E


