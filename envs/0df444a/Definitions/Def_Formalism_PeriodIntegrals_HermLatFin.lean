-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
-- name    : Formalism_PeriodIntegrals_HermLatFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:43.186058+00:00
-- url     : https://prove2.me/theorems/8a60e00d-7e57-4903-aabd-8b1eeb812bad
-- title:
--   Herm Lat Fin
-- statement:
--   Definitions and structural lemmas for Herm Lat Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermLatFin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
namespace PI.HermLatFin
def herm {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j
def IsLat {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤
def admitted {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm σ J x y)) ∧
    ∀ y : Fin n → E, (∀ x ∈ L, IsIntegral ℤ (herm σ J x y)) → (T : E) • y ∈ L
def IsUJ {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J g : Matrix (Fin n) (Fin n) E) : Prop :=
  (g.map σ)ᵀ * J * g = J
def HermLatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ),
    (∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) →
    0 < T →
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧
      ∀ L, admitted σ J T L → ∃ L' ∈ S, ∃ g : Matrix (Fin n) (Fin n) E, IsUJ σ J g ∧
        (fun x => g *ᵥ x) '' (L' : Set (Fin n → E)) = (L : Set (Fin n → E))
end PI.HermLatFin


