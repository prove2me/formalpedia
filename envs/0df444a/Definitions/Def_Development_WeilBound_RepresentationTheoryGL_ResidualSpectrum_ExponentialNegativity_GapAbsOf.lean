-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
-- name    : Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:09.724553+00:00
-- url     : https://prove2.me/theorems/71b2d1de-4666-41b9-95b2-29033b87dac5
-- title:
--   Gap Abs Of
-- statement:
--   Definitions and structural lemmas for Gap Abs Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/GapAbsOf.lean

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
open Matrix Classical
namespace PositivityTheory.Rg.Rs
def e0 (k : Type) [Field k] (n : ℕ) : Fin (n + 1) → k := Pi.single 0 1
def H0 (k : Type) [Field k] (n : ℕ) : Submodule k (Fin (n + 1) → k) := LinearMap.ker (LinearMap.proj 0)
def gmap {k : Type} [Field k] {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) : Submodule k (Fin N → k) :=
  M.map (Matrix.toLin' g.val)
structure LatData (k : Type) [Field k] (n : ℕ) {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V)
    (v : Submodule k (Fin (n + 1) → k) → V) : Prop where
  herm : ∀ x y, B y x = starRingEnd ℂ (B x y)
  pos : ∀ x, x ≠ 0 → 0 < (B x x).re
  surj : Function.Surjective red
  unit : ∀ γ x y, B (ρ γ x) (ρ γ y) = B x y
  isom : ∀ x y, B (t x) (t y) = B x y
  ne : v ⊤ ≠ 0
  equiv : ∀ γ M, ρ γ (v M) = v (gmap (red γ) M)
  fix : ∀ y, (∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y) →
    ∀ γ, gmap (red γ) (H0 k n) = H0 k n → ρ γ (t y) = t y
  step : ∀ M, e0 k n ∈ M → t (v M) = v (M ⊓ H0 k n)
def LatEig (k : Type) [Field k] [Fintype k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (v : Submodule k (Fin (n + 1) → k) → V) (S : Multiset ℂ) : Prop :=
  S.card = n + 1 ∧ ∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M =
    ((Fintype.card k : ℂ) ^ (((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2) * S.esymm j) • v ⊤
def GapAbs : Prop := ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V Γ : Type) [AddCommGroup V] [Module ℂ V] [Group Γ]
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V)
  (v : Submodule k (Fin (n + 1) → k) → V) (S : Multiset ℂ), LatData k n B red ρ t v → LatEig k n v S → 0 ∉ S →
  ∀ z : ℂ, ‖z‖ < (Fintype.card k : ℝ) ^ (-(1 / 2) : ℝ) → S.count z ≤ S.count ((Fintype.card k : ℂ) * z)
def GapOp : Prop := ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V Γ : Type) [AddCommGroup V] [Module ℂ V] [Group Γ]
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V)
  (v : Submodule k (Fin (n + 1) → k) → V) (lam : ℕ → ℂ), LatData k n B red ρ t v →
  (∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M = lam j • v ⊤) →
  ∃ (W : Submodule ℂ V) (U : Module.End ℂ V) (Z : ℕ → V), (∀ y ∈ W, U y ∈ W) ∧ (∀ j, Z j ∈ W) ∧
    (∀ y ∈ W, (Fintype.card k : ℝ) ^ ((n : ℝ) - 1) * (B y y).re ≤ (B (U y) (U y)).re) ∧
    Z 0 = v ⊤ ∧ Z (n + 1) = 0 ∧
    (∀ j ≤ n, U (Z j) = (Fintype.card k : ℂ) ^ j • (lam (j + 1) • v ⊤ - Z (j + 1))) ∧
    ∀ j ≤ n + 1, ((Fintype.card k : ℂ) ^ (n + 1) - 1) * B (Z j) (v ⊤) =
      ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j * B (v ⊤) (v ⊤)
def GapPoly : Prop := ∀ (q n : ℕ), 2 ≤ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (W : Submodule ℂ V) (U : Module.End ℂ V) (Z : ℕ → V) (S : Multiset ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) →
  S.card = n + 1 → 0 ∉ S → Z 0 ≠ 0 → (∀ y ∈ W, U y ∈ W) → (∀ j, Z j ∈ W) →
  (∀ y ∈ W, (q : ℝ) ^ ((n : ℝ) - 1) * (B y y).re ≤ (B (U y) (U y)).re) → Z (n + 1) = 0 →
  (∀ j ≤ n, U (Z j) = (q : ℂ) ^ j •
    (((q : ℂ) ^ ((((j + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - ((j + 1 : ℕ) : ℂ))) / 2) * S.esymm (j + 1)) • Z 0 - Z (j + 1))) →
  (∀ j ≤ n + 1, ((q : ℂ) ^ (n + 1) - 1) * B (Z j) (Z 0) =
    ((q : ℂ) ^ (n + 1 - j) - 1) * ((q : ℂ) ^ (((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2) * S.esymm j) * B (Z 0) (Z 0)) →
  ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → S.count z ≤ S.count ((q : ℂ) * z)
end PositivityTheory.Rg.Rs
end


