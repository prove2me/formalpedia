-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:36.761206+00:00
-- url     : https://prove2.me/theorems/d43c6992-2199-497d-aef3-fb9fd2225582
-- title:
--   Kuga St
-- statement:
--   Definitions and structural lemmas for Kuga St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/KugaSt.lean

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
namespace PositivityTheory.Rg.Cz
def KugaAbs : Prop :=
  ∀ (P : Type) [AddCommGroup P] [Module ℝ P] (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (β γ : Type) [Fintype β] [Fintype γ] (b : β → P) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (a r : P →ₗ[ℝ] Module.End ℂ M) (a' r' : γ → Module.End ℂ M) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ),
    Submodule.span ℝ (Set.range b) = ⊤ → (∀ x y, B y x = starRingEnd ℂ (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) →
    (∀ X x y, B (a X x) y = -B x (a X y)) → (∀ X x y, B (r X x) y = B x (r X y)) →
    (∀ X Y, Commute (a X) (r Y)) → (∀ k, Commute (a' k) (r' k)) →
    (∀ i j, a (b i) * a (b j) - a (b j) * a (b i) = ∑ k, (c i j k : ℂ) • a' k) →
    (∀ i j, r (b i) * r (b j) - r (b j) * r (b i) = ∑ k, (c i j k : ℂ) • r' k) →
    (∀ i j k, c j i k = -c i j k) → (∀ k j, D k (b j) = ∑ i, c i j k • b i) →
    (∀ x, (B (((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
      Module.End ℂ M) x) x).re ≤ 0) →
    ∀ (q : ℕ) (ω : P [⋀^Fin q]→ₗ[ℝ] M),
      (∀ k (Y : Fin q → P), (a' k + r' k) (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s)))) →
      ∀ X : Fin (q + 1) → P, ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (a (X i) + r (X i)) (ω (i.removeNth X)) = 0
end PositivityTheory.Rg.Cz
end


