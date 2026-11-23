-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_DescentCut
-- name    : Formalism_MeanHeightDescent_DescentCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:34.143137+00:00
-- url     : https://prove2.me/theorems/4c13378d-a2ab-46d1-b637-fcb84c3bf27b
-- title:
--   Descent Cut
-- statement:
--   Definitions and structural lemmas for Descent Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/DescentCut.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_BadRowsNumeric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.ExtensionFiltration
open Formalism.HN
def DescentCut : Prop :=
  ∀ (K V ι W κ V2 ι2 : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [AddCommGroup V2] [Module K V2] [Module (𝓞 K) V2]
    [IsScalarTower (𝓞 K) K V2] [Fintype ι2] [DecidableEq ι2]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (b2 : Basis ι2 K V2) (X2 : InfinitePlace K → Matrix ι2 ι2 ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) → (∀ v, IsUnit (X2 v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W)
      (N Mb : Submodule (𝓞 K) V2) (e : V2 →ₗ[K] V2) (g : ℕ) (c X0 P Λ Q ε δ : ℝ),
      A.FG → B.FG → N.FG → Mb.FG → A ≠ ⊥ → N ≠ ⊥ →

      Function.Injective φ → A.map (φ.restrictScalars (𝓞 K)) ≤ B → htMap b X b' X' φ ≤ P → 0 ≤ P →

      muDef b' X' B = muDef b2 X2 N → muMinDef b' X' B = muMinDef b2 X2 N →

      rkK A ≤ rkK B → (1 - ε) * (rkK B : ℝ) ≤ (rkK A : ℝ) → 0 ≤ ε →

      c - X0 ≤ muDef b X A → 0 ≤ X0 → |c| ≤ Q →

      (∃ s : Set V2, s ⊆ (N : Set V2) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b2 X2 v x ≤ Real.exp Λ) ∧
        (N : Set V2) ⊆ (Submodule.span K s : Set V2)) → 2 * Λ ≤ Q →

      1 ≤ g → e ∘ₗ e = e →
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt b2 X2 v (e x) y = Formalism.HermitianLatticesTheory.majAt b2 X2 v x (e y)) →
      (∀ x ∈ N, (g : K) • e x ∈ N) → N ≤ Mb →
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ≤ 3 * δ * (rkK N : ℝ) →
      0 ≤ δ → δ ≤ 1 / 12 →
      |muDef b2 X2 N| ≤ Q → muMaxDef b2 X2 Mb ≤ Q → 2 * Real.log g ≤ Q →
      c - X0 - P - 2 * ε * Q - 12 * δ * Q ≤
        muDef b2 X2 (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K))
end Formalism.ExtensionFiltration


