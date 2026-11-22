-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
-- name    : Formalism_QuotientMetricDivisors_ClassSumDualGeF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:25.860911+00:00
-- url     : https://prove2.me/theorems/821761cd-ebc5-49d4-96ca-b903e8ea7f3a
-- title:
--   Class Sum Dual Ge F
-- statement:
--   Definitions and structural lemmas for Class Sum Dual Ge F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/ClassSumDualGeF.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
section Defs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def valLatF {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V) :
    Submodule (𝓞 K) (Fin n → K) :=
  (Submodule.pi Set.univ N).comap (I.restrictScalars (𝓞 K))
end Defs
def ClassSumDualLeF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n → K) →ₗ[K] (Cl → V),
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLatF I Nab), (s : 𝓞 K) • y ∈ valLatF I Del
def ClassSumDualGeF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), (∀ c, 0 < g c) → IsClassSum H I pair g →
    ∀ (Nab Del : Cl → Submodule (𝓞 K) V) (s : ℕ),
    (∀ c, ∀ y ∈ Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c)) →
    ∀ DG : ℕ, (∀ c, g c ∣ DG) →
    ∀ y ∈ valLatF I Del, ((DG * s : ℕ) : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLatF I Nab)
def BoundsIClassF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K),
    pair.IsSymm → pair.Nondegenerate →
    ∀ (Gam : Cl → Type) [∀ c, Group (Gam c)] [∀ c, Fintype (Gam c)]
      (ρ : ∀ c, Gam c →* Module.End K V),
    (∀ c γ x y, pair (ρ c γ x) (ρ c γ y) = pair x y) →
    ∀ I : (Fin n' → K) →ₗ[K] (Cl → V), Function.Injective I →
    (∀ f : Cl → V, (∃ x, I x = f) ↔ ∀ c γ, ρ c γ (f c) = f c) →
    IsClassSum H' I pair (fun c => Fintype.card (Gam c)) →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, (∀ c, ∀ y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c), (s : 𝓞 K) • y ∈ Del c) →
    (∀ c, Del c ≤ Nab c) → (∀ c γ, ∀ y ∈ Del c, ρ c γ y ∈ Del c) →
    ∀ (G0 : Type) [Fintype G0] (r : G0 → Matrix (Fin n') (Fin n') K) (c : G0 → K) (G : ℕ),
    E * Pr = ∑ t, c t • r t → (∀ t, ∃ a : 𝓞 K, (a : K) = (G : K) * c t) →
    (∀ t, ∀ x ∈ valLatF I Del, (r t).mulVec x ∈ valLatF I Del) →
      Submodule.IsLattice K (valLatF I Nab) ∧ Submodule.IsLattice K (cutLat E (valLatF I Nab)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E (valLatF I Nab)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (valLatF I Nab)
def BoundsIVClassF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), Function.Injective I → (∀ c, 0 < g c) →
    IsClassSum H I pair g →
    ∀ Nab Del : Cl → Submodule (𝓞 K) V, (∀ c, Submodule.IsLattice K (Nab c)) →
    ∀ s : ℕ, 0 < s → (∀ c, ∀ y ∈ Del c, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair (Nab c)) →
    ∀ DG : ℕ, 0 < DG → (∀ c, g c ∣ DG) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E (valLatF I Nab),
      (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E (valLatF I Del))) →
      Submodule.IsLattice K (matLat Pr (valLatF I Nab)) ∧
      jw (Eᴴ * H * E) w (matLat Pr (valLatF I Nab)) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr (valLatF I Nab)) (cutLat E (valLatF I Nab)) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K) + vw w (s : K))
end Formalism.DivisionValues


