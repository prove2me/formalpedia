-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
-- name    : Formalism_QuotientMetricDivisors_ClassSumDualLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:31.538623+00:00
-- url     : https://prove2.me/theorems/ab287f7a-4b02-43d5-96e2-17099f83de43
-- title:
--   Class Sum Dual Le
-- statement:
--   Definitions and structural lemmas for Class Sum Dual Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/ClassSumDualLe.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
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
def cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  A.comap ((Matrix.mulVecLin E).restrictScalars (𝓞 K))
def IsOrthProj {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) : Prop :=
  Pr * E = 1 ∧ Eᴴ * H * (1 - E * Pr) = 0
def valLat {n : ℕ} {Cl V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) (Fin n → K) :=
  (Submodule.pi Set.univ fun _ : Cl => N).comap (I.restrictScalars (𝓞 K))
def IsClassSum {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    (H : Matrix (Fin n) (Fin n) K) (I : (Fin n → K) →ₗ[K] (Cl → V))
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (g : Cl → ℕ) : Prop :=
  ∀ x y, hform H x y = ∑ c, ((g c : K))⁻¹ * pair (I x c) (I y c)
end Defs
def OrthProjExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K), IsConjAt v0 →
    ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) K), (H.map v0.embedding).PosDef →
    ∀ E : Matrix (Fin n) (Fin d) K, Function.Injective E.mulVec →
      Hᴴ = H ∧ IsUnit H.det ∧ IsUnit (Eᴴ * H * E).det ∧
        IsOrthProj H E ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)) ∧
        ∀ Pr, IsOrthProj H E Pr → Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H)
def ProjDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (matLat Pr A) = cutLat E (Formalism.HermitianLatticesTheory.dual (hform H) A)
def CutDualLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H * E)) (cutLat E A) = matLat Pr (Formalism.HermitianLatticesTheory.dual (hform H) A)
def ExpIndexLat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsLattice K A → Submodule.IsLattice K B →
    ∀ a : 𝓞 K, a ≠ 0 → (∀ x ∈ A, a • x ∈ B) →
    ∀ w : HeightOneSpectrum (𝓞 K), idx w A B ≤ (D : ℤ) * vw w (a : K)
def ExpIndexLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (A B : Submodule (𝓞 K) (Fin D → K)), Submodule.IsLattice K A → Submodule.IsLattice K B →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ x ∈ A, a • x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
      idx w A B ≤ (D : ℤ) * vw w (a : K)
def ClassSumDualLe : Prop :=
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
    ∀ Nab Del : Submodule (𝓞 K) V, Submodule.IsLattice K Nab →
    ∀ s : ℕ, (∀ y ∈ Formalism.HermitianLatticesTheory.dual pair Nab, (s : 𝓞 K) • y ∈ Del) →
    (∀ c γ, ∀ y ∈ Del, ρ c γ y ∈ Del) →
    ∀ y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLat I Nab), (s : 𝓞 K) • y ∈ valLat I Del
def ClassSumDualGe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K)
    (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), (∀ c, 0 < g c) → IsClassSum H I pair g →
    ∀ (Nab Del : Submodule (𝓞 K) V) (s : ℕ), (∀ y ∈ Del, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair Nab) →
    ∀ DG : ℕ, (∀ c, g c ∣ DG) →
    ∀ y ∈ valLat I Del, ((DG * s : ℕ) : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) (valLat I Nab)
def ProjIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G0 : Type) [Fintype G0]
    (r : G0 → Matrix (Fin n) (Fin n) K) (c : G0 → K) (G : ℕ),
    (∀ s, ∃ a : 𝓞 K, (a : K) = (G : K) * c s) →
    ∀ B : Submodule (𝓞 K) (Fin n → K), (∀ s, ∀ x ∈ B, (r s).mulVec x ∈ B) →
    ∀ x ∈ B, (G : 𝓞 K) • (∑ s, c s • r s).mulVec x ∈ B
def BoundsI : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ) (H' : Matrix (Fin n') (Fin n') K),
    H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ s : ℕ, (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
      Submodule.IsLattice K (cutLat E A) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E A), ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E A
def BoundsIVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n' n D : ℕ) (H' : Matrix (Fin n') (Fin n') K), H'ᴴ = H' → IsUnit H'.det →
    ∀ (E : Matrix (Fin n') (Fin n) K) (Pr : Matrix (Fin n) (Fin n') K), IsOrthProj H' E Pr →
    (∀ i j, (Eᴴ * H' * E) i j ∈ K0) →
    (∀ v : InfinitePlace K, ((Eᴴ * H' * E).map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ A B : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ s : ℕ, 0 < s → (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H') A, (s : 𝓞 K) • x ∈ B) →
    ∀ G : ℕ, 0 < G → (∀ x ∈ B, (G : 𝓞 K) • (E * Pr).mulVec x ∈ A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K),
      IsLocBasis (matLat P (cutLat E A)) w e →
      vw w (gramR (quotGram P (Eᴴ * H' * E)) e) ≤ (D : ℤ) * (vw w (G : K) + vw w (s : K))
def BoundsIVGen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K), a ≠ 0 →
    (∀ z ∈ cutLat E A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsLattice K (matLat Pr A) ∧ Submodule.IsLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * (vw w (a : K) + vw w (DG : K))
def BoundsIV : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      Submodule.IsLattice K (matLat Pr A) ∧ Submodule.IsLattice K (cutLat E A) ∧
      cutLat E A ≤ matLat Pr A ∧
      jw (Eᴴ * H * E) w (matLat Pr A) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K))
def BoundsIVReal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E A, (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
        ((J : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
          (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ)
def BoundsIClass : Prop :=
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
    ∀ Nab Del : Submodule (𝓞 K) V, Submodule.IsLattice K Nab →
    ∀ s : ℕ, (∀ y ∈ Formalism.HermitianLatticesTheory.dual pair Nab, (s : 𝓞 K) • y ∈ Del) →
    Del ≤ Nab → (∀ c γ, ∀ y ∈ Del, ρ c γ y ∈ Del) →
    ∀ (G0 : Type) [Fintype G0] (r : G0 → Matrix (Fin n') (Fin n') K) (c : G0 → K) (G : ℕ),
    E * Pr = ∑ t, c t • r t → (∀ t, ∃ a : 𝓞 K, (a : K) = (G : K) * c t) →
    (∀ t, ∀ x ∈ valLat I Del, (r t).mulVec x ∈ valLat I Del) →
      Submodule.IsLattice K (valLat I Nab) ∧ Submodule.IsLattice K (cutLat E (valLat I Nab)) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform (Eᴴ * H' * E)) (cutLat E (valLat I Nab)),
        ((G * s : ℕ) : 𝓞 K) • x ∈ cutLat E (valLat I Nab)
def BoundsIVClass : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ (Cl : Type) [Fintype Cl] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (pair : V →ₗ⋆[K] V →ₗ[K] K)
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (g : Cl → ℕ), Function.Injective I → (∀ c, 0 < g c) →
    IsClassSum H I pair g →
    ∀ Nab Del : Submodule (𝓞 K) V, Submodule.IsLattice K Nab →
    ∀ s : ℕ, 0 < s → (∀ y ∈ Del, (s : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual pair Nab) →
    ∀ DG : ℕ, 0 < DG → (∀ c, g c ∣ DG) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (J : ℕ), vw w (ϖ : K) = 1 →
    (∀ z ∈ cutLat E (valLat I Nab),
      (ϖ ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E (valLat I Del))) →
      Submodule.IsLattice K (matLat Pr (valLat I Nab)) ∧
      jw (Eᴴ * H * E) w (matLat Pr (valLat I Nab)) ≤
        (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr (valLat I Nab)) (cutLat E (valLat I Nab)) : ℤ) +
          (d : ℤ) * ((J : ℤ) + vw w (DG : K) + vw w (s : K))
end Formalism.DivisionValues


