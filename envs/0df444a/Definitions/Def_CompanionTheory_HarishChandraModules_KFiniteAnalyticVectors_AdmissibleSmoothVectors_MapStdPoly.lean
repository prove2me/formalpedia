-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
-- name    : CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:58.26889+00:00
-- url     : https://prove2.me/theorems/92cef23c-eefd-47b2-a849-b5c6a901099c
-- title:
--   Map Std Poly
-- statement:
--   Definitions and structural lemmas for Map Std Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/MapStdPoly.lean

import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace CompanionTheory.D.gk.admitted
open PI.UpqRep
section Words
variable {R : Type*} [Ring R]
def word (E : R) (l : List R) : R := l.foldr (fun a w => E * a * w) E
def stdPoly (E : R) {M : ℕ} (a : Fin M → R) : R :=
  ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : R) * word E (List.ofFn fun i => a (π i))
end Words
def RFin {K : Type} [Group K] [TopologicalSpace K] (e : K → ℂ) (d : ℕ) : Prop :=
  ∃ φ : Fin d → K → ℂ, (∀ i, Continuous (φ i)) ∧ ∀ k : K, ∃ c : Fin d → ℂ, ∀ x, e (x * k⁻¹) = ∑ i, c i * φ i x
structure IsGood {G : Type} [Group G] [TopologicalSpace G] (st : G → G) (S : Set G) {ι : Type} [Fintype ι]
    [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ) : Prop where
  cont : Continuous ρ
  adj : ∀ g, ρ (st g) = (ρ g)ᴴ
  tri : ∃ h : ι → ℕ, Function.Injective h ∧ ∀ s ∈ S, (ρ s).BlockTriangular h
def FinOfPI : Prop :=
  ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : G →* (H →L[ℂ] H)), (∀ g v, ‖σ g v‖ = ‖v‖) →
    (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    ∀ (E : H →L[ℂ] H) (M : ℕ), (∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0) →
      FiniteDimensional ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ∧ Module.finrank ℂ (LinearMap.range (E : H →ₗ[ℂ] H)) ≤ M
def SmallPI : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W Y : Submodule ℂ V) [FiniteDimensional ℂ Y], Y ≤ W →
    ∀ E : Module.End ℂ V, (∀ w ∈ W, E w ∈ Y) → ∀ M : ℕ, Module.finrank ℂ Y ^ 2 < M →
    ∀ a : Fin M → Module.End ℂ V, (∀ i, ∀ w ∈ W, a i w ∈ W) → ∀ w ∈ W, stdPoly E a w = 0
def GoodPI : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    (K : Subgroup G) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulRightInvariant]
    (st : G → G) (S : Set G), (∀ g, ∃ k ∈ K, ∃ s ∈ S, g = k * s) →
    ∀ (e : K → ℂ) (d M : ℕ), Continuous e → RFin e d → d ^ 2 < M →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ), IsGood st S ρ →
    ∀ E : Module.End ℂ (ι → ℂ), (∀ u, E u = ∫ k : K, e k • (ρ k *ᵥ u) ∂μ) →
    ∀ g : Fin M → G, stdPoly E (fun i => Matrix.toLin' (ρ (g i))) = 0
def Transfer : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    (K : Subgroup G) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (st : G → G) (S : Set G)
    (ι₀ : Type) [Fintype ι₀] [DecidableEq ι₀] (ρ₀ : G →* Matrix ι₀ ι₀ ℂ), IsGood st S ρ₀ → Function.Injective ρ₀ →
    ∀ (e : K → ℂ), Continuous e → ∀ (M : ℕ) (g : Fin M → G),
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι ℂ), IsGood st S ρ →
      ∀ E : Module.End ℂ (ι → ℂ), (∀ u, E u = ∫ k : K, e k • (ρ k *ᵥ u) ∂μ) →
        stdPoly E (fun i => Matrix.toLin' (ρ (g i))) = 0) →
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
      (∀ v, Continuous fun x => σ x v) → ∀ E : H →L[ℂ] H, (∀ u, E u = ∫ k : K, e k • σ k u ∂μ) →
        stdPoly E (fun i => σ (g i)) = 0
def ExistsAvg : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [SecondCountableTopology K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : K →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → (∀ v, Continuous fun x => σ x v) →
    ∀ (S : Submodule ℂ H) [FiniteDimensional ℂ S], (∀ k, ∀ v ∈ S, σ k v ∈ S) → ∀ v ∈ S,
      ∃ (e : K → ℂ) (E : H →L[ℂ] H), Continuous e ∧ RFin e (Module.finrank ℂ S) ∧
        (∀ u, E u = ∫ k, e k • σ k u ∂μ) ∧ E v = v
def Iwa {n : ℕ} (ε : Fin n → Bool) : Prop :=
  ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ UJset ε, ∃ k ∈ Kset ε, ∃ s ∈ UJset ε,
    g = k * s ∧ (Uᴴ * s * U).BlockTriangular id
def IwaHpk : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    IsCayleyU k r ε P → Iwa ε
def IwaAll : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), Iwa ε
def GardingFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y],
      (∀ T : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y) →
      ∀ v ∈ Y, SmoothOnH (Jm ε) fun g => σ g v
def AdmUJ {n : ℕ} (ε : Fin n → Bool) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ (S : Submodule ℂ H) [FiniteDimensional ℂ S], IsKStableOn ε σ S → ∀ v ∈ S,
      ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ Module.finrank ℂ Y ≤ Module.finrank ℂ S ^ 2 + 1 ∧ v ∈ Y ∧
        ∀ T : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y
end CompanionTheory.D.gk.admitted


