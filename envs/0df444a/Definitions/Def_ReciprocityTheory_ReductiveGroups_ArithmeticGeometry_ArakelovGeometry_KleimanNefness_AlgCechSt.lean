-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:55.262444+00:00
-- url     : https://prove2.me/theorems/ac81440c-d34b-43b0-90fb-37ff3ec6a2af
-- title:
--   Alg Cech St
-- statement:
--   Definitions and structural lemmas for Alg Cech St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AlgCechSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def CechDSqStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (n : ℕ),
    (cechD S ι M (n + 1)).comp (cechD S ι M n) = 0
def CechDDegStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ),
    ∀ φ ∈ cechCc ι 𝓜 c n, cechD S ι M n φ ∈ cechCc ι 𝓜 c (n + 1)
def CechMapDegStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
    [IsScalarTower S (MRingOver S ι) N]
    (𝓜 : (K → ℤ) → Submodule S M) (𝓝 : (K → ℤ) → Submodule S N) (g : M →ₗ[MRingOver S ι] N)
    (c : K → ℤ) (n : ℕ),
    IsMGradedMap S ι 𝓜 𝓝 g →
    (∀ φ ∈ cechCc ι 𝓜 c n, cechMap S ι g n φ ∈ cechCc ι 𝓝 c n) ∧
      (cechD S ι N n).comp (cechMap S ι g n) = (cechMap S ι g (n + 1)).comp (cechD S ι M n)
def CechTopStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ),
    ∑ k, (Fintype.card (ι k) - 1) < n → Subsingleton (cechHc ι 𝓜 c n)
def CechSESStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M'']
    (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
    (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
    IsMGraded S ι 𝓜' → IsMGraded S ι 𝓜 → IsMGraded S ι 𝓜'' →
    IsMGradedMap S ι 𝓜' 𝓜 g → IsMGradedMap S ι 𝓜 𝓜'' h →
    Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
    ∀ (c : K → ℤ) (n : ℕ),
      (Subsingleton (cechHc ι 𝓜' c n) → Subsingleton (cechHc ι 𝓜'' c n) →
        Subsingleton (cechHc ι 𝓜 c n)) ∧
      (Subsingleton (cechHc ι 𝓜 c n) → Subsingleton (cechHc ι 𝓜' c (n + 1)) →
        Subsingleton (cechHc ι 𝓜'' c n)) ∧
      (IsNoetherianRing S → Module.Finite S (cechHc ι 𝓜' c n) → Module.Finite S (cechHc ι 𝓜'' c n) →
        Module.Finite S (cechHc ι 𝓜 c n)) ∧
      (IsNoetherianRing S → Module.Finite S (cechHc ι 𝓜 c n) →
        Module.Finite S (cechHc ι 𝓜' c (n + 1)) → Module.Finite S (cechHc ι 𝓜'' c n)) ∧
      (Subsingleton (cechHc ι 𝓜' c 1) →
        ∀ z'' ∈ cechZc ι 𝓜'' c 0, ∃ z ∈ cechZc ι 𝓜 c 0, cechMap S ι h 0 z = z'') ∧
      (∀ z ∈ cechZc ι 𝓜 c 0, cechMap S ι h 0 z = 0 → ∃ z' ∈ cechZc ι 𝓜' c 0, cechMap S ι g 0 z' = z)
def TheoremSStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    (∀ (c : K → ℤ) (n : ℕ), Module.Finite S (cechHc ι 𝓜 c n)) ∧
    (∃ c₀ : ℤ, ∀ (c : K → ℤ) (n : ℕ), 1 ≤ n → (∀ k, c₀ ≤ c k) → Subsingleton (cechHc ι 𝓜 c n)) ∧
    (∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ z ∈ cechZc ι 𝓜 c 0,
      ∃ m ∈ 𝓜 c, ∀ I, z I = LocalizedModule.mk m 1) ∧
    (∀ d : K → ℤ, (Submodule.span (MRingOver S ι)
      (⋃ c : ℕ, (cechZc ι 𝓜 (d + fun _ => (c : ℤ)) 0 : Set (CechC S ι M 0)))).FG)
def TheoremSDirStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    (∀ (c : K → ℤ) (n : ℕ), Module.Finite S (cechHc ι 𝓜 c n)) ∧
    (∀ (ν : K → ℕ) (d : K → ℤ), (∀ k, 1 ≤ ν k) → ∃ τ₀ : ℕ, ∀ τ : ℕ, τ₀ ≤ τ →
      (∀ n : ℕ, 1 ≤ n → Subsingleton (cechHc ι 𝓜 (d + fun k => ((τ * ν k : ℕ) : ℤ)) n)) ∧
      (∀ z ∈ cechZc ι 𝓜 (d + fun k => ((τ * ν k : ℕ) : ℤ)) 0,
        ∃ m ∈ 𝓜 (d + fun k => ((τ * ν k : ℕ) : ℤ)), ∀ I, z I = LocalizedModule.mk m 1)) ∧
    (∀ d : K → ℤ, (Submodule.span (MRingOver S ι)
      (⋃ c : ℕ, (cechZc ι 𝓜 (d + fun _ => (c : ℤ)) 0 : Set (CechC S ι M 0)))).FG)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


