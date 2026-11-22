-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelPairSetVariant
-- name    : Formalism_CharacterColumnKernels_CharacterColumnKernelPairSetVariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:50.673623+00:00
-- url     : https://prove2.me/theorems/cefd8b91-9997-4cf3-bbca-e4fb0da68e5f
-- title:
--   Character Column Kernel Pair Set Variant
-- statement:
--   Definitions and structural lemmas for Character Column Kernel Pair Set Variant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/CharacterColumnKernelPairSetVariant.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.NG
section Cochains
variable {O : Type*} [CommRing O] {D : Type*} [Group D] {M : Type*} [AddCommGroup M] [Module O M]
def coD0 (ρ : Representation O D M) : M →ₗ[O] (D → M) where
  toFun v g := ρ g v - v
  map_add' v w := by ext g; simp only [map_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]
def coB1 (ρ : Representation O D M) : Submodule O (D → M) := LinearMap.range (coD0 ρ)
def characterColumnKernelSet (ρ : Representation O D M) : Set (D → M) :=
  {c | ∀ g h, c (g * h) = c g + ρ g (c h)}
def characterColumnKernelPairSetVariant (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0}
def characterColumnKernelPairSet (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∃ b : D → M, ∀ g h, c g h = ρ g (b h) - b (g * h) + b g}
end Cochains
def cup1 {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₂ : Representation O D M₂) (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (a : D → M₁) (b : D → M₂) :
    D → D → N :=
  fun g h => β (a g) (ρ₂ g (b h))
def IsEquivPairing {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρN : Representation O D N)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) : Prop :=
  ∀ g m n, β (ρ₁ g m) (ρ₂ g n) = ρN g (β m n)
def IsEquivMap {O D M M' : Type*} [CommRing O] [Group D] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (ρ : Representation O D M) (ρ' : Representation O D M')
    (f : M →ₗ[O] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)
def StatCupKill : Prop :=
  ∀ (O D M₁ M₂ M₂' N N' M₁'' M₂'' P : Type*) [CommRing O] [Group D]
    [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂] [Module O M₂] [AddCommGroup M₂'] [Module O M₂']
    [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N'] [AddCommGroup M₁''] [Module O M₁'']
    [AddCommGroup M₂''] [Module O M₂''] [AddCommGroup P] [Module O P]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρ₂' : Representation O D M₂')
    (ρN : Representation O D N) (ρN' : Representation O D N') (ρ₁'' : Representation O D M₁'')
    (ρ₂'' : Representation O D M₂'') (ρP : Representation O D P)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (β' : M₁ →ₗ[O] M₂' →ₗ[O] N') (γ : M₁'' →ₗ[O] M₂'' →ₗ[O] P)
    (j : M₂ →ₗ[O] M₂') (ι : N →ₗ[O] N') (π : M₁ →ₗ[O] M₁'') (φ : M₂ →ₗ[O] M₂'') (ψ : N →ₗ[O] P),
    IsEquivPairing ρ₁ ρ₂ ρN β → IsEquivPairing ρ₁ ρ₂' ρN' β' → IsEquivMap ρ₂ ρ₂' j →
    IsEquivMap ρN ρN' ι → IsEquivMap ρ₁ ρ₁'' π → IsEquivMap ρ₂ ρ₂'' φ → IsEquivMap ρN ρP ψ →
    (∀ m n, ι (β m n) = β' m (j n)) → (∀ m n, γ (π m) (φ n) = ψ (β m n)) →
    (∀ z ∈ characterColumnKernelPairSetVariant ρN, (fun g h => ι (z g h)) ∈ characterColumnKernelPairSet ρN' → z ∈ characterColumnKernelPairSet ρN) →
    ∀ (a : D → M₁) (b : D → M₂) (e : M₂'), a ∈ characterColumnKernelSet ρ₁ → b ∈ characterColumnKernelSet ρ₂ →
      (∀ g, j (b g) = ρ₂' g e - e) →
      cup1 ρ₂'' γ (fun g => π (a g)) (fun g => φ (b g)) ∈ characterColumnKernelPairSet ρP
abbrev ColFree (A : Type*) [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (ι : Type*) (j : ℕ) : Type _ :=
  Ymod r χ E × (ι → A × (Fin j → A) × A)
def colGen {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ℕ} (y : Ymod r χ E) (l : ι)
    (c : A) (s : Fin j → A) (c₀ : A) : ColFree A r χ E ι j :=
  (y, Pi.single l (c, s, c₀))
def colRel {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ℕ) (Kc : ι → Fin j → G → A) (k0 : ι → G → A) : Submodule A (ColFree A r χ E ι j) :=
  Submodule.span A
    ({z | ∃ l, z = colGen 0 l E 0 0} ∪
     {z | ∃ l a, z = colGen 0 l 0 (Pi.single a (1 - e₁)) 0} ∪
     {z | ∃ l, z = colGen 0 l 0 0 (algebraMap T' A δ - E)} ∪
     {z | ∃ l, ∃ g ∈ D l, z = colGen ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1)
        (fun a => -(algebraMap T' A δ * Kc l a g)) (-(algebraMap T' A δ * k0 l g))})
abbrev ColNN {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ℕ) (Kc : ι → Fin j → G → A) (k0 : ι → G → A) : Type _ :=
  ColFree A r χ E ι j ⧸ colRel r χ E e₁ δ D j Kc k0
def colD {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) : V →ₗ[K] (D → V) where
  toFun v g := ((((χ g)⁻¹ : T'ˣ) : T') • r g) • v - v
  map_add' v w := by ext g; simp only [smul_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm]
def StatColumn : Prop :=
  ∀ (A T' K V G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V] [FiniteDimensional K V]
    [Module T' V] [IsScalarTower T' A V]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ℕ) (Kc : ι → Fin j → G → A) (k0 : ι → G → A),
    E * E = algebraMap T' A δ * E → e₁ * e₁ = e₁ →
    ∀ δx : K, δx ≠ 0 → (∀ v : V, δ • v = δx • v) →
    Module.finrank K (LinearMap.range (DistribSMul.toLinearMap K V E)) = 1 →
    Module.finrank K (LinearMap.range (DistribSMul.toLinearMap K V e₁)) = 1 →
    (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap K V E), η ≠ 0 →
      ∃ g : G, ((((χ g)⁻¹ : T'ˣ) : T') • r g) • η ≠ η) →
    (∀ l, ∃ L : Submodule K (D l → V),
      LinearMap.range (colD (K := K) (V := V) r χ (D l)) ≤ L ∧
      (∀ a, ∀ s ∈ LinearMap.range (DistribSMul.toLinearMap K V e₁),
        (fun g : D l => Kc l a g • s) ∈ L) ∧
      (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap K V E), (fun g : D l => k0 l g • s) ∈ L) ∧
      Module.rank K (L ⧸ (LinearMap.range (colD (K := K) (V := V) r χ (D l))).comap L.subtype) ≤
        (j + Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ (D l))) : ℕ)) →
    ∃ φ : ColNN r χ E e₁ δ D j Kc k0 →ₗ[A] V, φ ≠ 0
end Formalism.NG


