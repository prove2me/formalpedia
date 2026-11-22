-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
-- name    : Formalism_CharacterColumnKernels_StatGlobalModule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:32.698837+00:00
-- url     : https://prove2.me/theorems/3f39be81-0b75-4b23-92be-f035f75e546a
-- title:
--   Stat Global Module
-- statement:
--   Definitions and structural lemmas for Stat Global Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatGlobalModule.lean

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelPairSetVariant
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
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
abbrev ColFreeJ (A : Type*) [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (ι : Type*) (j : ι → ℕ) : Type _ :=
  Ymod r χ E × ((l : ι) → A × (Fin (j l) → A) × A)
def colGenJ {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ} (y : Ymod r χ E)
    (l : ι) (c : A) (s : Fin (j l) → A) (c₀ : A) : ColFreeJ A r χ E ι j :=
  (y, Pi.single (M := fun l => A × (Fin (j l) → A) × A) l (c, s, c₀))
def colRelJ {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) : Submodule A (ColFreeJ A r χ E ι j) :=
  Submodule.span A
    ({z | ∃ l, z = colGenJ 0 l E 0 0} ∪
     {z | ∃ l a, z = colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0} ∪
     {z | ∃ l, z = colGenJ 0 l 0 0 (algebraMap T' A δ - E)} ∪
     {z | ∃ l, ∃ g ∈ D l, z = colGenJ ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1)
        (fun a => -(algebraMap T' A δ * Kc l a g)) (-(algebraMap T' A δ * k0 l g))})
abbrev ColNNJ {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) : Type _ :=
  ColFreeJ A r χ E ι j ⧸ colRelJ r χ E e₁ δ D j Kc k0
def StatColumnJ : Prop :=
  ∀ (A T' K V G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V] [FiniteDimensional K V]
    [Module T' V] [IsScalarTower T' A V]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A),
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
        (j l + Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ (D l))) : ℕ)) →
    ∃ φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] V, φ ≠ 0
def StatCupKillAdm : Prop :=
  ∀ (O D M₁ M₂ M₂' N N' M₁'' M₂'' P : Type*) [CommRing O] [Group D]
    [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂] [Module O M₂] [AddCommGroup M₂'] [Module O M₂']
    [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N'] [AddCommGroup M₁''] [Module O M₁'']
    [AddCommGroup M₂''] [Module O M₂''] [AddCommGroup P] [Module O P]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρ₂' : Representation O D M₂')
    (ρN : Representation O D N) (ρN' : Representation O D N') (ρ₁'' : Representation O D M₁'')
    (ρ₂'' : Representation O D M₂'') (ρP : Representation O D P)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (β' : M₁ →ₗ[O] M₂' →ₗ[O] N') (γ : M₁'' →ₗ[O] M₂'' →ₗ[O] P)
    (j : M₂ →ₗ[O] M₂') (ι : N →ₗ[O] N') (π : M₁ →ₗ[O] M₁'') (φ : M₂ →ₗ[O] M₂'') (ψ : N →ₗ[O] P)
    (CN2 : (D → D → N) → Prop) (CN : (D → N) → Prop) (CN' : (D → N') → Prop) (CP : (D → P) → Prop),
    IsEquivPairing ρ₁ ρ₂ ρN β → IsEquivPairing ρ₁ ρ₂' ρN' β' → IsEquivMap ρ₂ ρ₂' j →
    IsEquivMap ρN ρN' ι → IsEquivMap ρ₁ ρ₁'' π → IsEquivMap ρ₂ ρ₂'' φ → IsEquivMap ρN ρP ψ →
    (∀ m n, ι (β m n) = β' m (j n)) → (∀ m n, γ (π m) (φ n) = ψ (β m n)) →
    (∀ f, CN f → CP (fun g => ψ (f g))) →
    (∀ z ∈ characterColumnKernelPairSetVariant ρN, CN2 z →
      (∃ f, CN' f ∧ ∀ g h, ι (z g h) = ρN' g (f h) - f (g * h) + f g) →
      ∃ c, CN c ∧ ∀ g h, z g h = ρN g (c h) - c (g * h) + c g) →
    ∀ (a : D → M₁) (b : D → M₂) (e : M₂'), a ∈ characterColumnKernelSet ρ₁ → b ∈ characterColumnKernelSet ρ₂ →
      (∀ g, j (b g) = ρ₂' g e - e) →
      CN2 (cup1 ρ₂ β a b) → CN' (fun g => -β' (a g) (ρ₂' g e)) →
      ∃ c, CP c ∧ ∀ g h, cup1 ρ₂'' γ (fun g => π (a g)) (fun g => φ (b g)) g h =
        ρP g (c h) - c (g * h) + c g
def StatFinPres : Prop :=
  ∀ (R : Type*) [Ring R] [IsNoetherian R R] (M : Type*) [AddCommGroup M] [Module R M]
    (g₀ : ℕ) (n : Fin g₀ → M), Submodule.span R (Set.range n) = ⊤ →
    ∃ (m : ℕ) (P : Matrix (Fin m) (Fin g₀) R), Nonempty (M ≃ₗ[R] Coker P)
def StatGlobalModule : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type*)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      [IsNoetherian R' R'],
    (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    ∀ (NN : Type*) [AddCommGroup NN] [Module R' NN] (g₀ : ℕ) (n : Fin g₀ → NN),
      Submodule.span R' (Set.range n) = ⊤ →
    (∀ x', p x' ∉ Z → ∃ φ : NN →ₗ[R'] EvalSp O d R' x', φ ≠ 0) →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (α : Type) [LinearOrder α] [Fintype α] (bl : d → α), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      [∀ k, SMulCommClass R' O (LatQ O {a // bl a = k} (ρk k).toRingHom)] →
      ((g₀ * ∑ k : α, Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      vcc T Z (p π') ≤
        ∑ k ∈ univ.image bl, Module.length O (NN →ₗ[R'] LatQ O {a // bl a = k} (ρk k).toRingHom)
end Formalism.NG


