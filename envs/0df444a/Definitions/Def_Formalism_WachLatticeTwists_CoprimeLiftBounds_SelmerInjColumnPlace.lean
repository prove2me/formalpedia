-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_SelmerInjColumnPlace
-- name    : Formalism_WachLatticeTwists_CoprimeLiftBounds_SelmerInjColumnPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:27:55.447852+00:00
-- url     : https://prove2.me/theorems/0ed89444-d51d-4fc7-97a8-68ed7d719280
-- title:
--   Selmer Inj Column Place
-- statement:
--   Definitions and structural lemmas for Selmer Inj Column Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/CoprimeLiftBounds/SelmerInjColumnPlace.lean

import Definitions.Def_Formalism_WachLatticeTwists_CoprimeLiftBounds_Statement
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
namespace Formalism.RepresentationBoundsCohomology.BR
open Formalism.NG
def StatLiftOver : Prop :=
  ∀ (O D M₁ M₂ : Type*) [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂]
    [Module O M₂] (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (p : M₁ →ₗ[O] M₂),
    IsEquivMap ρ₁ ρ₂ p → Function.Surjective p →
    ∀ (K' : coZ1s ρ₁) (κ : coZ1s ρ₂),
      (∃ w : M₂, ∀ g, p ((K' : D → M₁) g) = (κ : D → M₂) g + (ρ₂ g w - w)) →
      ∃ K : coZ1s ρ₁, (Submodule.mkQ _ K : H1z ρ₁) = Submodule.mkQ _ K' ∧
        ∀ g, p ((K : D → M₁) g) = (κ : D → M₂) g
def SelmerInjTensorForm : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (D : Type*) [Group D] (L V M : Type*) [AddCommGroup L] [Module O L] [AddCommGroup V]
    [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup M] [Module O M]
    (ρL : Representation O D L) (ρV : Representation (FractionRing O) D V)
    (ρM : Representation O D M) (i : L →ₗ[O] V) (q : V →ₗ[O] M)
    (tens : L →ₗ[O] KO O →ₗ[O] M),
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = q (x • i v)) →
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    (∀ g v, i (ρL g v) = ρV g (i v)) → (∀ g v, q (ρV g v) = ρM g (q v)) →
    ∀ (Ff : Submodule O (H1z ρL)) (j : ℕ) (κ : Fin j → coZ1s ρL),
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, (Submodule.mkQ _ (κ a) : H1z ρL) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL)) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 → b = 0) →
    ∀ (x : Fin j → KO O) (m : M),
      (∀ g, ∑ a, tens ((κ a : D → L) g) (x a) = ρM g m - m) → ∀ a, x a = 0
def SelmerInjColumnPlace : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (V : Type*) [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [SMulCommClass A (FractionRing O) V]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (i : L →ₗ[O] V) (q : V →ₗ[O] M)
    (tens : L →ₗ[O] KO O →ₗ[O] M),
    (∀ (a : A) v, i (a • v) = a • i v) → (∀ (a : A) v, q (a • v) = a • q v) →
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = q (x • i v)) →
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    ∀ (Ff : Submodule O (H1z (resRep (uRep O (M := L) r χ) Dl))) (j : ℕ) (κ : Fin j → G → L)
      (κz : Fin j → coZ1s (resRep (uRep O (M := L) r χ) Dl)),
    (∀ a (g : Dl), (κz a : Dl → L) g = κ a g) →
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, Submodule.mkQ _ (κz a) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κz a) : H1z (resRep (uRep O (M := L) r χ) Dl))) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κz a) : H1z (resRep (uRep O (M := L) r χ) Dl)) = 0 →
      b = 0) →
    ∀ x : Fin j → KO O, (fun g : Dl => ∑ a, tens (κ a g) (x a)) ∈
      LinearMap.range (colDO (O := O) (M := M) r χ Dl) → ∀ a, x a = 0
end Formalism.RepresentationBoundsCohomology.BR


