-- Prove2me | Definitions.Def_Formalism_FrobeniusContraction_HighestWeightResidueAvoids
-- name    : Formalism_FrobeniusContraction_HighestWeightResidueAvoids
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:31.30335+00:00
-- url     : https://prove2.me/theorems/80a1a524-0d7e-4651-8804-4f7f014323e8
-- title:
--   Highest Weight Residue Avoids
-- statement:
--   Definitions and structural lemmas for Highest Weight Residue Avoids, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/HighestWeightResidueAvoids.lean

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_StatementTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace Formalism.WachCohomologyFacts.V2
open Formalism.WachCohomologyFacts
def FrobContractsSharp : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h : ℕ),
    h < (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    (∀ x ∈ W.XMN M, W.Φ x ∈ Ideal.span {B.q} • W.XMN M) ∧
      ∀ k : ℕ, ∀ x ∈ B.I ^ k • W.XMN M, W.Φ x ∈ B.I ^ (k + 1) • W.XMN M
def FrobSubIdUniqueSharp : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h : ℕ),
    h < (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    IsAdicComplete B.I ↥(W.XMN M) →
    (∀ y ∈ W.XMN M, ∃! x, x ∈ W.XMN M ∧ W.Φ x - x = y) ∧
      ∀ y ∈ W.XMN M, ∀ z ∈ W.XMN M, W.Φ z - z = W.Γ y - y → (y, z) ∈ W.B1
def Sat : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (ι : Type) [Fintype ι]
    (ℓ f f' : A), IsRelPrime ℓ (f * f') →
    ∀ x : ι → FractionRing A,
      (∀ i, ∃ a : A, algebraMap A (FractionRing A) f' * x i = algebraMap A (FractionRing A) a) →
      (∃ k : ℕ, ∀ i, ∃ a : A,
        algebraMap A (FractionRing A) (ℓ ^ k) * x i = algebraMap A (FractionRing A) (f * a)) →
      ∀ i, ∃ a : A, x i = algebraMap A (FractionRing A) (f * a)
def sgN (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋
def SgBoundN : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (m : ZMod f → ℤ),
    2 ≤ ℓ → (∀ i, (ℓ : ℤ) * m (i - 1) ≤ m i + h i) → ∀ i, m i ≤ sgN f ℓ h i
def IneqIN : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    sgN f ℓ h i < (ℓ : ℤ) * (sgN f ℓ h (i - 1) + 1) - h i
def LemmaSN : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ t M : ℕ) (h w η σ : ZMod f → ℕ) (G : ZMod f → Bool)
    (k : ℕ → ℕ → ZMod f → ℤ),
    1 ≤ t → 1 ≤ M →
    (∀ i, G i = true → 1 ≤ w i ∧ w i + t - 1 ≤ η i) →
    (∀ i, G i = false → (h i : ℤ) - η i ≤ w i ∧ w i + t ≤ h i) →
    (∀ i, η i + 4 * σ i + 6 < ℓ) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → |k c μ i| ≤ σ i) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M →
      0 ≤ (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i - 1) - k c μ i ∧
      (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i - 1) - k c μ i ≤ h i) →
    (∀ i, (Finset.Icc 1 t ×ˢ Finset.Icc 1 M).val.map
        (fun cμ : ℕ × ℕ => (((w i : ℤ) + cμ.1 - 1 - k cμ.1 cμ.2 i : ℤ) : ZMod ℓ)) =
      M • (Finset.Icc 1 t).val.map (fun c : ℕ => (((w i : ℤ) + c - 1 : ℤ) : ZMod ℓ))) →
    ∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → k c μ i = 0
def InWinN (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 1 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ (h : ℤ) - 1
def ClN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (fun x => ¬ InWinN G h η x)
def ResidueAvoidance (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ ClN G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)
def HighestWeightResidueAvoids : Prop :=
  (∀ (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ), 0 ≤ σ →
    (∀ x ∈ U, 0 ≤ x ∧ x ≤ h) → (h : ℤ) + 2 * σ + η + 5 < ℓ →
    (∀ x ∈ ClN G h η U, (η : ℤ) + 2 * σ + 3 < (if G then x else (h : ℤ) - x)) →
    ResidueAvoidance ℓ G h η σ U) ∧
  (∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), (∀ i, h i + 2 < ℓ) → ∀ i, sgN f ℓ h i = 0)
end Formalism.WachCohomologyFacts.V2


