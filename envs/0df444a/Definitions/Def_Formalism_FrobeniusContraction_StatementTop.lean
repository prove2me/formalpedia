-- Prove2me | Definitions.Def_Formalism_FrobeniusContraction_StatementTop
-- name    : Formalism_FrobeniusContraction_StatementTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:46.6348+00:00
-- url     : https://prove2.me/theorems/305acd7c-8323-43ac-bf39-10c3f2fae66f
-- title:
--   Statement Top
-- statement:
--   Definitions and structural lemmas for Statement Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/StatementTop.lean

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
open Classical
namespace Formalism.WachCohomologyFacts.Top
def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i - ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋
def InWin (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 0 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ h
def FarWin (G : Bool) (h η : ℕ) (d x : ℤ) : Prop :=
  if G then x < -d ∨ (η : ℤ) + d < x else x < (h : ℤ) - η - d ∨ (h : ℤ) + d < x
def Low (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (InWin G h η)
def Cl (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U - Low G h η U
def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)
def T1 (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ
def T2 (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ Low G h η U, ∀ y ∈ GlobalTheory w t, σ + 2 < |x - y|
def T3' (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ Cl G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)
def SgBound : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (m : ZMod f → ℤ),
    2 ≤ ℓ → (∀ i, (ℓ : ℤ) * m (i + 1) ≤ m i + h i) → ∀ i, m i ≤ sg f ℓ h i
def LemmaS : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ t M : ℕ) (h w η σ : ZMod f → ℕ) (G : ZMod f → Bool)
    (k : ℕ → ℕ → ZMod f → ℤ),
    1 ≤ t → 1 ≤ M → (∀ i, w i + t - 1 ≤ h i) →
    (∀ i, G i = true → w i + t - 1 ≤ η i) → (∀ i, G i = false → (h i : ℤ) - η i ≤ w i) →
    (∀ i, η i + 4 * σ i + 6 < ℓ) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → |k c μ i| ≤ σ i) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M →
      0 ≤ (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i + 1) - k c μ i ∧
      (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i + 1) - k c μ i ≤ h i) →
    (∀ i, (Finset.Icc 1 t ×ˢ Finset.Icc 1 M).val.map
        (fun cμ : ℕ × ℕ => (((w i : ℤ) + cμ.1 - 1 - k cμ.1 cμ.2 i : ℤ) : ZMod ℓ)) =
      M • (Finset.Icc 1 t).val.map (fun c : ℕ => (((w i : ℤ) + c - 1 : ℤ) : ZMod ℓ))) →
    ∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → k c μ i = 0
def LemmaD : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (H : Type) [AddCommGroup H] [Module O H]
    (Hf : Submodule O H)
    (adm : ∀ (X : Type) [AddCommGroup X] [Module O X], Submodule O (TensorProduct O H X)),
    (∀ (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y],
      IsFiniteLength O X → IsFiniteLength O Y → ∀ g : X →ₗ[O] Y,
        (adm X).map (g.lTensor H) ≤ adm Y) →
    (∀ (X : Type) [AddCommGroup X] [Module O X], IsFiniteLength O X →
      LinearMap.range (Hf.subtype.rTensor X) ≤ adm X) →
    (∀ (X : Type) [AddCommGroup X] [Module O X] (X₁ : Submodule O X), IsFiniteLength O X →
      (adm X).comap (X₁.subtype.lTensor H) = adm X₁) →
    adm (IsLocalRing.ResidueField O) = LinearMap.range (Hf.subtype.rTensor _) →
    ∀ (X : Type) [AddCommGroup X] [Module O X], IsFiniteLength O X →
      adm X = LinearMap.range (Hf.subtype.rTensor X)
def TopCor : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ t : ℕ) (h w η : ZMod f → ℕ) (G : ZMod f → Bool)
    (U : ZMod f → Multiset ℤ),
    (∀ i, ∀ x ∈ U i, 0 ≤ x ∧ x ≤ h i) →
    (∀ i, h i + 2 < ℓ) → (∀ i, η i + 6 < ℓ) →
    (∀ i, ∀ x ∈ Low (G i) (h i) (η i) (U i), ∀ y ∈ GlobalTheory (w i) t, 2 < |x - y|) →
    (∀ i, ∀ x ∈ Cl (G i) (h i) (η i) (U i), FarWin (G i) (h i) (η i) 3 x) →
    ∀ i, sg f ℓ h i = 0 ∧ T1 ℓ (η i) (sg f ℓ h i) ∧
      T2 (G i) (h i) (η i) (w i) t (sg f ℓ h i) (U i) ∧
      T3' ℓ (G i) (h i) (η i) (sg f ℓ h i) (U i)
end Formalism.WachCohomologyFacts.Top


