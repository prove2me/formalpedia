-- Prove2me | Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
-- name    : Formalism_RankGapBounds_TheoremALocOfLemmaA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:53.750792+00:00
-- url     : https://prove2.me/theorems/8b2acc1f-f3f4-4a12-982f-a4456088c42d
-- title:
--   Theorem ALoc Of Lemma A
-- statement:
--   Definitions and structural lemmas for Theorem ALoc Of Lemma A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/TheoremALocOfLemmaA.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
namespace Formalism.RankGapBounds.FormsTensorLocalization
open Formalism.UG
def LatIncl {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (e : ℕ) : Prop :=
  ∀ x : A, l ^ e • x ∈ B
def tensSub {k : Type} [CommRing k] {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) : Submodule k (⨂[k] i, A i) :=
  LinearMap.range (PiTensorProduct.map fun i => (B i).subtype)
def formsIn {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] (Γ K : Subgroup G) (ρK : Representation k K W) (U : Submodule k W) :
    Submodule k (G → W) :=
  AMFK k Γ K ρK ⊓ Submodule.pi Set.univ (fun _ => U)
def IsStable {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] {K : Subgroup G} (ρK : Representation k K W) (U : Submodule k W) : Prop :=
  ∀ κ : K, ∀ x ∈ U, ρK κ x ∈ U
def resRep {G : Type} [Group G] {k : Type} [CommRing k] {W : Type} [AddCommGroup W]
    [Module k W] {K : Subgroup G} (ρK : Representation k K W) (U : Submodule k W)
    (hU : IsStable ρK U) : Representation k K U where
  toFun κ := (ρK κ).restrict (hU κ)
  map_one' := by ext x; simp
  map_mul' κ κ' := by ext x; simp [map_mul]
def locSet {T : Type} [CommRing T] {M : Type} [AddCommGroup M] [Module T M]
    (S : Submonoid T) (N : Set M) : Set (LocalizedModule S M) :=
  {y | ∃ x ∈ N, ∃ s : S, LocalizedModule.mk x s = y}
def LemmaA {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A]
    (l : k) (B : Submodule k A) (e : ℕ) : Prop :=
  LatIncl l B e
def TensorStep : Prop :=
  ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (A : ι → Type) [∀ i, AddCommGroup (A i)]
    [∀ i, Module k (A i)] (B : ∀ i, Submodule k (A i)) (l : k) (e : ι → ℕ),
    (∀ i, LatIncl l (B i) (e i)) → ∀ y : ⨂[k] i, A i, l ^ (∑ i, e i) • y ∈ tensSub B
def FunctStep : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (W : Type)
    [AddCommGroup W] [Module k W] (ρK : Representation k K W) (U V : Submodule k W) (l : k)
    (e : ℕ), (∀ x ∈ V, l ^ e • x ∈ U) → ∀ f ∈ formsIn Γ K ρK V, l ^ e • f ∈ formsIn Γ K ρK U
def FormsInEquiv : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (W : Type)
    [AddCommGroup W] [Module k W] (ρK : Representation k K W) (U : Submodule k W)
    (hU : IsStable ρK U),
    ∃ e : AMFK k Γ K (resRep ρK U hU) ≃ₗ[k] formsIn Γ K ρK U,
      ∀ f g, (e f : G → W) g = ((f : G → U) g : W)
def HeckeValStep : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (k : Type) [CommRing k]
    (W : Type) [AddCommGroup W] [Module k W] (U : Submodule k W) (f : G₁ → k)
    (φ : G₁ × G₂ → W), (∀ g, φ g ∈ U) → ∀ g, hActK K₁ f φ g ∈ U
def LocStep : Prop :=
  ∀ (T : Type) [CommRing T] (M : Type) [AddCommGroup M] [Module T M] (S : Submonoid T)
    (N : Set M) (t : T) (e : ℕ), (∀ x : M, t ^ e • x ∈ N) →
    ∀ y : LocalizedModule S M, t ^ e • y ∈ locSet S N
def TheoremA_of_LemmaA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k) (e : ι → ℕ),
    (∀ i, LemmaA l (B i) (e i)) →
    ∀ f ∈ AMFK k Γ K ρK, l ^ (∑ i, e i) • f ∈ formsIn Γ K ρK (tensSub B)
def TheoremA_loc_of_LemmaA : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (k : Type) [CommRing k] (ι : Type) [Fintype ι]
    (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
    (B : ∀ i, Submodule k (A i)) (ρK : Representation k K (⨂[k] i, A i)) (l : k) (e : ι → ℕ)
    (T : Type) [CommRing T] [Algebra k T] [Module T (AMFK k Γ K ρK)]
    [IsScalarTower k T (AMFK k Γ K ρK)] (S : Submonoid T),
    (∀ i, LemmaA l (B i) (e i)) →
    ∀ y : LocalizedModule S (AMFK k Γ K ρK),
      (algebraMap k T l) ^ (∑ i, e i) • y ∈
        locSet S {x : AMFK k Γ K ρK | (x : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)}
end Formalism.RankGapBounds.FormsTensorLocalization


