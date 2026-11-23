-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:13.520386+00:00
-- url     : https://prove2.me/theorems/6abf1ef4-735b-41ea-8799-b4f952c42d37
-- title:
--   Exists Finite Affine Cover
-- statement:
--   Definitions and structural lemmas for Exists Finite Affine Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter
namespace GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
section Ring
variable (A : ι → Type) [∀ i, CommRing (A i)]
def nullIdeal : Ideal (∀ i, A i) where
  carrier := {a | ∀ᶠ i in (U : Filter ι), a i = 0}
  add_mem' := by
    intro a b ha hb
    filter_upwards [ha, hb] with i h1 h2
    simp [h1, h2]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    filter_upwards [ha] with i h1
    simp [h1]
abbrev Ult : Type := (∀ i, A i) ⧸ nullIdeal U A
variable {A}
def mk : (∀ i, A i) →+* Ult U A := Ideal.Quotient.mk _
lemma mk_surjective : Function.Surjective (mk U (A := A)) := Ideal.Quotient.mk_surjective
lemma mk_eq_mk_iff {a b : ∀ i, A i} : mk U a = mk U b ↔ ∀ᶠ i in (U : Filter ι), a i = b i := by
  unfold mk
  rw [Ideal.Quotient.eq]
  change (∀ᶠ i in (U : Filter ι), (a - b) i = 0) ↔ _
  simp [sub_eq_zero]
lemma mk_eq_zero_iff {a : ∀ i, A i} : mk U a = 0 ↔ ∀ᶠ i in (U : Filter ι), a i = 0 := by
  rw [← map_zero (mk U), mk_eq_mk_iff]; rfl
lemma nullIdeal_isPrime [∀ i, IsDomain (A i)] : (nullIdeal U A).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    obtain ⟨i, hi⟩ := Filter.Eventually.exists (show ∀ᶠ i in (U : Filter ι), (1 : ∀ i, A i) i = 0 from h)
    exact one_ne_zero hi
  · intro a b h
    have h' : ∀ᶠ i in (U : Filter ι), a i = 0 ∨ b i = 0 := by
      filter_upwards [show ∀ᶠ i in (U : Filter ι), (a * b) i = 0 from h] with i hi
      simpa using hi
    exact Ultrafilter.eventually_or.1 h'
instance [∀ i, IsDomain (A i)] : IsDomain (Ult U A) :=
  haveI := nullIdeal_isPrime U (A := A)
  Ideal.Quotient.isDomain _
end Ring
section Field
variable (K : ι → Type) [∀ i, Field (K i)]
lemma isField_ult : IsField (Ult U K) := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := mk_surjective U x
  refine ⟨mk U (fun i => (a i)⁻¹), ?_⟩
  rw [← map_mul, ← map_one (mk U), mk_eq_mk_iff]
  have : ∀ᶠ i in (U : Filter ι), a i ≠ 0 := by
    have h := (not_congr (mk_eq_zero_iff U)).1 hx
    exact Ultrafilter.eventually_not.2 h
  filter_upwards [this] with i hi
  simp [hi]
instance : Field (Ult U K) := (isField_ult U K).toField
end Field
section Val
variable (V : ι → Type) [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)]
instance : ValuationRing (Ult U V) := by
  refine ValuationRing.iff_dvd_total.2 ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := mk_surjective U x
  obtain ⟨b, rfl⟩ := mk_surjective U y
  have key : ∀ (a b : ∀ i, V i), (∀ᶠ i in (U : Filter ι), a i ∣ b i) → mk U a ∣ mk U b := by
    intro a b h
    have h' : ∀ i, ∃ c, a i ∣ b i → b i = a i * c := by
      intro i
      by_cases hi : a i ∣ b i
      · obtain ⟨c, hc⟩ := hi
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose c hc using h'
    refine ⟨mk U c, ?_⟩
    rw [← map_mul, mk_eq_mk_iff]
    filter_upwards [h] with i hi
    exact hc i hi
  have h : ∀ᶠ i in (U : Filter ι), a i ∣ b i ∨ b i ∣ a i :=
    Filter.Eventually.of_forall fun i => ValuationRing.dvd_total (a i) (b i)
  rcases Ultrafilter.eventually_or.1 h with h | h
  · exact Or.inl (key a b h)
  · exact Or.inr (key b a h)
end Val
section Map
variable {A B : ι → Type} [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
def map (g : ∀ i, A i →+* B i) : Ult U A →+* Ult U B :=
  Ideal.Quotient.lift _ ((mk U).comp (Pi.ringHom fun i => (g i).comp (Pi.evalRingHom A i))) (by
    intro a ha
    have ha' : ∀ᶠ i in (U : Filter ι), a i = 0 := ha
    change mk U _ = 0
    rw [mk_eq_zero_iff]
    filter_upwards [ha'] with i hi
    change g i (a i) = 0
    rw [hi, map_zero])
end Map
section Frac
variable (V K : ι → Type) [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, Field (K i)]
  [∀ i, Algebra (V i) (K i)]
instance : Algebra (Ult U V) (Ult U K) := (map U fun i => algebraMap (V i) (K i)).toAlgebra
lemma algebraMap_mk (a : ∀ i, V i) :
    algebraMap (Ult U V) (Ult U K) (mk U a) = mk U (fun i => algebraMap (V i) (K i) (a i)) := rfl
instance [∀ i, IsFractionRing (V i) (K i)] : IsFractionRing (Ult U V) (Ult U K) := by
  have hinj : Function.Injective (algebraMap (Ult U V) (Ult U K)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := mk_surjective U x
    rw [algebraMap_mk, mk_eq_zero_iff] at hx
    rw [mk_eq_zero_iff]
    filter_upwards [hx] with i hi
    exact (map_eq_zero_iff _ (IsFractionRing.injective (V i) (K i))).1 hi
  haveI : FaithfulSMul (Ult U V) (Ult U K) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field _ _ ?_
  intro z
  obtain ⟨k, rfl⟩ := mk_surjective U z
  have h : ∀ i, ∃ x y : V i, y ≠ 0 ∧ algebraMap (V i) (K i) x / algebraMap (V i) (K i) y = k i := by
    intro i
    obtain ⟨x, y, hy, e⟩ := IsFractionRing.div_surjective (A := V i) (k i)
    exact ⟨x, y, nonZeroDivisors.ne_zero hy, e⟩
  choose x y hy e using h
  have hy' : algebraMap (Ult U V) (Ult U K) (mk U y) ≠ 0 := by
    rw [algebraMap_mk]
    intro h0
    rw [mk_eq_zero_iff] at h0
    obtain ⟨i, hi⟩ := h0.exists
    exact hy i ((map_eq_zero_iff _ (IsFractionRing.injective (V i) (K i))).1 hi)
  refine ⟨mk U x, mk U y, ?_⟩
  rw [eq_div_iff hy', algebraMap_mk, algebraMap_mk, ← map_mul, mk_eq_mk_iff]
  refine Filter.Eventually.of_forall fun i => ?_
  have : algebraMap (V i) (K i) (y i) ≠ 0 := fun h0 =>
    hy i ((map_eq_zero_iff _ (IsFractionRing.injective (V i) (K i))).1 h0)
  simp only [Pi.mul_apply]
  rw [← e i]
  field_simp
end Frac
section Rep
variable {A : ι → Type} [∀ i, CommRing (A i)] {B : Type} [CommRing B]
def IsAEHom (h : ∀ i, B → A i) : Prop := ∀ᶠ i in (U : Filter ι), ∃ p : B →+* A i, ⇑p = h i
def ofFamily (h : ∀ i, B → A i) (h1 : ∀ᶠ i in (U : Filter ι), h i 1 = 1)
    (hadd : ∀ a b, ∀ᶠ i in (U : Filter ι), h i (a + b) = h i a + h i b)
    (hmul : ∀ a b, ∀ᶠ i in (U : Filter ι), h i (a * b) = h i a * h i b) : B →+* Ult U A where
  toFun b := mk U (fun i => h i b)
  map_one' := by
    rw [← map_one (mk U), mk_eq_mk_iff]
    exact h1
  map_mul' a b := by
    rw [← map_mul, mk_eq_mk_iff]
    exact hmul a b
  map_zero' := by
    rw [mk_eq_zero_iff]
    filter_upwards [hadd 0 0] with i hi
    simpa using hi
  map_add' a b := by
    rw [← map_add, mk_eq_mk_iff]
    exact hadd a b
def homOf (h : ∀ i, B → A i) (hh : IsAEHom U h) : B →+* Ult U A :=
  ofFamily U h
    (by filter_upwards [hh] with i ⟨p, hp⟩; rw [← hp, map_one])
    (fun a b => by filter_upwards [hh] with i ⟨p, hp⟩; rw [← hp, map_add])
    (fun a b => by filter_upwards [hh] with i ⟨p, hp⟩; rw [← hp, map_mul])
def Rep (h : ∀ i, B → A i) (g : B →+* Ult U A) : Prop :=
  IsAEHom U h ∧ ∀ b, g b = mk U (fun i => h i b)
end Rep
section Scheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
instance (W : X.affineOpens) : IsOpenImmersion W.2.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec W.2
def pt (W : X.affineOpens) {A : Type} [CommRing A] (p : Γ(X, W.1) →+* A) :
    Spec (CommRingCat.of A) ⟶ X :=
  Spec.map (CommRingCat.ofHom p) ≫ W.2.fromSpec
def res {W W' : X.affineOpens} (h : W.1 ≤ W'.1) : Γ(X, W'.1) →+* Γ(X, W.1) :=
  (X.presheaf.map (homOfLE h).op).hom
variable {A : ι → Type} [∀ i, CommRing (A i)]
end Scheme
end GlobalTheory.CompanionTheory.Ultra


