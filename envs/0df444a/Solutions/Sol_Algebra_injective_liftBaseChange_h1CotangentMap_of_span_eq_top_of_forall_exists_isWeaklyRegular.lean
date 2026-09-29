-- Prove2me | solution 1 for Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6883a558-4894-57c2-8465-982f9fc846c4

import Mathlib
import Theorems.Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct Pointwise
open RingTheory.Sequence

namespace P2mKcK1Loc

section Alt

variable {A : Type*} [CommRing A]

def IsAlt {n : ℕ} {M : Type*} [AddCommGroup M] (d : Fin n → Fin n → M) : Prop :=
  (∀ j, d j j = 0) ∧ ∀ j l, d j l = - d l j

theorem sum_sum_smul_eq_zero_of_isAlt {n : ℕ} {M : Type*} [AddCommGroup M] [Module A M]
    (a : Fin n → A) (d : Fin n → Fin n → M) (hd : IsAlt d) :
    ∑ j, ∑ l, (a j * a l) • d j l = 0 := by
  classical
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun j l => (a j * a l) • d j l)]
  refine Finset.sum_ninvolution (fun p => p.swap) ?_ ?_ (fun p => Finset.mem_product.mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _⟩) (fun p => Prod.swap_swap p)
  · rintro ⟨j, l⟩
    simp only [Prod.swap_prod_mk]
    rw [hd.2 l j, mul_comm (a l) (a j), smul_neg, add_neg_cancel]
  · rintro ⟨j, l⟩ hne heq
    apply hne
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp only [hd.1, smul_zero]

theorem exists_isAlt_lift {n : ℕ} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (π : M →+ N) (hπ : Function.Surjective π) (d : Fin n → Fin n → N) (hd : IsAlt d) :
    ∃ D : Fin n → Fin n → M, IsAlt D ∧ ∀ j l, π (D j l) = d j l := by
  classical
  choose L hL using hπ
  refine ⟨fun j l => if j < l then L (d j l) else if l < j then - L (d l j) else 0, ⟨?_, ?_⟩, ?_⟩
  · intro j; simp
  · intro j l
    rcases lt_trichotomy j l with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp
    · simp [h, not_lt.mpr h.le]
  · intro j l
    rcases lt_trichotomy j l with h | rfl | h
    · simp [h, hL]
    · simp [hd.1 j]
    · simp [h, not_lt.mpr h.le, hL, ← hd.2 j l]

theorem exists_eq_smul_of_mem_smul_top {M : Type*} [AddCommGroup M] [Module A M]
    (r : A) {x : M} (hx : x ∈ r • (⊤ : Submodule A M)) : ∃ u : M, x = r • u := by
  obtain ⟨u, -, hu⟩ := (Submodule.mem_smul_pointwise_iff_exists x r ⊤).mp hx
  exact ⟨u, hu.symm⟩

theorem exists_isAlt_of_sum_smul_eq_zero (n : ℕ) :
    ∀ {M : Type*} [AddCommGroup M] [Module A M] (r : Fin n → A)
      (_ : IsWeaklyRegular M (List.ofFn r)) (m : Fin n → M)
      (_ : ∑ j, r j • m j = 0),
      ∃ d : Fin n → Fin n → M, IsAlt d ∧ ∀ j, m j = ∑ l, r l • d j l := by
  induction n with
  | zero =>
    intro M _ _ r _ m _
    exact ⟨fun _ _ => 0, ⟨fun j => rfl, fun j l => by simp⟩, fun j => Fin.elim0 j⟩
  | succ n ih =>
    intro M _ _ r hr m hm
    rw [List.ofFn_succ, isWeaklyRegular_cons_iff] at hr
    obtain ⟨hreg, hrest⟩ := hr

    let π : M →ₗ[A] QuotSMulTop (r 0) M := Submodule.mkQ _
    have hπ0 : ∀ x : M, π (r 0 • x) = 0 := fun x => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_pointwise_smul x (r 0) ⊤ Submodule.mem_top
    have hm' : ∑ j : Fin n, r j.succ • π (m j.succ) = 0 := by
      have h1 : π (∑ j : Fin (n + 1), r j • m j) = 0 := by rw [hm, map_zero]
      rw [Fin.sum_univ_succ, map_add, hπ0, zero_add, map_sum] at h1
      simpa only [map_smul] using h1
    obtain ⟨d', hd', hmd'⟩ := ih (fun j => r j.succ) hrest (fun j => π (m j.succ)) hm'

    obtain ⟨d, hd, hdd⟩ := exists_isAlt_lift π.toAddMonoidHom (Submodule.mkQ_surjective _) d' hd'

    have hdef : ∀ j : Fin n, ∃ u : M, m j.succ - ∑ l, r l.succ • d j l = r 0 • u := by
      intro j
      apply exists_eq_smul_of_mem_smul_top
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      change π (m j.succ) - ∑ l, π (r l.succ • d j l) = 0
      simp only [map_smul]
      change π (m j.succ) - ∑ l, r l.succ • π.toAddMonoidHom (d j l) = 0
      simp only [hdd, ← hmd' j, sub_self]
    choose u hu using hdef

    have hm0 : m 0 = - ∑ j, r j.succ • u j := by
      have h1 : r 0 • (m 0 + ∑ j, r j.succ • u j) = 0 := by
        rw [Fin.sum_univ_succ] at hm
        have h2 : ∀ j : Fin n, m j.succ = ∑ l, r l.succ • d j l + r 0 • u j := fun j => by
          rw [← hu j, add_sub_cancel]
        simp only [h2, smul_add, Finset.sum_add_distrib, Finset.smul_sum, ← mul_smul] at hm
        rw [sum_sum_smul_eq_zero_of_isAlt (fun j => r j.succ) d hd, zero_add] at hm
        rw [smul_add, Finset.smul_sum]
        simpa only [← mul_smul, mul_comm (r 0)] using hm
      have h2 : r 0 • (m 0 + ∑ j, r j.succ • u j) = r 0 • 0 := by rw [h1, smul_zero]
      have h3 := hreg h2
      exact eq_neg_of_add_eq_zero_left h3

    refine ⟨fun j l => Fin.cases (Fin.cases 0 (fun l' => - u l') l)
      (fun j' => Fin.cases (u j') (fun l' => d j' l') l) j, ⟨?_, ?_⟩, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp
      · simp [hd.1 j']
    · intro j l
      refine Fin.cases ?_ (fun j' => ?_) j <;> refine Fin.cases ?_ (fun l' => ?_) l
      · simp
      · simp
      · simp
      · simp [hd.2 j' l']
    · intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · rw [Fin.sum_univ_succ]
        simp [hm0, Finset.sum_neg_distrib]
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cases_succ, Fin.cases_zero]
        rw [← hu j']
        abel

end Alt

section SyzLoc

variable {B : Type*} [CommRing B]

def HasKoszulSyzygies {n : ℕ} (r : Fin n → B) : Prop :=
  ∀ m : Fin n → B, ∑ j, r j * m j = 0 →
    ∃ d : Fin n → Fin n → B, IsAlt d ∧ ∀ j, m j = ∑ l, r l * d j l

def goodIdeal {n : ℕ} (r c : Fin n → B) : Ideal B where
  carrier := {u | ∃ d : Fin n → Fin n → B, IsAlt d ∧ ∀ j, u * c j = ∑ l, r l * d j l}
  zero_mem' := ⟨fun _ _ => 0, ⟨fun _ => rfl, fun _ _ => by simp⟩, fun j => by simp⟩
  add_mem' := by
    rintro u u' ⟨d, hd, hu⟩ ⟨d', hd', hu'⟩
    refine ⟨fun j l => d j l + d' j l, ⟨fun j => by simp [hd.1, hd'.1], fun j l => ?_⟩, fun j => ?_⟩
    · dsimp only; rw [hd.2 j l, hd'.2 j l]; abel
    · simp only [add_mul, hu, hu', mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    rintro a u ⟨d, hd, hu⟩
    refine ⟨fun j l => a * d j l, ⟨fun j => by simp [hd.1], fun j l => ?_⟩, fun j => ?_⟩
    · dsimp only; rw [hd.2 j l]; ring
    · simp only [smul_eq_mul, mul_assoc, hu, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring

lemma mem_goodIdeal_iff {n : ℕ} (r c : Fin n → B) (u : B) :
    u ∈ goodIdeal r c ↔ ∃ d : Fin n → Fin n → B, IsAlt d ∧ ∀ j, u * c j = ∑ l, r l * d j l :=
  Iff.rfl

lemma self_mem_goodIdeal {n : ℕ} (r c : Fin n → B) (hc : ∑ j, r j * c j = 0) (l : Fin n) :
    r l ∈ goodIdeal r c := by
  classical
  refine ⟨fun j i => (if i = l then c j else 0) - (if j = l then c i else 0), ⟨fun j => ?_,
    fun j i => ?_⟩, fun j => ?_⟩
  · exact sub_self _
  · ring
  · simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    split_ifs with h
    · rw [hc, sub_zero, mul_comm]
    · rw [Finset.sum_const_zero, sub_zero, mul_comm]

lemma exists_isAlt_integer {n : ℕ} (M : Submonoid B) (L : Type*) [CommRing L] [Algebra B L]
    [IsLocalization M L] (D : Fin n → Fin n → L) (hD : IsAlt D) :
    ∃ (b : M) (d : Fin n → Fin n → B), IsAlt d ∧
      ∀ j l, algebraMap B L (d j l) = (b : B) • D j l := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M (fun p : Fin n × Fin n => D p.1 p.2)
  choose e he using hb
  refine ⟨b, fun j l => if j < l then e (j, l) else if l < j then - e (l, j) else 0, ⟨?_, ?_⟩, ?_⟩
  · intro j; simp
  · intro j l
    rcases lt_trichotomy j l with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp
    · simp [h, not_lt.mpr h.le]
  · intro j l
    rcases lt_trichotomy j l with h | rfl | h
    · simp [h, he]
    · simp [hD.1 j]
    · simp only [h, not_lt.mpr h.le, if_false, if_true, map_neg, he]
      rw [hD.2 j l, smul_neg]

theorem hasKoszulSyzygies_of_forall_isWeaklyRegular {n : ℕ} (r : Fin n → B)
    (H : ∀ (m : Ideal B) [m.IsMaximal], Ideal.span (Set.range r) ≤ m →
      IsWeaklyRegular (Localization.AtPrime m)
        (List.ofFn fun j => algebraMap B (Localization.AtPrime m) (r j))) :
    HasKoszulSyzygies r := by
  classical
  intro c hc
  suffices htop : goodIdeal r c = ⊤ by
    have h1 : (1 : B) ∈ goodIdeal r c := by rw [htop]; exact Submodule.mem_top
    obtain ⟨d, hd, hd'⟩ := h1
    exact ⟨d, hd, fun j => by simpa using hd' j⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  by_cases hrm : Ideal.span (Set.range r) ≤ m
  ·
    set L := Localization.AtPrime m
    have hreg := H m hrm
    have hrel : ∑ j, algebraMap B L (r j) • algebraMap B L (c j) = 0 := by
      simp only [smul_eq_mul, ← map_mul, ← map_sum, hc, map_zero]
    obtain ⟨D, hD, hcD⟩ := exists_isAlt_of_sum_smul_eq_zero n (fun j => algebraMap B L (r j)) hreg
      (fun j => algebraMap B L (c j)) hrel
    obtain ⟨b, d, hd, hdD⟩ := exists_isAlt_integer m.primeCompl L D hD

    have heq : ∀ j, ∃ t : m.primeCompl, (t : B) * ((b : B) * c j) = (t : B) * ∑ l, r l * d j l := by
      intro j
      apply (IsLocalization.eq_iff_exists m.primeCompl L).mp
      rw [map_mul, map_sum, ← Algebra.smul_def, hcD j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hdD]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    choose t ht using heq
    set τ : B := ∏ j, (t j : B) with hτ
    have hτm : τ ∈ m.primeCompl := by
      rw [hτ]
      exact prod_mem fun j _ => (t j).2
    have hgood : τ * (b : B) ∈ goodIdeal r c := by
      refine ⟨fun j l => τ * d j l,
        ⟨fun j => by simp [hd.1], fun j l => by dsimp only; rw [hd.2 j l]; ring⟩, fun j => ?_⟩
      have hsplit : τ = (∏ i ∈ Finset.univ.erase j, (t i : B)) * (t j : B) :=
        (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
      calc τ * (b : B) * c j = (∏ i ∈ Finset.univ.erase j, (t i : B)) * ((t j : B) * ((b : B) * c j)) := by
              rw [hsplit]; ring
        _ = (∏ i ∈ Finset.univ.erase j, (t i : B)) * ((t j : B) * ∑ l, r l * d j l) := by rw [ht j]
        _ = ∑ l, r l * (τ * d j l) := by
              rw [hsplit, Finset.mul_sum, Finset.mul_sum]
              exact Finset.sum_congr rfl fun l _ => by ring
    have : τ * (b : B) ∈ m := hle hgood
    rcases hm.isPrime.mem_or_mem this with h | h
    · exact hτm h
    · exact b.2 h
  ·
    apply hrm
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact hle (self_mem_goodIdeal r c hc l)

theorem hasKoszulSyzygies_get_of_forall_isWeaklyRegular (f : List B)
    (H : ∀ (m : Ideal B) [m.IsMaximal], Ideal.ofList f ≤ m →
      IsWeaklyRegular (Localization.AtPrime m)
        (f.map (algebraMap B (Localization.AtPrime m)))) :
    HasKoszulSyzygies f.get := by
  have hspan : Ideal.span (Set.range f.get) = Ideal.ofList f := by
    rw [Ideal.ofList]
    congr 1
    ext b
    simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_iff_get]
  have hmap : ∀ (L : Type _) [CommRing L] [Algebra B L],
      f.map (algebraMap B L) = List.ofFn fun j => algebraMap B L (f.get j) := by
    intro L _ _
    exact List.ext_getElem (by simp) fun i h1 h2 => by simp
  refine hasKoszulSyzygies_of_forall_isWeaklyRegular f.get fun m _ hm => ?_
  have := H m (hspan ▸ hm)
  rwa [hmap] at this

end SyzLoc

section Functorial

p2m_open "Algebra TensorProduct.Algebra TensorProduct Algebra.TensorProduct"

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {T' : Type*} [CommRing T'] [Algebra R T'] [Algebra S T'] [Algebra T T']
    [IsScalarTower R S T'] [IsScalarTower R T T'] [IsScalarTower S T T']

lemma map_map (h : Algebra.H1Cotangent R S) :
    Algebra.H1Cotangent.map R R T T' (Algebra.H1Cotangent.map R R S T h) =
      Algebra.H1Cotangent.map R R S T' h := by
  rw [Algebra.H1Cotangent.map, Algebra.H1Cotangent.map, Algebra.H1Cotangent.map,
    ← (Extension.H1Cotangent.map
      (Generators.defaultHom (Generators.self R T) (Generators.self R T')).toExtensionHom
        ).coe_restrictScalars S,
    ← LinearMap.comp_apply, ← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq]

variable (R S T T') in

noncomputable def phi (M : Type*) [AddCommGroup M] [Module S M] :
    T ⊗[S] M →ₗ[T] T' ⊗[S] M :=
  AlgebraTensorModule.map (Algebra.linearMap T T') LinearMap.id

lemma phi_tmul {M : Type*} [AddCommGroup M] [Module S M] (t : T) (m : M) :
    phi S T T' M (t ⊗ₜ m) = algebraMap T T' t ⊗ₜ m := rfl

lemma square (x : T ⊗[S] Algebra.H1Cotangent R S) :
    Algebra.H1Cotangent.map R R T T' ((Algebra.H1Cotangent.map R R S T).liftBaseChange T x) =
      (Algebra.H1Cotangent.map R R S T').liftBaseChange T'
        (phi S T T' (Algebra.H1Cotangent R S) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t h =>
    rw [LinearMap.liftBaseChange_tmul, map_smul, map_map, phi_tmul,
      LinearMap.liftBaseChange_tmul, algebraMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma isBaseChange_phi (M : Type*) [AddCommGroup M] [Module S M] :
    IsBaseChange T' (phi S T T' M) := by
  refine IsBaseChange.of_comp (S := T) (f := (TensorProduct.mk S T M 1))
    (TensorProduct.isBaseChange S M T) ?_
  have : ((phi S T T' M : T ⊗[S] M →ₗ[S] T' ⊗[S] M) ∘ₗ TensorProduct.mk S T M 1) =
      TensorProduct.mk S T' M 1 := by
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      LinearMap.coe_restrictScalars, phi_tmul, map_one]
  rw [this]
  exact TensorProduct.isBaseChange S M T'

end Functorial

section Main

p2m_open "Algebra TensorProduct.Algebra TensorProduct Algebra.TensorProduct"

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

scoped instance isLocalizedModule_phi (g : T) (M : Type*) [AddCommGroup M] [Module S M] :
    IsLocalizedModule (Submonoid.powers g) (phi S T (Localization.Away g) M) :=
  (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) (Localization.Away g) _).mpr
    (isBaseChange_phi M)

theorem chart {T' : Type w} [CommRing T'] [Algebra R T'] [Algebra S T'] [IsScalarTower R S T']
    [Module.Flat S T'] {ι : Type w'} (x : ι → T') (f : List (MvPolynomial ι S))
    (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T'))
    (hf : RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T') = Ideal.ofList f)
    (hreg : ∀ (m : Ideal (MvPolynomial ι S)) [m.IsMaximal], Ideal.ofList f ≤ m →
        IsWeaklyRegular (Localization.AtPrime m)
          (f.map (algebraMap (MvPolynomial ι S) (Localization.AtPrime m)))) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T').liftBaseChange T') := by
  have hsyz := hasKoszulSyzygies_get_of_forall_isWeaklyRegular f hreg
  have hspan : Ideal.ofList f = Ideal.span (Set.range f.get) := by
    rw [Ideal.ofList]
    congr 1
    ext b
    simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_iff_get]
  refine Algebra.injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating
    x hx f.get (hf.trans hspan) fun c hc => ?_
  obtain ⟨d, hd, hcd⟩ := hsyz c (by simpa only [mul_comm] using hc)
  exact ⟨d, hd.1, hd.2, hcd⟩

theorem main [Module.Flat S T]
    (s : Set T) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, ∃ (ι : Type w') (x : ι → Localization.Away g) (f : List (MvPolynomial ι S)),
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) ∧
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) =
        Ideal.ofList f ∧
      ∀ (m : Ideal (MvPolynomial ι S)) [m.IsMaximal], Ideal.ofList f ≤ m →
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m)
          (f.map (algebraMap (MvPolynomial ι S) (Localization.AtPrime m)))) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine Module.eq_zero_of_isLocalized_span s hs
    (fun g : s => Localization.Away (g : T) ⊗[S] Algebra.H1Cotangent R S)
    (fun g : s => phi S T (Localization.Away (g : T)) (Algebra.H1Cotangent R S)) x ?_
  rintro ⟨g, hg⟩
  obtain ⟨ι, y, f, hy, hf, hreg⟩ := H g hg
  haveI : Module.Flat S (Localization.Away g) := Module.Flat.trans S T (Localization.Away g)
  have hinj := chart (R := R) (S := S) (T' := Localization.Away g) y f hy hf hreg
  rw [injective_iff_map_eq_zero] at hinj
  refine hinj _ ?_
  rw [← square, hx, map_zero]

end Main

end P2mKcK1Loc
p2m_reactivate "P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc"

theorem solution
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    (s : Set T) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, ∃ (ι : Type w') (x : ι → Localization.Away g) (f : List (MvPolynomial ι S)),
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) ∧
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) =
        Ideal.ofList f ∧
      ∀ (m : Ideal (MvPolynomial ι S)) [m.IsMaximal], Ideal.ofList f ≤ m →
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m)
          (f.map (algebraMap (MvPolynomial ι S) (Localization.AtPrime m)))) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) :=
  P2mKcK1Loc.main s hs H

end S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
end P2MW
export P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular (solution)
