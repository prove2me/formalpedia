-- Prove2me | solution 1 for AlgebraicCurve.exists_principal_support_subset_chartDomains_of_multidegree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6aedb643-204b-5df6-a54f-2a461cbe292b

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_principal_support_subset_chartDomains_of_multidegree_eq_zero

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace P2mMoveToCharts

section PartA

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem pow_exp_unique (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (u u' : Aˣ) (a b : ℕ)
    (h : (u : A) * π ^ a = u' * π ^ b) : a = b := by

  have key : ∀ (u u' : Aˣ) (a b : ℕ), a ≤ b → (u : A) * π ^ a = u' * π ^ b → a = b := by
    intro u u' a b hab h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rcases Nat.eq_zero_or_pos k with hk | hk
    · omega
    · exfalso
      have hπa : (π : A) ^ a ≠ 0 := pow_ne_zero _ hπ0
      have h2 : (u : A) = u' * π ^ k := by
        have : (u : A) * π ^ a = (u' * π ^ k) * π ^ a := by rw [h]; ring
        exact mul_right_cancel₀ hπa this
      have hunit : IsUnit ((π : A) ^ k) := by
        have : (π : A) ^ k = (u'⁻¹ : Aˣ) * u := by
          rw [h2, ← mul_assoc, Units.inv_mul, one_mul]
        rw [this]
        exact (Units.isUnit _).mul (Units.isUnit _)
      rw [isUnit_pow_iff (by omega)] at hunit
      exact (IsLocalRing.mem_maximalIdeal _).mp hπ hunit
  rcases le_total a b with hab | hab
  · exact key u u' a b hab h
  · exact (key u' u b a hab h.symm).symm

end PartA

section PartB

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

theorem deg_eq_one_of_isRational {K : Type*} [Field K] {Fb : Type*} [Field Fb] [Algebra K Fb]
    (Q : Place K Fb) (hQ : Q.IsRational) : Q.deg = 1 := by
  unfold Place.deg
  have hb : Function.Bijective (Algebra.linearMap K Q.ResidueField) :=
    ⟨(algebraMap K Q.ResidueField).injective, hQ⟩
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]

theorem depth_bounds (π : A) (hπ0 : π ≠ 0) (An : Annulus A F) {W : ℕ} {u₀ : Aˣ}
    (hW : An.modulus = u₀ * π ^ W) {P : Place L F} (hP : P ∈ An.dom) {d : ℕ} {u : Aˣ}
    {hm : P.evalAt An.param ∈ A} (h : (⟨P.evalAt An.param, hm⟩ : A) = u * π ^ d) :
    0 < d ∧ d < W := by
  obtain ⟨-, -, ⟨hm', hmax⟩, -, ⟨mm, hmm, hmod⟩⟩ := An.mem_dom P hP
  have hsame : (⟨P.evalAt An.param, hm'⟩ : A) = ⟨P.evalAt An.param, hm⟩ := rfl
  constructor
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · exfalso
      subst hd
      rw [hsame, h, pow_zero, mul_one] at hmax
      exact (IsLocalRing.mem_maximalIdeal _).mp hmax (Units.isUnit u)
    · exact hd
  · by_contra hdW
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hdW)

    have hA : (u₀ : A) * π ^ W = u * π ^ (W + k) * mm := by
      apply Subtype.ext
      have h1 : ((An.modulus : A) : L) = P.evalAt An.param * (mm : L) := hmod
      rw [hW] at h1
      have h2 : (P.evalAt An.param) = ((u * π ^ (W + k) : A) : L) := by
        rw [← h]
      rw [h2] at h1
      push_cast at h1 ⊢
      exact h1
    have hπW : (π : A) ^ W ≠ 0 := pow_ne_zero _ hπ0
    have h3 : (u₀ : A) = u * π ^ k * mm := by
      have : (u₀ : A) * π ^ W = (u * π ^ k * mm) * π ^ W := by rw [hA]; ring
      exact mul_right_cancel₀ hπW this
    have hmem : (u₀ : A) ∈ maximalIdeal A := by
      rw [h3]
      exact Ideal.mul_mem_left _ _ hmm
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (Units.isUnit u₀)

end PartB

section PartC

abbrev Vtx (n m : ℕ) (w : Fin m → ℕ) : Type := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))

theorem depth_index_lt {d W : ℕ} (hd0 : 0 < d) (hdw : d < W) : d - 1 < W - 1 := by omega

end PartC

section PartD

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {n m : ℕ}
variable {Fbar : Fin n → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]

open scoped Classical in

noncomputable def dep (π : A) (An : Fin m → Annulus A F) (e : Fin m) (P : Place L F) : ℕ :=
  if hd : ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d
  then hd.choose else 0

theorem dep_spec (π : A) (An : Fin m → Annulus A F) (e : Fin m) (P : Place L F)
    (hd : ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) :
    ∃ (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ dep π An e P := by
  classical
  unfold dep
  rw [dif_pos hd]
  exact hd.choose_spec

theorem dep_of_not (π : A) (An : Fin m → Annulus A F) (e : Fin m) (P : Place L F)
    (hd : ¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) :
    dep π An e P = 0 := by
  classical
  unfold dep
  rw [dif_neg hd]

theorem dep_eq (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (An : Fin m → Annulus A F)
    (e : Fin m) (P : Place L F) {d : ℕ} {u : Aˣ} {h : P.evalAt (An e).param ∈ A}
    (heq : (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) : dep π An e P = d := by
  obtain ⟨u', h', heq'⟩ := dep_spec π An e P ⟨d, u, h, heq⟩
  have : (⟨P.evalAt (An e).param, h'⟩ : A) = ⟨P.evalAt (An e).param, h⟩ := rfl
  rw [this, heq] at heq'
  exact (pow_exp_unique π hπ hπ0 u u' d _ heq').symm

def Covers (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F) : Prop :=
  ∀ P : Place L F,
    (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
    (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)

theorem Covers.of_chart {C : ∀ i, ComponentChart A F (Fbar i)} {An : Fin m → Annulus A F}
    (hc : Covers C An) {P : Place L F} {i : Fin n} (hi : P ∈ (C i).dom) :
    (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom := by
  rcases hc P with ⟨i₀, hi₀, hu, hno⟩ | ⟨e, _, _, hno⟩
  · have := hu i hi
    subst this
    exact ⟨hu, hno⟩
  · exact absurd hi (hno i)

theorem Covers.of_ann {C : ∀ i, ComponentChart A F (Fbar i)} {An : Fin m → Annulus A F}
    (hc : Covers C An) {P : Place L F} {e : Fin m} (he : P ∈ (An e).dom) :
    (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom := by
  rcases hc P with ⟨i, _, _, hno⟩ | ⟨e₀, he₀, hu, hno⟩
  · exact absurd he (hno e)
  · have := hu e he
    subst this
    exact ⟨hu, hno⟩

open scoped Classical in

noncomputable def phi0 (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) (P : Place L F) : Vtx n m w → ℤ :=
  if h : ∃ i, P ∈ (C i).dom then Pi.single (Sum.inl h.choose) 1
  else if h2 : ∃ e, P ∈ (An e).dom then
    (if hb : 0 < dep π An h2.choose P ∧ dep π An h2.choose P < w h2.choose then
      Pi.single (Sum.inr ⟨h2.choose, ⟨dep π An h2.choose P - 1, by omega⟩⟩) 1
     else 0)
  else 0

theorem phi0_chart (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) (hc : Covers C An) {P : Place L F} {i : Fin n} (hi : P ∈ (C i).dom) :
    phi0 π C An w P = Pi.single (Sum.inl i) 1 := by
  obtain ⟨hu, -⟩ := hc.of_chart hi
  have h : ∃ i, P ∈ (C i).dom := ⟨i, hi⟩
  classical
  unfold phi0
  rw [dif_pos h, hu _ h.choose_spec]

theorem phi0_ann (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) (hc : Covers C An) {P : Place L F} {e : Fin m} (he : P ∈ (An e).dom)
    (hb : 0 < dep π An e P ∧ dep π An e P < w e) :
    phi0 π C An w P = Pi.single (Sum.inr ⟨e, ⟨dep π An e P - 1, by omega⟩⟩) 1 := by
  obtain ⟨hu, hno⟩ := hc.of_ann he
  have h1 : ¬ ∃ i, P ∈ (C i).dom := fun ⟨i, hi⟩ => hno i hi
  have h2 : ∃ e, P ∈ (An e).dom := ⟨e, he⟩
  have he2 : h2.choose = e := hu _ h2.choose_spec
  have key : ∀ e₀ : Fin m, e₀ = e →
      (if hb : 0 < dep π An e₀ P ∧ dep π An e₀ P < w e₀ then
        (Pi.single (Sum.inr ⟨e₀, ⟨dep π An e₀ P - 1, by omega⟩⟩) 1 : Vtx n m w → ℤ)
       else 0) = Pi.single (Sum.inr ⟨e, ⟨dep π An e P - 1, by omega⟩⟩) 1 := by
    rintro _ rfl
    rw [dif_pos hb]
  classical
  unfold phi0
  rw [dif_neg h1, dif_pos h2]
  exact key _ he2

theorem phi0_ann_none (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) (hc : Covers C An) {P : Place L F} {e : Fin m} (he : P ∈ (An e).dom)
    (hnone : ¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) :
    phi0 π C An w P = 0 := by
  obtain ⟨hu, hno⟩ := hc.of_ann he
  have h1 : ¬ ∃ i, P ∈ (C i).dom := fun ⟨i, hi⟩ => hno i hi
  have h2 : ∃ e, P ∈ (An e).dom := ⟨e, he⟩
  have he2 : h2.choose = e := hu _ h2.choose_spec
  have hd0 : dep π An e P = 0 := dep_of_not π An e P hnone
  have key : ∀ e₀ : Fin m, e₀ = e →
      (if hb : 0 < dep π An e₀ P ∧ dep π An e₀ P < w e₀ then
        (Pi.single (Sum.inr ⟨e₀, ⟨dep π An e₀ P - 1, by omega⟩⟩) 1 : Vtx n m w → ℤ)
       else 0) = 0 := by
    rintro _ rfl
    rw [dif_neg]
    rw [hd0]
    omega
  classical
  unfold phi0
  rw [dif_neg h1, dif_pos h2]
  exact key _ he2

theorem single_inr_congr (w : Fin m → ℕ) (e : Fin m) {x y : ℕ} (hx : x < w e - 1) (hy : y < w e - 1)
    (h : x = y) :
    (Pi.single (Sum.inr ⟨e, ⟨x, hx⟩⟩) 1 : Vtx n m w → ℤ) = Pi.single (Sum.inr ⟨e, ⟨y, hy⟩⟩) 1 := by
  subst h
  rfl

noncomputable def psi (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) : Divisor L F →+ (Vtx n m w → ℤ) :=
  Finsupp.liftAddHom fun P => zmultiplesHom _ (phi0 π C An w P)

theorem psi_single (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) (P : Place L F) :
    psi π C An w (Finsupp.single P 1) = phi0 π C An w P := by
  simp [psi]

theorem psi_apply (π : A) (C : ∀ i, ComponentChart A F (Fbar i)) (An : Fin m → Annulus A F)
    (w : Fin m → ℕ) (D : Divisor L F) :
    psi π C An w D = D.sum fun P k => k • phi0 π C An w P := by
  unfold psi
  rw [Finsupp.liftAddHom_apply]
  rfl

theorem psi_apply_inr_of_charts (π : A) (C : ∀ i, ComponentChart A F (Fbar i))
    (An : Fin m → Annulus A F) (w : Fin m → ℕ) (hc : Covers C An) (G : Divisor L F)
    (hG : ∀ P ∈ G.support, ∃ i, P ∈ (C i).dom) (v : Σ e : Fin m, Fin (w e - 1)) :
    psi π C An w G (Sum.inr v) = 0 := by
  rw [psi_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  obtain ⟨i, hi⟩ := hG P hP
  rw [Pi.smul_apply, phi0_chart π C An w hc hi, Pi.single_apply, if_neg Sum.inr_ne_inl, smul_zero]

theorem psi_of_support_subset (π : A) (C : ∀ i, ComponentChart A F (Fbar i))
    (An : Fin m → Annulus A F) (w : Fin m → ℕ) (hc : Covers C An) {i : Fin n} (G : Divisor L F)
    (hG : ∀ P ∈ G.support, P ∈ (C i).dom) (hrat : ∀ P ∈ (C i).dom, P.IsRational) :
    psi π C An w G = Divisor.degree G • (Pi.single (Sum.inl i) 1 : Vtx n m w → ℤ) := by
  have hdeg : Divisor.degree G = ∑ P ∈ G.support, G P := by
    have : Divisor.degree G = G.sum fun Q k => k * (Q.deg : ℤ) := by
      unfold Divisor.degree
      rw [Finsupp.liftAddHom_apply]
      rfl
    rw [this, Finsupp.sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [deg_eq_one_of_isRational P (hrat P (hG P hP)), Nat.cast_one, mul_one]
  rw [psi_apply, Finsupp.sum, hdeg, Finset.sum_smul]
  exact Finset.sum_congr rfl fun P hP => by rw [phi0_chart π C An w hc (hG P hP)]

theorem exists_fun_of_mem_closure_range {V : Type*} [Fintype V] {M : Type*} [AddCommGroup M]
    (lap : V → M) {x : M} (hx : x ∈ AddSubgroup.closure (Set.range lap)) :
    ∃ c : V → ℤ, x = ∑ u, c u • lap u := by
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

end PartD

section Main

theorem main
    {L : Type*} [Field L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An : Fin m → Annulus A F) (w : Fin m → ℕ)
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hcover : Covers C An)
    (D : Divisor L F)
    (hDlat : ∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    (lap : Vtx n m w → (Vtx n m w → ℤ))
    (φ : Divisor L F →+ (Vtx n m w → ℤ) ⧸ AddSubgroup.closure (Set.range lap))
    (hφ1 : ∀ i, ∀ P ∈ (C i).dom,
        φ (Finsupp.single P 1) = QuotientAddGroup.mk (Pi.single (Sum.inl i) 1 : Vtx n m w → ℤ))
    (hφ2 : ∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          φ (Finsupp.single P 1) =
            QuotientAddGroup.mk
              (Pi.single (Sum.inr ⟨e, ⟨d - 1, depth_index_lt hd0 hdw⟩⟩) 1 : Vtx n m w → ℤ))
    (hφ3 : ∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → φ (Finsupp.single P 1) = 0)
    (hlift : ∀ μ : Divisor L F →+ (Vtx n m w → ℤ),
        (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
        (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
            μ (Finsupp.single P 1) =
              Pi.single (Sum.inr ⟨e, ⟨d - 1, depth_index_lt hd0 hdw⟩⟩) 1) →
        (∀ e, ∀ P ∈ (An e).dom,
          (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → μ (Finsupp.single P 1) = 0) →
        ∀ (c : Vtx n m w → ℤ) (Dan : Divisor L F),
          (∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧
            ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
              (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
          (∀ v : Σ e : Fin m, Fin (w e - 1), μ Dan (Sum.inr v) = (∑ u, c u • lap u) (Sum.inr v)) →
          ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
            (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧
              ∀ i, μ Df (Sum.inl i) = (∑ u, c u • lap u) (Sum.inl i))
    (hφD : φ D = 0) :
    ∃ (f : F) (E : Divisor L F), f ≠ 0 ∧ (∀ P, E P = P.ord f) ∧
      (∀ P ∈ E.support, (∃ i, P ∈ (C i).dom) ∨
        ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) ∧
      ∃ Di : Fin n → Divisor L F, D - E = ∑ i, Di i ∧
        (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by
  classical

  have hμ1 : ∀ i, ∀ P ∈ (C i).dom, psi π C An w (Finsupp.single P 1) = Pi.single (Sum.inl i) 1 := by
    intro i P hP
    rw [psi_single, phi0_chart π C An w hcover hP]
  have hμ2 : ∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
        psi π C An w (Finsupp.single P 1) =
          Pi.single (Sum.inr ⟨e, ⟨d - 1, depth_index_lt hd0 hdw⟩⟩) 1 := by
    intro e P hP d u h heq hd0 hdw
    have hdep : dep π An e P = d := dep_eq π hπ hπ0 An e P heq
    have hb : 0 < dep π An e P ∧ dep π An e P < w e := by rw [hdep]; exact ⟨hd0, hdw⟩
    rw [psi_single, phi0_ann π C An w hcover hP hb,
      single_inr_congr w e _ _ (by rw [hdep] : dep π An e P - 1 = d - 1)]
  have hμ3 : ∀ e, ∀ P ∈ (An e).dom,
      (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → psi π C An w (Finsupp.single P 1) = 0 := by
    intro e P hP hnone
    rw [psi_single, phi0_ann_none π C An w hcover hP hnone]

  have hfac : φ = (QuotientAddGroup.mk' (AddSubgroup.closure (Set.range lap))).comp (psi π C An w) := by
    apply Finsupp.addHom_ext'
    intro P
    apply AddMonoidHom.ext_int
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, QuotientAddGroup.mk'_apply]
    rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, he, -, -⟩
    · rw [hφ1 i P hi, hμ1 i P hi]
    · by_cases hlat : ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d
      · obtain ⟨d, u, h, heq⟩ := hlat
        obtain ⟨u₀, hu₀⟩ := hw e
        obtain ⟨hd0, hdw⟩ := depth_bounds π hπ0 (An e) hu₀ he heq
        rw [hφ2 e P he d u h heq hd0 hdw, hμ2 e P he d u h heq hd0 hdw]
      · rw [hφ3 e P he hlat, hμ3 e P he hlat, QuotientAddGroup.mk_zero]

  have hmem : psi π C An w D ∈ AddSubgroup.closure (Set.range lap) := by
    have h1 : ((QuotientAddGroup.mk' (AddSubgroup.closure (Set.range lap))).comp (psi π C An w)) D
        = 0 := by
      rw [← hfac]; exact hφD
    rwa [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h1
  obtain ⟨c, hc⟩ := exists_fun_of_mem_closure_range lap hmem

  obtain ⟨Dan, hDan_pos, hDan_neg⟩ : ∃ Dan : Divisor L F,
      (∀ P, (¬ ∃ i, P ∈ (C i).dom) → Dan P = D P) ∧ (∀ P, (∃ i, P ∈ (C i).dom) → Dan P = 0) :=
    ⟨D.filter (fun P => ¬ ∃ i, P ∈ (C i).dom),
      fun P hP => Finsupp.filter_apply_pos (fun P => ¬ ∃ i, P ∈ (C i).dom) D hP,
      fun P hP => Finsupp.filter_apply_neg (fun P => ¬ ∃ i, P ∈ (C i).dom) D (not_not.mpr hP)⟩
  obtain ⟨Dch, hDch_pos, hDch_neg⟩ : ∃ Dch : Divisor L F,
      (∀ P, (∃ i, P ∈ (C i).dom) → Dch P = D P) ∧ (∀ P, (¬ ∃ i, P ∈ (C i).dom) → Dch P = 0) :=
    ⟨D.filter (fun P => ∃ i, P ∈ (C i).dom),
      fun P hP => Finsupp.filter_apply_pos (fun P => ∃ i, P ∈ (C i).dom) D hP,
      fun P hP => Finsupp.filter_apply_neg (fun P => ∃ i, P ∈ (C i).dom) D hP⟩
  have hsplit : Dch + Dan = D := by
    ext P
    rw [Finsupp.add_apply]
    by_cases hP : ∃ i, P ∈ (C i).dom
    · rw [hDch_pos P hP, hDan_neg P hP, add_zero]
    · rw [hDch_neg P hP, hDan_pos P hP, zero_add]
  have hDch_supp : ∀ P ∈ Dch.support, ∃ i, P ∈ (C i).dom := by
    intro P hP
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hP) (hDch_neg P hn)
  have hDan_supp : ∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧
      ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d := by
    intro P hP
    have hP' := Finsupp.mem_support_iff.mp hP
    have hn : ¬ ∃ i, P ∈ (C i).dom := fun h => hP' (hDan_neg P h)
    have hD : P ∈ D.support := by
      rw [Finsupp.mem_support_iff, ← hDan_pos P hn]
      exact hP'
    rcases hDlat P hD with h | h
    · exact absurd h hn
    · exact h

  have hint : ∀ v : Σ e : Fin m, Fin (w e - 1),
      psi π C An w Dan (Sum.inr v) = (∑ u, c u • lap u) (Sum.inr v) := by
    intro v
    rw [← hc, ← hsplit, map_add, Pi.add_apply,
      psi_apply_inr_of_charts π C An w hcover Dch hDch_supp v, zero_add]

  obtain ⟨f, Df, hf0, hDf, hDfan, hDfi⟩ := hlift (psi π C An w) hμ1 hμ2 hμ3 c Dan hDan_supp hint

  obtain ⟨Di, hDi_pos, hDi_neg⟩ : ∃ Di : Fin n → Divisor L F,
      (∀ i P, P ∈ (C i).dom → Di i P = (D - Df) P) ∧ (∀ i P, P ∉ (C i).dom → Di i P = 0) :=
    ⟨fun i => (D - Df).filter (· ∈ (C i).dom),
      fun i P hP => Finsupp.filter_apply_pos (· ∈ (C i).dom) (D - Df) hP,
      fun i P hP => Finsupp.filter_apply_neg (· ∈ (C i).dom) (D - Df) hP⟩
  have hDi_supp : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom := by
    intro i P hP
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hP) (hDi_neg i P hn)
  have hDsum : D - Df = ∑ j, Di j := by
    ext P
    rw [Finsupp.finsetSum_apply]
    rcases hcover P with ⟨i, hi, hu, -⟩ | ⟨e, he, -, hnoC⟩
    · rw [Finset.sum_eq_single i]
      · exact (hDi_pos i P hi).symm
      · intro j _ hji
        exact hDi_neg j P (fun h => hji (hu j h))
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [Finset.sum_eq_zero (fun j _ => hDi_neg j P (hnoC j))]
      rw [Finsupp.sub_apply, hDfan e P he, hDan_pos P (fun ⟨j, hj⟩ => hnoC j hj), sub_self]
  refine ⟨f, Df, hf0, hDf, ?_, Di, hDsum, hDi_supp, ?_⟩
  ·
    intro P hP
    rcases hcover P with ⟨i, hi, -, -⟩ | ⟨e, he, -, -⟩
    · exact Or.inl ⟨i, hi⟩
    · have hP' : Df P ≠ 0 := Finsupp.mem_support_iff.mp hP
      rw [hDfan e P he] at hP'
      exact Or.inr (hDan_supp P (Finsupp.mem_support_iff.mpr hP'))
  ·
    intro i
    have hsub0 : psi π C An w (D - Df) (Sum.inl i) = 0 := by
      rw [map_sub, Pi.sub_apply, hc, hDfi i, sub_self]
    have hread : psi π C An w (D - Df) (Sum.inl i) = Divisor.degree (Di i) := by
      rw [hDsum, map_sum, Finset.sum_apply, Finset.sum_eq_single i]
      · rw [psi_of_support_subset π C An w hcover (Di i) (hDi_supp i) (hratF i), Pi.smul_apply,
          Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hji
        rw [psi_of_support_subset π C An w hcover (Di j) (hDi_supp j) (hratF j), Pi.smul_apply,
          Pi.single_apply, if_neg (fun h => hji (Sum.inl_injective h).symm), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [← hread, hsub0]

end Main

end P2mMoveToCharts

open AlgebraicCurve IsLocalRing in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    [HasPrincipalDivisors L F] (D : Divisor L F) (hD : Divisor.degree D = 0)
    (hDlat : ∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d)
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))
    let ends : (Σ e : Fin m, Fin (w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ φ : Divisor L F →+ (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap),
      (∀ i, ∀ P ∈ (C i).dom,
        φ (Finsupp.single P 1) = QuotientAddGroup.mk (Pi.single (Sum.inl i) 1 : V → ℤ)) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          φ (Finsupp.single P 1) =
            QuotientAddGroup.mk (Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1 : V → ℤ)) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → φ (Finsupp.single P 1) = 0) →
      (∀ f : F, f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord f) →
        (∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
        φ D = 0) →
      (∀ μ : Divisor L F →+ (V → ℤ),
        (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
        (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
            μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
        (∀ e, ∀ P ∈ (An e).dom,
          (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → μ (Finsupp.single P 1) = 0) →
        ∀ (c : V → ℤ) (Dan : Divisor L F),
          (∀ P ∈ Dan.support, ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
          (∀ v : Σ e : Fin m, Fin (w e - 1), μ Dan (Sum.inr v) = (∑ u, c u • lap u) (Sum.inr v)) →
          ∃ (f : F) (Df : Divisor L F), f ≠ 0 ∧ (∀ P, Df P = P.ord f) ∧
            (∀ e, ∀ Q ∈ (An e).dom, Df Q = Dan Q) ∧ ∀ i, μ Df (Sum.inl i) = (∑ u, c u • lap u) (Sum.inl i)) →
      φ D = 0 →
      ∃ (f : F) (E : Divisor L F), f ≠ 0 ∧ (∀ P, E P = P.ord f) ∧
        (∀ P ∈ E.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) ∧
        ∃ Di : Fin n → Divisor L F, D - E = ∑ i, Di i ∧
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0 := by
  intro V ends lap φ hφ1 hφ2 hφ3 _hφ4 hlift hφD
  exact P2mMoveToCharts.main A π hπ hπ0 F n m Fbar C hratF An w hw hcover D hDlat lap φ hφ1 hφ2 hφ3
    hlift hφD

end S_AlgebraicCurve_exists_principal_support_subset_chartDomains_of_multidegree_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_exists_principal_support_subset_chartDomains_of_multidegree_eq_zero (solution)
