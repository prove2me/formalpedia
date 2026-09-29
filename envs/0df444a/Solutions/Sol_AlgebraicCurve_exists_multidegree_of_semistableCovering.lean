-- Prove2me | solution 1 for AlgebraicCurve.exists_multidegree_of_semistableCovering
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/15f1b2e2-2e23-5cd9-991a-5cbc46bcc98e

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_multidegree_of_semistableCovering

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_multidegree_of_semistableCovering.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor RegularProlongation"
namespace Multidegree
p2m_open "AlgebraicCurve"

open IsLocalRing

private theorem depth_unique {L : Type*} [Field L] (A : ValuationSubring L) (π : A) (hπ : π ∈ maximalIdeal A)
    (hπ0 : π ≠ 0) (u u' : Aˣ) (a b : ℕ) (h : (u : A) * π ^ a = u' * π ^ b) : a = b := by

  wlog hab : a ≤ b generalizing a b u u'
  · exact (this u' u b a h.symm (not_le.mp hab).le).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  by_contra hne
  have hk : k ≠ 0 := by omega
  have hπa : (π : A) ^ a ≠ 0 := pow_ne_zero _ hπ0
  have h' : (u : A) = u' * π ^ k := by
    have : (u : A) * π ^ a = (u' * π ^ k) * π ^ a := by rw [h]; ring
    exact mul_right_cancel₀ hπa this
  have hmem : (u : A) ∈ maximalIdeal A := by
    rw [h']
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπ _ (Nat.pos_of_ne_zero hk))
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem u.isUnit

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

@[reducible] private noncomputable def chartRP {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

private theorem ord_smul_const (P : Place L F) {c : L} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    P.ord (c • f) = P.ord f := by
  have hcF : algebraMap L F c ≠ 0 := (map_ne_zero _).mpr hc
  have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩, ?_⟩
    apply Subtype.ext
    simp [hc]
  have h0 : P.ord (algebraMap L F c) = 0 := by
    have := P.ord_coe_unit hu.unit
    simpa using this
  rw [Algebra.smul_def, P.ord_mul hcF hf, h0, zero_add]

private theorem const_ne_zero_of_residue {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : C.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

private theorem annulus_wide [IsAlgClosed L] (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by

  have root_mem : ∀ (k : ℕ), 0 < k → ∀ r : L, r ^ k = (An.modulus : L) →
      ∃ hr : r ∈ A, (⟨r, hr⟩ : A) ∈ maximalIdeal A ∧ r ≠ 0 := by
    intro k hk r hrk
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hrk
      exact hmod0 hrk.symm
    have hrA : r ∈ A := by
      rcases A.mem_or_inv_mem r with h | h
      · exact h
      · exfalso
        have hinv : (An.modulus : L)⁻¹ ∈ A := by
          rw [← hrk, ← inv_pow]
          exact A.pow_mem h k
        have hunit : IsUnit An.modulus := by
          refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
          simp [hmod0]
        exact (mem_maximalIdeal _).mp An.modulus_mem hunit
    refine ⟨hrA, ?_, hr0⟩
    have hpow : (⟨r, hrA⟩ : A) ^ k = An.modulus := Subtype.ext (by simpa using hrk)
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance k (hpow ▸ An.modulus_mem)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (An.modulus : L) (by norm_num : 0 < 2)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (An.modulus : L) (by norm_num : 0 < 3)
  obtain ⟨hrA, hrm, hr0⟩ := root_mem 2 (by norm_num) r hr
  obtain ⟨hsA, hsm, hs0⟩ := root_mem 3 (by norm_num) s hs

  have hr_adm : ∃ m ∈ maximalIdeal A, (An.modulus : L) = r * m :=
    ⟨⟨r, hrA⟩, hrm, by rw [← hr]; ring⟩
  have hs_adm : ∃ m ∈ maximalIdeal A, (An.modulus : L) = s * m :=
    ⟨⟨s, hsA⟩ ^ 2, Ideal.pow_mem_of_mem _ hsm _ (by norm_num), by rw [← hs]; simp; ring⟩
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0 hr_adm
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := An.existsUnique_evalAt_eq ⟨s, hsA⟩ hsm hs0 hs_adm
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  simp only [hQ₁v, hQ₂v]
  intro hv

  have h6 : A.valuation (An.modulus : L) ^ 3 = A.valuation (An.modulus : L) ^ 2 := by
    conv_lhs => rw [← hr]
    conv_rhs => rw [← hs]
    rw [map_pow, map_pow, ← pow_mul, ← pow_mul, hv]
  have hv0 : A.valuation (An.modulus : L) ≠ 0 := by
    rwa [Ne, map_eq_zero]
  have hv1 : A.valuation (An.modulus : L) = 1 := by
    have : A.valuation (An.modulus : L) ^ 2 * A.valuation (An.modulus : L) =
        A.valuation (An.modulus : L) ^ 2 * 1 := by rw [mul_one, ← pow_succ, h6]
    exact mul_left_cancel₀ (pow_ne_zero _ hv0) this
  have hlt : A.valuation (An.modulus : L) < 1 := (A.valuation_lt_one_iff _).mp An.modulus_mem
  exact hlt.ne hv1

private theorem annulus_two_end [IsAlgClosed L]
    {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa] {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (An An' : Annulus A F) (Ca : ComponentChart A F Fa) (Cb : ComponentChart A F Fb)
    (xa : Place (ResidueField A) Fa) (xb : Place (ResidueField A) Fb)
    (hdom : An'.dom = An.dom) (hmod0 : (An.modulus : L) ≠ 0)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (ha : An.IsAttached Ca xa) (hb : An'.IsAttached Cb xb)
    (f : F) (hf0 : f ≠ 0) (ca cb : L) (hca : ca • f ∈ Ca.integers) (hresa : Ca.residue ⟨ca • f, hca⟩ ≠ 0)
    (hcb : cb • f ∈ Cb.integers) (hresb : Cb.residue ⟨cb • f, hcb⟩ ≠ 0)
    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord f) :
    (D.sum fun _ n => n) = xa.ord (Ca.residue ⟨ca • f, hca⟩) + xb.ord (Cb.residue ⟨cb • f, hcb⟩) ∧
    (D.prod fun P n => A.valuation (P.evalAt An.param) ^ n) =
      A.valuation (ca / cb) * A.valuation (An.modulus : L) ^ (xb.ord (Cb.residue ⟨cb • f, hcb⟩)) := by
  have hca0 : ca ≠ 0 := const_ne_zero_of_residue Ca hca hresa
  have hcb0 : cb ≠ 0 := const_ne_zero_of_residue Cb hcb hresb

  have hz0 : An.param ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hparam
    exact hmod0 ((map_eq_zero _).mp hparam.symm)
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ := by
    rw [← hparam, mul_inv_cancel_right₀ hz0]

  obtain ⟨-, hza, hxa, hslope_a⟩ := ha
  obtain ⟨-, hzb, hxb, hslope_b⟩ := hb
  revert hzb hxb hslope_b
  rw [hp', hdom]
  intro hzb hxb hslope_b

  have heq : (algebraMap L F (ca / cb))⁻¹ * (ca • f) = cb • f := by
    rw [Algebra.smul_def, Algebra.smul_def, map_div₀]
    have : algebraMap L F ca ≠ 0 := (map_ne_zero _).mpr hca0
    have : algebraMap L F cb ≠ 0 := (map_ne_zero _).mpr hcb0
    field_simp
  have hhb : (algebraMap L F (ca / cb))⁻¹ * (ca • f) ∈ Cb.integers := heq ▸ hcb
  have hsub : (⟨(algebraMap L F (ca / cb))⁻¹ * (ca • f), hhb⟩ : Cb.integers) = ⟨cb • f, hcb⟩ :=
    Subtype.ext heq
  have hresb' : Cb.residue ⟨(algebraMap L F (ca / cb))⁻¹ * (ca • f), hhb⟩ ≠ 0 := by
    rw [hsub]; exact hresb
  have hh0 : ca • f ≠ 0 := smul_ne_zero hca0 hf0
  have hD' : ∀ P ∈ An.dom, D P = P.ord (ca • f) := fun P hP => by
    rw [hD P hP, ord_smul_const P hca0 hf0]
  have two := An.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation hmod0
    (chartRP Ca) xa hza hxa hslope_a (chartRP Cb) xb hzb hxb hslope_b (annulus_wide An hmod0)
    (ca • f) hh0 hca hresa (ca / cb) (div_ne_zero hca0 hcb0) hhb hresb' D hDsupp hD'
  rw [hsub] at two
  exact two

private theorem deg_eq_one_of_isRational {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E]
    (Q : Place K E) (hQ : Q.IsRational) : Q.deg = 1 := by
  have hbij : Function.Bijective (Algebra.linearMap K Q.ResidueField) :=
    ⟨(algebraMap K Q.ResidueField).injective, hQ⟩
  have e : K ≃ₗ[K] Q.ResidueField := LinearEquiv.ofBijective _ hbij
  unfold Place.deg
  rw [← e.finrank_eq, Module.finrank_self]

private theorem degree_eq_sum_of_isRational {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E]
    (hrat : ∀ Q : Place K E, Q.IsRational) (D : Divisor K E) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro Q _
  simp [deg_eq_one_of_isRational Q (hrat Q)]

private theorem chart_mass {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (hrat : ∀ Q : Place (ResidueField A) Fbar, Q.IsRational)
    (f : F) (c : L) (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (hordc : ∀ P : Place L F, P.ord (c • f) = P.ord f)
    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ C.dom) (hD : ∀ P ∈ C.dom, D P = P.ord f) :
    (D.sum fun _ n => n) = -(∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩)) := by
  classical
  set fbar := C.residue ⟨c • f, hc⟩ with hfbar
  obtain ⟨Dbar, hDbar, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) fbar hres

  have hDoff : ∀ P, P ∉ C.dom → D P = 0 := by
    intro P hP
    by_contra h
    exact hP (hDsupp P (Finsupp.mem_support_iff.mpr h))

  have hmap : ∀ Q, Q ∉ C.nodes → Finsupp.mapDomain C.placeMap D Q = Q.ord fbar :=
    C.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P hP => by rw [hD P hP, hordc]) hDoff

  have hmap0 : ∀ Q ∈ C.nodes, Finsupp.mapDomain C.placeMap D Q = 0 := by
    intro Q hQ
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro P hP
    show Finsupp.single (C.placeMap P) (D P) Q = 0
    rw [Finsupp.single_apply, if_neg]
    intro hPQ
    exact C.placeMap_not_mem_nodes P (hDsupp P hP) (hPQ ▸ hQ)

  set Nbar : Divisor (ResidueField A) Fbar := ∑ x ∈ C.nodes, Finsupp.single x (x.ord fbar) with hNbar
  have hdec : Dbar = Finsupp.mapDomain C.placeMap D + Nbar := by
    ext Q
    rw [Finsupp.add_apply, hDbar Q, hNbar, Finsupp.finsetSum_apply]
    by_cases hQ : Q ∈ C.nodes
    · rw [hmap0 Q hQ, zero_add, Finset.sum_eq_single Q]
      · simp
      · intro x _ hxQ; simp [hxQ]
      · intro h; exact absurd hQ h
    · rw [hmap Q hQ, Finset.sum_eq_zero, add_zero]
      intro x hx
      rw [Finsupp.single_apply, if_neg]
      rintro rfl; exact hQ hx

  have h0 : (Dbar.sum fun _ n => n) = 0 := by rw [← degree_eq_sum_of_isRational hrat, hdeg]
  rw [hdec, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)] at h0
  have hN : (Nbar.sum fun _ n => n) = ∑ x ∈ C.nodes, x.ord fbar := by
    rw [hNbar, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    apply Finset.sum_congr rfl
    intro x _
    simp
  rw [hN] at h0
  linarith

private theorem exists_potential {G₀ : Type*} [CommGroupWithZero G₀] {ι : Type*} (t : G₀) (ht0 : t ≠ 0)
    (htors : ∀ n : ℤ, t ^ n = 1 → n = 0) (γ : ι → G₀) (hγ : ∀ i, γ i ≠ 0) :
    ∃ b : ι → ℤ, ∀ i j (k : ℤ), γ i = γ j * t ^ k → b i = b j + k := by
  classical
  set T : G₀ˣ := Units.mk0 t ht0 with hT
  let g : ι → G₀ˣ := fun i => Units.mk0 (γ i) (hγ i)
  let H : Subgroup G₀ˣ := Subgroup.zpowers T

  let rep : ι → G₀ˣ := fun i => Quotient.out (QuotientGroup.mk (s := H) (g i))
  have hrep : ∀ i, ∃ n : ℤ, rep i = g i * T ^ n := by
    intro i
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g i)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
    exact ⟨n, by rw [show rep i = g i * h from hh, ← hn]⟩
  choose nrep hnrep using hrep
  refine ⟨fun i => -nrep i, ?_⟩
  intro i j k hk
  have hgk : g i = g j * T ^ k := by
    apply Units.ext
    simp [g, hT, hk]
  have hmk : (QuotientGroup.mk (s := H) (g i) : G₀ˣ ⧸ H) = QuotientGroup.mk (g j) := by
    rw [QuotientGroup.eq, hgk, mul_inv_rev, inv_mul_cancel_right]
    exact H.inv_mem (Subgroup.zpow_mem_zpowers T k)
  have hreq : rep i = rep j := by
    show Quotient.out _ = Quotient.out _
    rw [hmk]
  have h1 := hnrep i
  have h2 := hnrep j
  rw [hreq, hgk] at h1

  have hT' : T ^ (k + nrep i - nrep j) = 1 := by
    have : g j * T ^ (k + nrep i) = g j * T ^ nrep j := by rw [zpow_add, ← mul_assoc, ← h1, ← h2]
    have := mul_left_cancel this
    rw [zpow_sub, this, mul_inv_cancel]
  have ht' : t ^ (k + nrep i - nrep j) = 1 := by
    have := congrArg Units.val hT'
    simpa [hT] using this
  have := htors _ ht'
  show -nrep i = -nrep j + k
  omega

private theorem telescope {M : Type*} [AddCommGroup M] (pos : ℕ → M) (s : ℕ → ℤ) (w : ℕ) (hw : 1 ≤ w) :
    ∑ k ∈ Finset.range w, s k • (pos k - pos (k + 1)) =
      s 0 • pos 0 - s (w - 1) • pos w + ∑ j ∈ Finset.Ico 1 w, (s j - s (j - 1)) • pos j := by
  induction w with
  | zero => omega
  | succ w ih =>
    rcases Nat.eq_zero_or_pos w with rfl | hw0
    · simp [smul_sub]
    · rw [Finset.sum_range_succ, ih hw0, Finset.sum_Ico_succ_top hw0]
      simp only [Nat.add_sub_cancel]
      obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le' hw0
      simp only [Nat.add_sub_cancel]
      rw [smul_sub, sub_smul]
      abel

private theorem depth_bounds (π : A) (hπ0 : π ≠ 0) (An : Annulus A F)
    {P : Place L F} (hP : P ∈ An.dom) (w : ℕ) (u' : Aˣ) (hw : An.modulus = u' * π ^ w)
    (d : ℕ) (u : Aˣ) (h : P.evalAt An.param ∈ A) (hd : (⟨P.evalAt An.param, h⟩ : A) = u * π ^ d) :
    0 < d ∧ d < w := by
  obtain ⟨-, -, ⟨h', hmax⟩, -, m, hm, hmod⟩ := An.mem_dom P hP
  have hh : (⟨P.evalAt An.param, h'⟩ : A) = ⟨P.evalAt An.param, h⟩ := rfl
  rw [hh, hd] at hmax
  constructor
  · by_contra h0
    have : d = 0 := by omega
    subst this
    rw [pow_zero, mul_one] at hmax
    exact (mem_maximalIdeal _).mp hmax u.isUnit
  · by_contra hdw
    push Not at hdw

    have hA : (u' : A) * π ^ w = u * π ^ d * m := by
      rw [← hw, ← hd]
      apply Subtype.ext
      simpa using hmod
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdw
    have hu' : (u' : A) = u * π ^ k * m := by
      have h1 : (u' : A) * π ^ w = (u * π ^ k * m) * π ^ w := by rw [hA]; ring
      exact mul_right_cancel₀ (pow_ne_zero _ hπ0) h1
    have : (u' : A) ∈ maximalIdeal A := by rw [hu']; exact Ideal.mul_mem_left _ _ hm
    exact (mem_maximalIdeal _).mp this u'.isUnit

private theorem chart_width_pos (π : A) (An : Annulus A F) (w : ℕ) (u' : Aˣ) (hw : An.modulus = u' * π ^ w) :
    1 ≤ w := by
  by_contra h
  have : w = 0 := by omega
  subst this
  rw [pow_zero, mul_one] at hw
  exact (mem_maximalIdeal _).mp (hw ▸ An.modulus_mem) u'.isUnit

private theorem filter_sum_eq (D : Divisor L F) (p : Place L F → Prop) [DecidablePred p] :
    ((D.filter p).sum fun _ n => n) = ∑ P ∈ D.support.filter p, D P := by
  rw [Finsupp.sum, Finsupp.support_filter]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hP).2]

private theorem filter_prod_eq {M : Type*} [CommMonoid M] (D : Divisor L F) (p : Place L F → Prop) [DecidablePred p]
    (g : Place L F → ℤ → M) :
    ((D.filter p).prod g) = ∏ P ∈ D.support.filter p, g P (D P) := by
  rw [Finsupp.prod, Finsupp.support_filter]
  apply Finset.prod_congr rfl
  intro P hP
  rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hP).2]

private theorem prod_zpow₀ {G₀ : Type*} [CommGroupWithZero G₀] {ι : Type*} (t : G₀) (ht : t ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, t ^ f i = t ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ ht]

private theorem sum_indicator_le (d w : ℕ) (hdw : d ≤ w) :
    ∑ i ∈ Finset.range w, (if d ≤ i then (1 : ℤ) else 0) = (w : ℤ) - d := by
  induction w with
  | zero => simp; omega
  | succ w ih =>
    rcases Nat.eq_or_lt_of_le hdw with h | h
    · subst h
      rw [Finset.sum_eq_zero]
      · simp
      · intro i hi
        rw [if_neg]
        have := Finset.mem_range.mp hi
        omega
    · rw [Finset.sum_range_succ, ih (by omega), if_pos (by omega)]
      push_cast
      ring

private theorem valuation_zpow_eq_one (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (n : ℤ)
    (h : A.valuation (π : L) ^ n = 1) : n = 0 := by
  have hlt : A.valuation (π : L) < 1 := (A.valuation_lt_one_iff _).mp hπ
  have hne : A.valuation (π : L) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact fun h0 => hπ0 (Subtype.ext h0)
  set T : (A.ValueGroup)ˣ := Units.mk0 _ hne with hT
  have hT1 : 1 < T⁻¹ := by
    rw [one_lt_inv']
    show (T : A.ValueGroup) < 1
    simpa [hT] using hlt
  have hmono := zpow_right_strictMono hT1
  have hTn : (T⁻¹) ^ n = (T⁻¹) ^ (0 : ℤ) := by
    rw [zpow_zero, inv_zpow, inv_eq_one]
    apply Units.ext
    simpa [hT] using h
  exact hmono.injective hTn

end AlgebraicCurve.Multidegree

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor RegularProlongation"
namespace Multidegree
namespace Chain
p2m_open "AlgebraicCurve"

private def vpos {n m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n) (e : Fin m) (j : ℕ) :
    Fin n ⊕ (Σ e : Fin m, Fin (w e - 1)) :=
  if h0 : j = 0 then Sum.inl (src e) else if h : j < w e then Sum.inr ⟨e, ⟨j - 1, by omega⟩⟩ else Sum.inl (tgt e)

private theorem vpos_zero {n m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n) (e : Fin m) :
    vpos w src tgt e 0 = Sum.inl (src e) := by simp [vpos]

private theorem vpos_w {n m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n) (e : Fin m) (hw : 1 ≤ w e) :
    vpos w src tgt e (w e) = Sum.inl (tgt e) := by
  simp only [vpos]
  rw [dif_neg (by omega), dif_neg (lt_irrefl _)]

private theorem vpos_mid {n m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n) (e : Fin m) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j < w e) : vpos w src tgt e j = Sum.inr ⟨e, ⟨j - 1, by omega⟩⟩ := by
  simp only [vpos]
  rw [dif_neg (by omega), dif_pos h2]

private theorem ends_eq_vpos {n m : ℕ} (w : Fin m → ℕ) (src tgt : Fin m → Fin n)
    (ends : (Σ e : Fin m, Fin (w e)) → (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))) × (Fin n ⊕ (Σ e : Fin m, Fin (w e - 1))))
    (hends : ∀ ε, ends ε =
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩))
    (e : Fin m) (k : Fin (w e)) :
    ends ⟨e, k⟩ = (vpos w src tgt e k, vpos w src tgt e (k + 1)) := by
  rw [hends]
  have hk := k.2
  ext1
  · dsimp only
    by_cases h0 : k.1 = 0
    · rw [dif_pos h0, h0, vpos_zero]
    · rw [dif_neg h0, vpos_mid w src tgt e k (by omega) hk]
  · dsimp only
    by_cases h1 : k.1 + 1 = w e
    · rw [dif_pos h1, h1, vpos_w w src tgt e (by omega)]
    · rw [dif_neg h1, vpos_mid w src tgt e (k + 1) (by omega) (by omega)]
      simp

private theorem sum_sigma_fin_eq_sum_range {m : ℕ} {M : Type*} [AddCommMonoid M] (w : Fin m → ℕ)
    (g : Fin m → ℕ → M) :
    ∑ ε : (Σ e : Fin m, Fin (w e)), g ε.1 ε.2 = ∑ e, ∑ k ∈ Finset.range (w e), g e k := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  exact Fin.sum_univ_eq_sum_range (g e) (w e)

private theorem sum_nodes_eq_sum_ends {n m : ℕ} {ι : Fin n → Type*}
    (nodes : ∀ i, Finset (ι i)) (src tgt : Fin m → Fin n) (xs : ∀ e, ι (src e)) (xt : ∀ e, ι (tgt e))
    (hmem : ∀ e, xs e ∈ nodes (src e) ∧ xt e ∈ nodes (tgt e))
    (hex : ∀ i, ∀ x ∈ nodes i, ∃ e, (⟨src e, xs e⟩ : Σ j, ι j) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, ι j) = ⟨i, x⟩)
    (huniq : ∀ i, ∀ x ∈ nodes i, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E')
    {M : Type*} [AddCommMonoid M] (G : (Σ j, ι j) → M) :
    ∑ i, ∑ x ∈ nodes i, G ⟨i, x⟩ = ∑ e, G ⟨src e, xs e⟩ + ∑ e, G ⟨tgt e, xt e⟩ := by
  classical
  set elim : Fin m ⊕ Fin m → (Σ j, ι j) :=
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) with helim
  have hR : ∑ e, G ⟨src e, xs e⟩ + ∑ e, G ⟨tgt e, xt e⟩ = ∑ E : Fin m ⊕ Fin m, G (elim E) := by
    rw [Fintype.sum_sum_type]
    rfl
  have hL : ∑ i, ∑ x ∈ nodes i, G ⟨i, x⟩ = ∑ σ ∈ Finset.univ.sigma nodes, G σ := by
    rw [Finset.sum_sigma]
  rw [hR, hL]
  symm
  apply Finset.sum_nbij elim
  · intro E _
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases E with e | e
    · exact (hmem e).1
    · exact (hmem e).2
  · intro E _ E' _ hEE'
    have hm : (elim E).2 ∈ nodes (elim E).1 := by
      rcases E with e | e
      · exact (hmem e).1
      · exact (hmem e).2
    exact huniq (elim E).1 (elim E).2 hm E E' rfl hEE'.symm
  · intro σ hσ
    obtain ⟨-, hx⟩ := Finset.mem_sigma.mp (Finset.mem_coe.mp hσ)
    obtain ⟨e, he | he⟩ := hex σ.1 σ.2 hx
    · exact ⟨Sum.inl e, Finset.mem_coe.mpr (Finset.mem_univ _), he⟩
    · exact ⟨Sum.inr e, Finset.mem_coe.mpr (Finset.mem_univ _), he⟩
  · intro E _
    rfl

end AlgebraicCurve.Multidegree.Chain

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor RegularProlongation"
namespace Multidegree
namespace Graph
p2m_open "AlgebraicCurve"

variable {V E : Type*} [DecidableEq V] [Fintype E]

private def lap (ends : E → V × V) (v : V) : V → ℤ :=
  ∑ ε, ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - Pi.single (ends ε).2 1 else 0) +
        (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - Pi.single (ends ε).1 1 else 0))

private def inc (ends : E → V × V) (ε : E) (x : V) : ℤ :=
  (if (ends ε).1 = x then 1 else 0) - (if (ends ε).2 = x then 1 else 0)

private theorem lap_apply (ends : E → V × V) (v x : V) :
    lap ends v x = ∑ ε, inc ends ε v * inc ends ε x := by
  classical
  simp only [lap, inc, Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun ε _ => ?_
  by_cases h1 : (ends ε).1 = v <;> by_cases h2 : (ends ε).2 = v <;>
    simp [h1, h2, Pi.single_apply, Pi.sub_apply, eq_comm]

private theorem sum_smul_lap_apply [Fintype V] (ends : E → V × V) (u : V → ℤ) (x : V) :
    (∑ v, u v • lap ends v) x = ∑ ε, (u (ends ε).1 - u (ends ε).2) * inc ends ε x := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, lap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ε _ => ?_

  have : ∑ v, u v * inc ends ε v = u (ends ε).1 - u (ends ε).2 := by
    simp only [inc, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc ∑ v, u v * (inc ends ε v * inc ends ε x)
      = (∑ v, u v * inc ends ε v) * inc ends ε x := by rw [Finset.sum_mul]; simp only [mul_assoc]
    _ = _ := by rw [this]

private theorem mem_closure_range_lap [Fintype V] (ends : E → V × V) (a : V → ℤ) (u : V → ℤ)
    (ha : ∀ x, a x = ∑ ε, (u (ends ε).1 - u (ends ε).2) * inc ends ε x) :
    a ∈ AddSubgroup.closure (Set.range (lap ends)) := by
  have : a = ∑ v, u v • lap ends v := by
    funext x; rw [ha, sum_smul_lap_apply]
  rw [this]
  exact AddSubgroup.sum_mem _ fun v _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self v)) _

end AlgebraicCurve.Multidegree.Graph

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
    ∃ φ : Divisor L F →+ (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap),
      (∀ i, ∀ P ∈ (C i).dom,
        φ (Finsupp.single P 1) = QuotientAddGroup.mk (Pi.single (Sum.inl i) 1 : V → ℤ)) ∧
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d → ∀ (hd0 : 0 < d) (hdw : d < w e),
          φ (Finsupp.single P 1) =
            QuotientAddGroup.mk (Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1 : V → ℤ)) ∧
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) → φ (Finsupp.single P 1) = 0) ∧
      (∀ f : F, f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord f) →
        (∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
          ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
            (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d) →
        φ D = 0) := by
  intro V ends lap

  have _hratF := hratF
  classical

  let Lat : Fin m → Place L F → Prop := fun e P =>
    P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
      (⟨P.evalAt (An e).param, h⟩ : A) = u * π ^ d ∧ 0 < d ∧ d < w e

  let ψ : Place L F → (V → ℤ) := fun P =>
    if h : ∃ i, P ∈ (C i).dom then Pi.single (Sum.inl h.choose) 1
    else if h' : ∃ e, Lat e P then
      Pi.single (Sum.inr ⟨h'.choose, ⟨h'.choose_spec.2.choose - 1, by
        have := h'.choose_spec.2.choose_spec
        obtain ⟨u, hu, -, hd0, hdw⟩ := this
        omega⟩⟩) 1
    else 0
  let φ₀ : Divisor L F →+ (V → ℤ) := Finsupp.liftAddHom fun P => zmultiplesHom (V → ℤ) (ψ P)
  have hφ₀ : ∀ P, φ₀ (Finsupp.single P 1) = ψ P := by
    intro P
    simp only [φ₀, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  let N := AddSubgroup.closure (Set.range lap)
  refine ⟨(QuotientAddGroup.mk' N).comp φ₀, ?h1, ?h2, ?h3, ?h4⟩
  case h1 =>

    intro i P hP
    have hex : ∃ j, P ∈ (C j).dom := ⟨i, hP⟩
    have hi : hex.choose = i := by
      rcases hcover P with ⟨i₀, hi₀, huniq, -⟩ | ⟨e, -, -, hno⟩
      · rw [huniq _ hex.choose_spec, huniq _ hP]
      · exact absurd hP (hno i)
    rw [AddMonoidHom.comp_apply, hφ₀, QuotientAddGroup.mk'_apply]
    simp only [ψ, dif_pos hex, hi]
    rfl
  case h2 =>

    intro e P hP d u h hd hd0 hdw
    have hno : ¬ ∃ j, P ∈ (C j).dom := by
      rintro ⟨j, hj⟩
      rcases hcover P with ⟨i₀, -, -, hnoAn⟩ | ⟨e₀, -, -, hnoC⟩
      · exact hnoAn e hP
      · exact hnoC j hj
    have hex : ∃ e', Lat e' P := ⟨e, hP, d, u, h, hd, hd0, hdw⟩
    have he : hex.choose = e := by
      rcases hcover P with ⟨i₀, hi₀, -, -⟩ | ⟨e₀, -, huniq, -⟩
      · exact absurd ⟨i₀, hi₀⟩ hno
      · rw [huniq _ hex.choose_spec.1, huniq _ hP]
    subst he
    have hd' : hex.choose_spec.2.choose = d := by
      obtain ⟨u', h', hEq', -, -⟩ := hex.choose_spec.2.choose_spec
      exact AlgebraicCurve.Multidegree.depth_unique A π hπ hπ0 u' u _ _ (by rw [← hEq', ← hd])
    have hmk : ∀ (e₁ e₂ : Fin m) (a : Fin (w e₁ - 1)) (b : Fin (w e₂ - 1)), e₁ = e₂ → a.val = b.val →
        (⟨e₁, a⟩ : Σ e, Fin (w e - 1)) = ⟨e₂, b⟩ := by
      rintro e₁ e₂ a b rfl hab
      exact congrArg _ (Fin.ext hab)
    rw [AddMonoidHom.comp_apply, hφ₀, QuotientAddGroup.mk'_apply]
    simp only [ψ, dif_neg hno, dif_pos hex]
    exact congrArg (fun s : Σ e, Fin (w e - 1) => ((Pi.single (Sum.inr s) 1 : V → ℤ) : (V → ℤ) ⧸ N))
      (hmk _ _ _ _ rfl (by show hex.choose_spec.2.choose - 1 = d - 1; rw [hd']))
  case h3 =>

    intro e P hP hnot
    have hno : ¬ ∃ j, P ∈ (C j).dom := by
      rintro ⟨j, hj⟩
      rcases hcover P with ⟨i₀, -, -, hnoAn⟩ | ⟨e₀, -, -, hnoC⟩
      · exact hnoAn e hP
      · exact hnoC j hj
    have hno' : ¬ ∃ e', Lat e' P := by
      rintro ⟨e', hP', d, u, h, hd, -, -⟩
      have he' : e' = e := by
        rcases hcover P with ⟨i₀, hi₀, -, -⟩ | ⟨e₀, -, huniq, -⟩
        · exact absurd ⟨i₀, hi₀⟩ hno
        · rw [huniq _ hP', huniq _ hP]
      subst he'
      exact hnot ⟨d, u, h, hd⟩
    rw [AddMonoidHom.comp_apply, hφ₀, QuotientAddGroup.mk'_apply]
    simp only [ψ, dif_neg hno, dif_neg hno', QuotientAddGroup.mk_zero]
  case h4 =>
    intro f hf0 D hDord hlat
    rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]

    have hDoff : ∀ P, P ∉ D.support → D P = 0 := fun P hP => Finsupp.notMem_support_iff.mp hP
    choose c hc hres using fun i => (C i).exists_smul_mem f hf0
    have hc0 : ∀ i, c i ≠ 0 := fun i => AlgebraicCurve.Multidegree.const_ne_zero_of_residue (C i) (hc i) (hres i)
    choose uw huw using hw
    have hw1 : ∀ e, 1 ≤ w e := fun e => AlgebraicCurve.Multidegree.chart_width_pos π (An e) (w e) (uw e) (huw e)
    set S := D.support with hS
    set os : Fin m → ℤ := fun e => (xs e).ord ((C (src e)).residue ⟨c (src e) • f, hc (src e)⟩) with hos
    set ot : Fin m → ℤ := fun e => (xt e).ord ((C (tgt e)).residue ⟨c (tgt e) • f, hc (tgt e)⟩) with hot

    let dep : Fin m → Place L F → ℕ := fun e P =>
      if h : ∃ (d : ℕ) (u : Aˣ) (hm : P.evalAt (An e).param ∈ A), (⟨P.evalAt (An e).param, hm⟩ : A) = u * π ^ d
      then h.choose else 0

    have hlatA : ∀ e, ∀ P ∈ S, P ∈ (An e).dom →
        ∃ (u : Aˣ) (hm : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, hm⟩ : A) = u * π ^ dep e P ∧ 0 < dep e P ∧ dep e P < w e := by
      intro e P hPS hPe
      have hex : ∃ (d : ℕ) (u : Aˣ) (hm : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, hm⟩ : A) = u * π ^ d := by
        rcases hlat P hPS with ⟨i, hi⟩ | ⟨e', hPe', d, u, hm, hd⟩
        · rcases hcover P with ⟨i₀, -, -, hnoAn⟩ | ⟨e₀, -, -, hnoC⟩
          · exact absurd hPe (hnoAn e)
          · exact absurd hi (hnoC i)
        · have : e' = e := by
            rcases hcover P with ⟨i₀, -, -, hnoAn⟩ | ⟨e₀, -, huniq, -⟩
            · exact absurd hPe (hnoAn e)
            · rw [huniq _ hPe', huniq _ hPe]
          subst this
          exact ⟨d, u, hm, hd⟩
      have hdepP : dep e P = hex.choose := by simp only [dep, dif_pos hex]
      obtain ⟨u, hm, hd⟩ := hex.choose_spec
      refine ⟨u, hm, hdepP ▸ hd, ?_⟩
      rw [hdepP]
      exact AlgebraicCurve.Multidegree.depth_bounds π hπ0 (An e) hPe (w e) (uw e) (huw e) _ u hm hd

    have hψC : ∀ i P, P ∈ (C i).dom → ψ P = Pi.single (Sum.inl i) 1 := by
      intro i P hP
      have hex : ∃ j, P ∈ (C j).dom := ⟨i, hP⟩
      have hi : hex.choose = i := by
        rcases hcover P with ⟨i₀, hi₀, huniq, -⟩ | ⟨e, -, -, hno⟩
        · rw [huniq _ hex.choose_spec, huniq _ hP]
        · exact absurd hP (hno i)
      simp only [ψ, dif_pos hex, hi]
    let vpos := AlgebraicCurve.Multidegree.Chain.vpos w src tgt
    have hψA : ∀ e, ∀ P ∈ S, P ∈ (An e).dom → ψ P = Pi.single (vpos e (dep e P)) 1 := by
      intro e P hPS hPe
      obtain ⟨u, hm, hd, hd0, hdw⟩ := hlatA e P hPS hPe
      have hno : ¬ ∃ j, P ∈ (C j).dom := by
        rintro ⟨j, hj⟩
        rcases hcover P with ⟨i₀, -, -, hnoAn⟩ | ⟨e₀, -, -, hnoC⟩
        · exact hnoAn e hPe
        · exact hnoC j hj
      have hex : ∃ e', Lat e' P := ⟨e, hPe, dep e P, u, hm, hd, hd0, hdw⟩
      have he : hex.choose = e := by
        rcases hcover P with ⟨i₀, hi₀, -, -⟩ | ⟨e₀, -, huniq, -⟩
        · exact absurd ⟨i₀, hi₀⟩ hno
        · rw [huniq _ hex.choose_spec.1, huniq _ hPe]
      have hd' : hex.choose_spec.2.choose = dep e P := by
        obtain ⟨u', h', hEq', -, -⟩ := hex.choose_spec.2.choose_spec
        refine AlgebraicCurve.Multidegree.depth_unique A π hπ hπ0 u' u _ _ ?_
        rw [← hEq', ← hd]
        apply Subtype.ext
        simp [he]
      have hmk : ∀ (e₁ e₂ : Fin m) (a : Fin (w e₁ - 1)) (b : Fin (w e₂ - 1)), e₁ = e₂ → a.val = b.val →
          (⟨e₁, a⟩ : Σ e, Fin (w e - 1)) = ⟨e₂, b⟩ := by
        rintro e₁ e₂ a b rfl hab
        exact congrArg _ (Fin.ext hab)
      simp only [ψ, dif_neg hno, dif_pos hex]
      rw [show vpos e (dep e P) = Sum.inr ⟨e, ⟨dep e P - 1, by omega⟩⟩ from
        AlgebraicCurve.Multidegree.Chain.vpos_mid w src tgt e _ hd0 hdw]
      congr 2
      exact hmk _ _ _ _ he (by show hex.choose_spec.2.choose - 1 = dep e P - 1; rw [hd'])

    let δ : V → (V → ℤ) := fun v => Pi.single v 1
    let pos : Fin m → ℕ → (V → ℤ) := fun e j => δ (vpos e j)
    let SC : Fin n → Finset (Place L F) := fun i => S.filter (· ∈ (C i).dom)
    let SA : Fin m → Finset (Place L F) := fun e => S.filter (· ∈ (An e).dom)
    have hφ₀D : φ₀ D = ∑ P ∈ S, D P • ψ P := by
      simp only [φ₀, Finsupp.liftAddHom_apply]
      rfl
    have hsplit : ∑ P ∈ S, D P • ψ P =
        ∑ i, ∑ P ∈ SC i, D P • δ (Sum.inl i) + ∑ e, ∑ P ∈ SA e, D P • pos e (dep e P) := by
      have hpt : ∀ P ∈ S, D P • ψ P =
          ∑ i, (if P ∈ (C i).dom then D P • δ (Sum.inl i) else 0) +
          ∑ e, (if P ∈ (An e).dom then D P • pos e (dep e P) else 0) := by
        intro P hPS
        rcases hcover P with ⟨i₀, hi₀, huniq, hnoAn⟩ | ⟨e₀, he₀, huniq, hnoC⟩
        · rw [hψC i₀ P hi₀, Finset.sum_eq_single i₀, if_pos hi₀, Finset.sum_eq_zero, add_zero]
          · intro e _; rw [if_neg (hnoAn e)]
          · intro j _ hj; rw [if_neg]; exact fun h => hj (huniq j h)
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [hψA e₀ P hPS he₀, Finset.sum_eq_zero, zero_add, Finset.sum_eq_single e₀, if_pos he₀]
          · intro e _ he; rw [if_neg]; exact fun h => he (huniq e h)
          · intro h; exact absurd (Finset.mem_univ _) h
          · intro i _; rw [if_neg (hnoC i)]
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := S)]
      congr 1
      · apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_filter]
      · apply Finset.sum_congr rfl; intro e _
        rw [Finset.sum_filter]

    have hchart : ∀ i, ∑ P ∈ SC i, D P =
        -(∑ x ∈ (C i).nodes, x.ord ((C i).residue ⟨c i • f, hc i⟩)) := by
      intro i
      rw [← AlgebraicCurve.Multidegree.filter_sum_eq D (· ∈ (C i).dom)]
      refine AlgebraicCurve.Multidegree.chart_mass (C i) (hratBar i) f (c i) (hc i) (hres i)
        (fun P => AlgebraicCurve.Multidegree.ord_smul_const P (hc0 i) hf0) _ ?_ ?_
      · intro P hP
        rw [Finsupp.support_filter, Finset.mem_filter] at hP
        exact hP.2
      · intro P hP
        rw [Finsupp.filter_apply_pos _ _ hP, hDord]
    have hchartV : ∑ i, ∑ P ∈ SC i, D P • δ (Sum.inl i) =
        -(∑ e, os e • δ (Sum.inl (src e)) + ∑ e, ot e • δ (Sum.inl (tgt e))) := by
      have h1 : ∀ i, ∑ P ∈ SC i, D P • δ (Sum.inl i) =
          -(∑ x ∈ (C i).nodes, x.ord ((C i).residue ⟨c i • f, hc i⟩) • δ (Sum.inl i)) := by
        intro i
        rw [← Finset.sum_smul, hchart i, neg_smul, Finset.sum_smul]
      simp only [h1, Finset.sum_neg_distrib]
      congr 1
      exact AlgebraicCurve.Multidegree.Chain.sum_nodes_eq_sum_ends
        (ι := fun j => Place (IsLocalRing.ResidueField A) (Fbar j))
        (fun i => (C i).nodes) src tgt xs xt (fun e => ⟨(hatt e).1.1, (hatt e).2.1⟩) hnodes.1 hnodes.2
        (fun σ => σ.2.ord ((C σ.1).residue ⟨c σ.1 • f, hc σ.1⟩) • δ (Sum.inl σ.1))

    set t := A.valuation (π : L) with ht
    have ht0 : t ≠ 0 := by
      rw [ht, Ne, map_eq_zero]; exact fun h0 => hπ0 (Subtype.ext h0)
    have hvz : ∀ e, ∀ P ∈ SA e, A.valuation (P.evalAt (An e).param) = t ^ dep e P := by
      intro e P hP
      obtain ⟨hPS, hPe⟩ := Finset.mem_filter.mp hP
      obtain ⟨u, hm, hd, -, -⟩ := hlatA e P hPS hPe
      have : P.evalAt (An e).param = ((u : A) : L) * (π : L) ^ dep e P := by
        have := congrArg Subtype.val hd
        simpa using this
      rw [this, map_mul, map_pow, (A.valuation_eq_one_iff _).mp u.isUnit, one_mul]
    have hvmod : ∀ e, A.valuation ((An e).modulus : L) = t ^ w e := by
      intro e
      rw [huw e]
      push_cast
      rw [map_mul, map_pow, (A.valuation_eq_one_iff _).mp (uw e).isUnit, one_mul]

    set kk : Fin m → ℤ := fun e => (∑ P ∈ SA e, (dep e P : ℤ) * D P) - (w e : ℤ) * ot e with hkk
    have hann : ∀ e, (∑ P ∈ SA e, D P = os e + ot e) ∧
        A.valuation (c (src e)) = A.valuation (c (tgt e)) * t ^ kk e := by
      intro e
      obtain ⟨hdom, -, hmod0, hparam⟩ := hpair e
      have two := AlgebraicCurve.Multidegree.annulus_two_end (An e) (An' e) (C (src e)) (C (tgt e)) (xs e) (xt e)
        hdom hmod0 hparam (hatt e).1 (hatt e).2 f hf0 (c (src e)) (c (tgt e))
        (hc (src e)) (hres (src e)) (hc (tgt e)) (hres (tgt e)) (D.filter (· ∈ (An e).dom))
        (fun P hP => by rw [Finsupp.support_filter, Finset.mem_filter] at hP; exact hP.2)
        (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hDord])
      rw [AlgebraicCurve.Multidegree.filter_sum_eq, AlgebraicCurve.Multidegree.filter_prod_eq] at two
      obtain ⟨hmass, hprod⟩ := two
      refine ⟨hmass, ?_⟩

      have hL : ∏ P ∈ SA e, A.valuation (P.evalAt (An e).param) ^ D P = t ^ ∑ P ∈ SA e, (dep e P : ℤ) * D P := by
        rw [← AlgebraicCurve.Multidegree.prod_zpow₀ t ht0]
        apply Finset.prod_congr rfl
        intro P hP
        rw [hvz e P hP, ← zpow_natCast, ← zpow_mul]
      rw [hL, hvmod, map_div₀, ← zpow_natCast, ← zpow_mul] at hprod
      have hct : A.valuation (c (tgt e)) ≠ 0 := by rw [Ne, map_eq_zero]; exact hc0 _

      have hprod' : t ^ (∑ P ∈ SA e, (dep e P : ℤ) * D P)
          = A.valuation (c (src e)) / A.valuation (c (tgt e)) * t ^ ((w e : ℤ) * ot e) := hprod
      have hta : t ^ ((w e : ℤ) * ot e) ≠ 0 := zpow_ne_zero _ ht0
      rw [hkk]
      simp only
      rw [zpow_sub₀ ht0, hprod', mul_div_assoc, div_self hta, mul_one, div_eq_mul_inv,
        mul_comm (A.valuation (c (src e))) _, ← mul_assoc, mul_inv_cancel₀ hct, one_mul]

    obtain ⟨b, hb⟩ := AlgebraicCurve.Multidegree.exists_potential t ht0
      (AlgebraicCurve.Multidegree.valuation_zpow_eq_one π hπ hπ0)
      (fun i => A.valuation (c i)) (fun i => by rw [Ne, map_eq_zero]; exact hc0 i)
    have hbe : ∀ e, b (src e) = b (tgt e) + kk e := fun e => hb _ _ _ (hann e).2

    let Nf : Fin m → ℕ → ℤ := fun e j => ∑ P ∈ SA e, if dep e P = j then D P else 0
    let s : Fin m → ℕ → ℤ := fun e j => os e - ∑ P ∈ SA e, if dep e P ≤ j then D P else 0
    have hs0 : ∀ e, s e 0 = os e := by
      intro e
      simp only [s]
      rw [Finset.sum_eq_zero, sub_zero]
      intro P hP
      obtain ⟨-, -, -, hd0, -⟩ := hlatA e P (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
      rw [if_neg (by omega)]
    have hsw : ∀ e, s e (w e - 1) = -ot e := by
      intro e
      simp only [s]
      rw [Finset.sum_congr rfl (g := fun P => D P), (hann e).1]
      · ring
      · intro P hP
        obtain ⟨-, -, -, -, hdw⟩ := hlatA e P (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
        rw [if_pos (by omega)]
    have hsdiff : ∀ e j, 1 ≤ j → s e j - s e (j - 1) = -Nf e j := by
      intro e j hj
      simp only [s, Nf]
      rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro P _
      split_ifs <;> omega
    have hssum : ∀ e, ∑ i ∈ Finset.range (w e), s e i = kk e := by
      intro e
      simp only [s, kk]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, Finset.sum_comm]
      have hin : ∀ P ∈ SA e, ∑ i ∈ Finset.range (w e), (if dep e P ≤ i then D P else 0)
          = ((w e : ℤ) - dep e P) * D P := by
        intro P hP
        obtain ⟨-, -, -, -, hdw⟩ := hlatA e P (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
        rw [← AlgebraicCurve.Multidegree.sum_indicator_le (dep e P) (w e) hdw.le, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hin]
      have hm := (hann e).1
      rw [nsmul_eq_mul]
      have : ∑ P ∈ SA e, ((w e : ℤ) - dep e P) * D P
          = (w e : ℤ) * ∑ P ∈ SA e, D P - ∑ P ∈ SA e, (dep e P : ℤ) * D P := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro P _; ring
      rw [this, hm]
      ring

    let u : V → ℤ := fun v => match v with
      | Sum.inl i => -b i
      | Sum.inr ⟨e, j⟩ => -b (src e) + ∑ i ∈ Finset.range (j.val + 1), s e i
    let U : Fin m → ℕ → ℤ := fun e j => -b (src e) + ∑ i ∈ Finset.range j, s e i
    have hU : ∀ e j, j ≤ w e → u (vpos e j) = U e j := by
      intro e j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [U, Finset.range_zero, Finset.sum_empty, add_zero]
        rw [show vpos e 0 = Sum.inl (src e) from AlgebraicCurve.Multidegree.Chain.vpos_zero w src tgt e]
      · rcases Nat.lt_or_ge j (w e) with hjw | hjw
        · rw [show vpos e j = Sum.inr ⟨e, ⟨j - 1, by omega⟩⟩ from
            AlgebraicCurve.Multidegree.Chain.vpos_mid w src tgt e j hj0 hjw]
          simp only [u, U]
          rw [Nat.sub_add_cancel hj0]
        · have hjeq : j = w e := le_antisymm hj hjw
          subst hjeq
          rw [show vpos e (w e) = Sum.inl (tgt e) from AlgebraicCurve.Multidegree.Chain.vpos_w w src tgt e (hw1 e)]
          simp only [u, U]
          rw [hssum e, hbe e]
          ring
    have hUdiff : ∀ e k, U e k - U e (k + 1) = -s e k := by
      intro e k
      simp only [U, Finset.sum_range_succ]
      ring

    have hfib : ∀ e, ∑ P ∈ SA e, D P • pos e (dep e P) = ∑ j ∈ Finset.Ico 1 (w e), Nf e j • pos e j := by
      intro e
      rw [← Finset.sum_fiberwise_of_maps_to (s := SA e) (t := Finset.Ico 1 (w e)) (g := dep e)
        (fun P hP => by
          obtain ⟨-, -, -, hd0, hdw⟩ := hlatA e P (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
          exact Finset.mem_Ico.mpr ⟨hd0, hdw⟩)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Nf]
      rw [Finset.sum_smul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P _
      split_ifs with h
      · rw [h]
      · rw [zero_smul]
    have hchain : ∀ e, ∑ k ∈ Finset.range (w e), (u (vpos e k) - u (vpos e (k + 1))) • (pos e k - pos e (k + 1))
        = -(os e • δ (Sum.inl (src e)) + ot e • δ (Sum.inl (tgt e))) + ∑ P ∈ SA e, D P • pos e (dep e P) := by
      intro e
      have h1 : ∑ k ∈ Finset.range (w e), (u (vpos e k) - u (vpos e (k + 1))) • (pos e k - pos e (k + 1))
          = ∑ k ∈ Finset.range (w e), (-s e k) • (pos e k - pos e (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [hU e k hk'.le, hU e (k + 1) hk', hUdiff]
      rw [h1]
      simp only [neg_smul, Finset.sum_neg_distrib]
      rw [AlgebraicCurve.Multidegree.telescope (pos e) (s e) (w e) (hw1 e), hs0, hsw, hfib]
      rw [Finset.sum_congr rfl (fun j hj => by rw [hsdiff e j (Finset.mem_Ico.mp hj).1])]
      simp only [pos, neg_smul, Finset.sum_neg_distrib]
      rw [show vpos e 0 = Sum.inl (src e) from AlgebraicCurve.Multidegree.Chain.vpos_zero w src tgt e,
        show vpos e (w e) = Sum.inl (tgt e) from AlgebraicCurve.Multidegree.Chain.vpos_w w src tgt e (hw1 e)]
      abel

    have hvec : φ₀ D = ∑ ε : (Σ e : Fin m, Fin (w e)),
        (u (ends ε).1 - u (ends ε).2) • (δ (ends ε).1 - δ (ends ε).2) := by
      have hE : ∀ ε : (Σ e : Fin m, Fin (w e)), ends ε = (vpos ε.1 ε.2, vpos ε.1 (ε.2 + 1)) := by
        rintro ⟨e, k⟩
        exact AlgebraicCurve.Multidegree.Chain.ends_eq_vpos w src tgt ends (fun _ => rfl) e k
      rw [Finset.sum_congr rfl (fun ε _ => by rw [hE ε])]
      rw [AlgebraicCurve.Multidegree.Chain.sum_sigma_fin_eq_sum_range w
        (fun e k => (u (vpos e k) - u (vpos e (k + 1))) • (δ (vpos e k) - δ (vpos e (k + 1))))]
      rw [Finset.sum_congr rfl (fun e _ => hchain e), Finset.sum_add_distrib, Finset.sum_neg_distrib,
        Finset.sum_add_distrib, hφ₀D, hsplit, hchartV]
    refine AlgebraicCurve.Multidegree.Graph.mem_closure_range_lap ends (φ₀ D) u fun x => ?_
    rw [hvec, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro ε _
    simp only [AlgebraicCurve.Multidegree.Graph.inc, δ, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
    congr 1
    congr 1 <;> exact if_congr eq_comm rfl rfl

end S_AlgebraicCurve_exists_multidegree_of_semistableCovering
end P2MW
export P2MW.S_AlgebraicCurve_exists_multidegree_of_semistableCovering (solution)
