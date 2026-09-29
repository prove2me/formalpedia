-- Prove2me | solution 1 for AlgebraicCurve.exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7af8fe0d-29fd-5b72-8671-b7f20344e331

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace SlopeLawEngine

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  have := v.ord_coe_unit u
  simpa [u] using this

theorem ord_smul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap v hc, zero_add]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  have := v.evalAt_algebraMap_eq (0 : K)
  simpa using this

theorem degree_eq_sum_of_isRational (D : Divisor K F) (h : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp [Place.deg_eq_one_of_isRational (h v hv)]

end PlaceLemmas

section OneChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

@[reducible] def rp (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem const_ne_zero (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 :=
  (rp C).smul_const_ne_zero hc hres

theorem fun_ne_zero (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨c • (0 : F), hc⟩ : C.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem mapDomain_eq_ord_of_not_mem_nodes (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∉ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = Q.ord (C.residue ⟨c • f, hc⟩) := by
  refine C.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P hP => ?_) hDoff Q hQ
  rw [hDdom P hP]
  exact (ord_smul P (const_ne_zero C hc hres) (fun_ne_zero C hc hres)).symm

theorem mapDomain_eq_zero_of_mem_nodes (C : ComponentChart A F Fbar)
    (D : Divisor L F) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∈ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  show Finsupp.single (C.placeMap P) (D P) Q = 0
  rw [Finsupp.single_apply, if_neg]
  intro hPQ
  have hPdom : P ∈ C.dom := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (hDoff P h)
  exact C.placeMap_not_mem_nodes P hPdom (hPQ ▸ hQ)

theorem sum_mapDomain (C : ComponentChart A F Fbar) (D : Divisor L F) :
    ((Finsupp.mapDomain C.placeMap D).sum fun _ n => n) = D.sum fun _ n => n :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem sum_nodes_ord_eq_zero [HasPrincipalDivisors (ResidueField A) Fbar]
    (hrat : ∀ x : Place (ResidueField A) Fbar, x.IsRational)
    (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (hmass : (D.sum fun _ n => n) = 0) :
    ∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩) = 0 := by
  classical
  set g : Fbar := C.residue ⟨c • f, hc⟩ with hg
  obtain ⟨E, hE, hdegE⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) g hres

  set N : Divisor (ResidueField A) Fbar := ∑ x ∈ C.nodes, Finsupp.single x (x.ord g) with hN
  have hN_apply : ∀ y, N y = if y ∈ C.nodes then y.ord g else 0 := by
    intro y
    rw [hN, Finsupp.finsetSum_apply]
    split_ifs with hy
    · rw [Finset.sum_eq_single y (fun x _ hxy => by rw [Finsupp.single_apply, if_neg hxy])
        (fun h => (h hy).elim), Finsupp.single_eq_same]
    · exact Finset.sum_eq_zero fun x hx => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hy hx
  have hEeq : E = Finsupp.mapDomain C.placeMap D + N := by
    ext y
    rw [Finsupp.add_apply, hN_apply, hE y]
    by_cases hy : y ∈ C.nodes
    · rw [if_pos hy, mapDomain_eq_zero_of_mem_nodes C D hDoff y hy, zero_add]
    · rw [if_neg hy, mapDomain_eq_ord_of_not_mem_nodes C hc hres D hDdom hDoff y hy, add_zero]

  have hmassE : (E.sum fun _ n => n) = 0 := by
    rw [← degree_eq_sum_of_isRational E (fun v _ => hrat v)]
    exact hdegE
  have hmassN : (N.sum fun _ n => n) = ∑ x ∈ C.nodes, x.ord g := by
    rw [hN, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index rfl
  rw [hEeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_mapDomain, hmass, zero_add,
    hmassN] at hmassE
  exact hmassE

end OneChart

section OneAnnulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

private theorem transfer_end {I : ValuationSubring F} (res : I →+* Fb) (x : Place (ResidueField A) Fb)
    {S S' : Set (Place L F)} (hS : S = S') {p p' : F} (hp : p = p')
    (H : ∃ hz : p ∈ I, x.ord (res ⟨p, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) → ∀ P ∈ S,
        ∃ h : P.evalAt f * (P.evalAt p) ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) :
    ∃ hz : p' ∈ I, x.ord (res ⟨p', hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S', P.ord f = 0) → ∀ P ∈ S',
        ∃ h : P.evalAt f * (P.evalAt p') ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  subst hS; subst hp; exact H

theorem param_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) : An.param ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
  exact hne (by rw [h0, evalAt_zero])

theorem end_orders (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    {f : F} (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    (hN : ∀ P ∈ An.dom, N P = P.ord f) (hNsum : (N.sum fun _ k => k) = 0)
    (hNprod : (N.prod fun P k => A.valuation (P.evalAt An.param) ^ k) = 1)
    {ca : L} (hca : ca • f ∈ Ca.integers) (hresa : Ca.residue ⟨ca • f, hca⟩ ≠ 0)
    {cb : L} (hcb : cb • f ∈ Cb.integers) (hresb : Cb.residue ⟨cb • f, hcb⟩ ≠ 0) :
    xa.ord (Ca.residue ⟨ca • f, hca⟩) + xb.ord (Cb.residue ⟨cb • f, hcb⟩) = 0 ∧
    A.valuation ca * (A.valuation cb)⁻¹ *
        A.valuation (An.modulus : L) ^ (xb.ord (Cb.residue ⟨cb • f, hcb⟩)) = 1 := by
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₁
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hca0 : ca ≠ 0 := const_ne_zero Ca hca hresa
  have hcb0 : cb ≠ 0 := const_ne_zero Cb hcb hresb
  have hf0 : f ≠ 0 := fun_ne_zero Ca hca hresa

  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, Hb⟩ := hatt'
  obtain ⟨hzb, hxb, hslb⟩ := transfer_end Cb.residue xb hdom hp' Hb

  set c' : L := ca * cb⁻¹ with hc'
  have hc'0 : c' ≠ 0 := mul_ne_zero hca0 (inv_ne_zero hcb0)
  have hh0 : ca • f ≠ 0 := smul_ne_zero hca0 hf0
  have heq : (algebraMap L F c')⁻¹ * (ca • f) = cb • f := by
    have hca' : algebraMap L F ca ≠ 0 := (map_ne_zero _).mpr hca0
    rw [hc', Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀]
    field_simp
  have hhb : (algebraMap L F c')⁻¹ * (ca • f) ∈ Cb.integers := heq ▸ hcb
  have hsub : (⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ : Cb.integers) = ⟨cb • f, hcb⟩ :=
    Subtype.ext heq
  have hresb' : Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ ≠ 0 := by rw [hsub]; exact hresb

  have hordh : ∀ P ∈ An.dom, N P = P.ord (ca • f) := fun P hP => by
    rw [ord_smul P hca0 hf0]; exact hN P hP
  obtain ⟨hmass, hprod⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (rp Ca) xa hza hxa hsla (rp Cb) xb hzb hxb hslb ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩
      (ca • f) hh0 hca hresa c' hc'0 hhb hresb' N hNdom hordh
  rw [hNsum] at hmass
  rw [hNprod] at hprod

  have hordb : xb.ord ((rp Cb).residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) =
      xb.ord (Cb.residue ⟨cb • f, hcb⟩) := by
    show xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) = _
    rw [hsub]
  rw [hordb] at hmass hprod
  refine ⟨?_, ?_⟩
  · exact hmass.symm
  · rw [hc', map_mul, map_inv₀] at hprod
    exact hprod.symm

end OneAnnulus

section Wide

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem mem_of_pow_mem {r : L} {k : ℕ} (hk : 0 < k) (hr : r ^ k ∈ A) : r ∈ A := by
  rw [← A.valuation_le_one_iff] at hr ⊢
  rw [map_pow] at hr
  by_contra h
  have h' : 1 < A.valuation r := not_le.mp h
  have : 1 < A.valuation r ^ k := one_lt_pow₀ h' hk.ne'
  exact absurd hr (not_le.mpr this)

theorem mem_maximalIdeal_of_pow {r : A} {k : ℕ} {a : A} (ha : a ∈ maximalIdeal A) (hr : r ^ k = a) :
    r ∈ maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro hu
  exact ha (hr ▸ hu.pow k)

theorem wide_of_isAlgClosed [IsAlgClosed L] (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  set μ : A := An.modulus with hμ
  have hμm : μ ∈ maximalIdeal A := An.modulus_mem
  have hvμ1 : A.valuation (μ : L) < 1 := (A.valuation_lt_one_iff μ).mp hμm
  have hvμ0 : A.valuation (μ : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hmod0

  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 2) two_pos
  have hrA : r ∈ A := mem_of_pow_mem two_pos (hr ▸ μ.2)
  have hr' : (⟨r, hrA⟩ : A) ^ 2 = μ := Subtype.ext (by simpa using hr)
  have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hr'
  have hr0 : r ≠ 0 := by rintro rfl; apply hmod0; rw [← hr]; simp

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 3) three_pos
  have hsA : s ∈ A := mem_of_pow_mem three_pos (hs ▸ μ.2)
  have hs' : (⟨s, hsA⟩ : A) ^ 3 = μ := Subtype.ext (by simpa using hs)
  have hsm : (⟨s, hsA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hs'
  have hs0 : s ≠ 0 := by rintro rfl; apply hmod0; rw [← hs]; simp
  have htm : (⟨s, hsA⟩ : A) ^ 2 ∈ maximalIdeal A :=
    Ideal.pow_mem_of_mem _ hsm 2 two_pos

  obtain ⟨Q₁, ⟨hQ₁, hQ₁z⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0
    ⟨⟨r, hrA⟩, hrm, by rw [← hμ, ← hr]; simp [pow_two]⟩
  obtain ⟨Q₂, ⟨hQ₂, hQ₂z⟩, -⟩ := An.existsUnique_evalAt_eq (⟨s, hsA⟩ ^ 2) htm (by simpa using hs0)
    ⟨⟨s, hsA⟩, hsm, by rw [← hμ, ← hs]; simp [pow_succ]⟩
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁z, hQ₂z]
  intro hv

  have h1 : A.valuation r ^ 2 = A.valuation (μ : L) := by rw [← map_pow, hr]
  have h2 : A.valuation (((⟨s, hsA⟩ : A) ^ 2 : A) : L) ^ 3 = A.valuation (μ : L) ^ 2 := by
    rw [← map_pow, ← map_pow]
    congr 1
    push_cast
    rw [← hs]; ring
  have hv' : A.valuation r = A.valuation (((⟨s, hsA⟩ : A) ^ 2 : A) : L) := hv
  rw [← hv'] at h2

  have ha0 : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have : A.valuation (μ : L) = 1 := by
    have h3 : A.valuation r ^ 3 * 1 = A.valuation r ^ 3 * A.valuation r := by
      rw [mul_one, ← pow_succ, h2, ← h1, ← pow_mul]
    have h4 : A.valuation r = 1 := (mul_left_cancel₀ (pow_ne_zero 3 ha0) h3).symm
    rw [← h1, h4, one_pow]
  exact absurd this hvμ1.ne

end Wide

section Nodes

open Finset

variable {ι E : Type*} [Fintype E] [DecidableEq ι] {P : ι → Type*}

theorem sum_nodes_eq_sum_ends (nodes : ∀ i, Finset (P i)) (src tgt : E → ι)
    (xs : ∀ e, P (src e)) (xt : ∀ e, P (tgt e))
    (hmem_s : ∀ e, xs e ∈ nodes (src e)) (hmem_t : ∀ e, xt e ∈ nodes (tgt e))
    (hex : ∀ i, ∀ x ∈ nodes i, ∃ e,
      (⟨src e, xs e⟩ : Σ j, P j) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, P j) = ⟨i, x⟩)
    (huniq : ∀ i, ∀ x ∈ nodes i, ∀ e₁ e₂ : E ⊕ E,
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) e₁ = ⟨i, x⟩ →
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) e₂ = ⟨i, x⟩ → e₁ = e₂)
    (φ : ∀ j, P j → ℤ) (i : ι) :
    ∑ x ∈ nodes i, φ i x =
      (∑ e ∈ univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
        ∑ e ∈ univ.filter (fun e => src e = i), φ (src e) (xs e) := by
  classical
  set endOf : E ⊕ E → Σ j, P j :=
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) with hendOf
  set Φ : (Σ j, P j) → ℤ := fun y => φ y.1 y.2 with hΦ
  set S : Finset (E ⊕ E) := univ.filter (fun t => (endOf t).1 = i) with hS

  have hend_mem : ∀ t : E ⊕ E, (endOf t).2 ∈ nodes (endOf t).1 := by
    rintro (e | e)
    · exact hmem_s e
    · exact hmem_t e

  have hR : (∑ e ∈ univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
      ∑ e ∈ univ.filter (fun e => src e = i), φ (src e) (xs e) = ∑ t ∈ S, Φ (endOf t) := by
    rw [hS, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type, add_comm]
    rfl

  have hL : ∑ x ∈ nodes i, φ i x = ∑ y ∈ (nodes i).map (Function.Embedding.sigmaMk i), Φ y := by
    rw [Finset.sum_map]
    rfl

  have himage : S.image endOf = (nodes i).map (Function.Embedding.sigmaMk i) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_map, Function.Embedding.sigmaMk_apply, hS,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨cast (congrArg P ht) (endOf t).2, ?_, ?_⟩
      · have := hend_mem t
        revert this
        generalize endOf t = y at ht ⊢
        obtain ⟨j, x⟩ := y
        cases ht
        exact id
      · generalize endOf t = y at ht ⊢
        obtain ⟨j, x⟩ := y
        cases ht
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨e, he | he⟩ := hex i x hx
      · exact ⟨Sum.inl e, by simp [hendOf, congrArg Sigma.fst he], he⟩
      · exact ⟨Sum.inr e, by simp [hendOf, congrArg Sigma.fst he], he⟩
  have hinj : Set.InjOn endOf (S : Set (E ⊕ E)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.coe_filter, hS, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht₁ ht₂
    have hy : ∃ x ∈ nodes i, endOf t₁ = ⟨i, x⟩ := by
      have := hend_mem t₁
      revert this
      generalize endOf t₁ = y at ht₁ ⊢
      obtain ⟨j, x⟩ := y
      cases ht₁
      exact fun h => ⟨x, h, rfl⟩
    obtain ⟨x, hx, h₁⟩ := hy
    exact huniq i x hx t₁ t₂ h₁ (heq ▸ h₁)
  rw [hL, hR, ← himage, Finset.sum_image hinj]

end Nodes

section General

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem sum_nodes_ord_add_sum_eq_zero [HasPrincipalDivisors (ResidueField A) Fbar]
    (hrat : ∀ x : Place (ResidueField A) Fbar, x.IsRational)
    (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0) :
    (D.sum fun _ n => n) + ∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩) = 0 := by
  classical
  set g : Fbar := C.residue ⟨c • f, hc⟩ with hg
  obtain ⟨E, hE, hdegE⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) g hres
  set Nd : Divisor (ResidueField A) Fbar := ∑ x ∈ C.nodes, Finsupp.single x (x.ord g) with hN
  have hN_apply : ∀ y, Nd y = if y ∈ C.nodes then y.ord g else 0 := by
    intro y
    rw [hN, Finsupp.finsetSum_apply]
    split_ifs with hy
    · rw [Finset.sum_eq_single y (fun x _ hxy => by rw [Finsupp.single_apply, if_neg hxy])
        (fun h => (h hy).elim), Finsupp.single_eq_same]
    · exact Finset.sum_eq_zero fun x hx => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hy hx
  have hEeq : E = Finsupp.mapDomain C.placeMap D + Nd := by
    ext y
    rw [Finsupp.add_apply, hN_apply, hE y]
    by_cases hy : y ∈ C.nodes
    · rw [if_pos hy, mapDomain_eq_zero_of_mem_nodes C D hDoff y hy, zero_add]
    · rw [if_neg hy, mapDomain_eq_ord_of_not_mem_nodes C hc hres D hDdom hDoff y hy, add_zero]
  have hmassE : (E.sum fun _ n => n) = 0 := by
    rw [← degree_eq_sum_of_isRational E (fun v _ => hrat v)]
    exact hdegE
  have hmassN : (Nd.sum fun _ n => n) = ∑ x ∈ C.nodes, x.ord g := by
    rw [hN, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index rfl
  rw [hEeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_mapDomain, hmassN] at hmassE
  exact hmassE

theorem end_law (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    {f : F} (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    (hN : ∀ P ∈ An.dom, N P = P.ord f)
    {ca : L} (hca : ca • f ∈ Ca.integers) (hresa : Ca.residue ⟨ca • f, hca⟩ ≠ 0)
    {cb : L} (hcb : cb • f ∈ Cb.integers) (hresb : Cb.residue ⟨cb • f, hcb⟩ ≠ 0) :
    (N.sum fun _ k => k) = xa.ord (Ca.residue ⟨ca • f, hca⟩) + xb.ord (Cb.residue ⟨cb • f, hcb⟩) ∧
    (N.prod fun P k => A.valuation (P.evalAt An.param) ^ k) =
      A.valuation ca * (A.valuation cb)⁻¹ * A.valuation (An.modulus : L) ^ (xb.ord (Cb.residue ⟨cb • f, hcb⟩)) := by
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₁
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hca0 : ca ≠ 0 := const_ne_zero Ca hca hresa
  have hcb0 : cb ≠ 0 := const_ne_zero Cb hcb hresb
  have hf0 : f ≠ 0 := fun_ne_zero Ca hca hresa
  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, Hb⟩ := hatt'
  obtain ⟨hzb, hxb, hslb⟩ := transfer_end Cb.residue xb hdom hp' Hb
  set c' : L := ca * cb⁻¹ with hc'
  have hc'0 : c' ≠ 0 := mul_ne_zero hca0 (inv_ne_zero hcb0)
  have hh0 : ca • f ≠ 0 := smul_ne_zero hca0 hf0
  have heq : (algebraMap L F c')⁻¹ * (ca • f) = cb • f := by
    have hca' : algebraMap L F ca ≠ 0 := (map_ne_zero _).mpr hca0
    rw [hc', Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀]
    field_simp
  have hhb : (algebraMap L F c')⁻¹ * (ca • f) ∈ Cb.integers := heq ▸ hcb
  have hsub : (⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ : Cb.integers) = ⟨cb • f, hcb⟩ :=
    Subtype.ext heq
  have hresb' : Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ ≠ 0 := by rw [hsub]; exact hresb
  have hordh : ∀ P ∈ An.dom, N P = P.ord (ca • f) := fun P hP => by
    rw [ord_smul P hca0 hf0]; exact hN P hP
  obtain ⟨hmass, hprod⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (rp Ca) xa hza hxa hsla (rp Cb) xb hzb hxb hslb ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩
      (ca • f) hh0 hca hresa c' hc'0 hhb hresb' N hNdom hordh
  have hordb : xb.ord ((rp Cb).residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) =
      xb.ord (Cb.residue ⟨cb • f, hcb⟩) := by
    show xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) = _
    rw [hsub]
  rw [hordb] at hmass hprod
  refine ⟨hmass, ?_⟩
  rw [hprod, hc', map_mul, map_inv₀]

end General

end SlopeLawEngine

open SlopeLawEngine in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
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
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (f : F) (hf : f ≠ 0)
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hDi : ∀ i, ∀ P ∈ (C i).dom, Di i P = P.ord f)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hN : ∀ e, ∀ P ∈ (An e).dom, N e P = P.ord f)
    :
    ∃ (σ : Fin m → ℤ) (a : Fin n → L), (∀ i, a i ≠ 0) ∧
      (∀ i : Fin n, Divisor.degree (Di i) + (∑ e, if src e = i then σ e else 0) +
          (∑ e, if tgt e = i then ((N e).sum fun _ k => k) - σ e else 0) = 0) ∧
      (∀ e : Fin m, A.valuation (a (src e)) * ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
          A.valuation (a (tgt e)) * A.valuation ((An e).modulus : L) ^ (((N e).sum fun _ k => k) - σ e)) := by
  classical

  choose c hc hres using fun i => (C i).exists_smul_mem f hf
  have hDoff : ∀ i P, P ∉ (C i).dom → Di i P = 0 := fun i P hP => by
    by_contra h
    exact hP (hdom i P (Finsupp.mem_support_iff.mpr h))
  have hmod0 : ∀ e, ((An e).modulus : L) ≠ 0 := fun e => (hpair e).2.2.1
  have hc0 : ∀ i, c i ≠ 0 := fun i => const_ne_zero (C i) (hc i) (hres i)
  set g : ∀ i, Fbar i := fun i => (C i).residue ⟨c i • f, hc i⟩ with hg

  have hedge : ∀ e, ((N e).sum fun _ k => k) = (xs e).ord (g (src e)) + (xt e).ord (g (tgt e)) ∧
      ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
        A.valuation (c (src e)) * (A.valuation (c (tgt e)))⁻¹ *
          A.valuation ((An e).modulus : L) ^ ((xt e).ord (g (tgt e))) := fun e =>
    end_law (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e) (C (src e)) (xs e) (hatt e).1
      (C (tgt e)) (xt e) (hatt e).2 (wide_of_isAlgClosed (An e) (hmod0 e)) (N e) (hNdom e) (hN e)
      (hc (src e)) (hres (src e)) (hc (tgt e)) (hres (tgt e))

  have hvert : ∀ i, ((Di i).sum fun _ n => n) + ∑ x ∈ (C i).nodes, x.ord (g i) = 0 := fun i =>
    sum_nodes_ord_add_sum_eq_zero (hratBar i) (C i) (hc i) (hres i) (Di i) (hDi i) (hDoff i)

  have hnodesum : ∀ (φ : ∀ j, Place (IsLocalRing.ResidueField A) (Fbar j) → ℤ) (i : Fin n),
      ∑ x ∈ (C i).nodes, φ i x =
        (∑ e ∈ Finset.univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
          ∑ e ∈ Finset.univ.filter (fun e => src e = i), φ (src e) (xs e) :=
    sum_nodes_eq_sum_ends (fun i => (C i).nodes) src tgt xs xt (fun e => (hatt e).1.1)
      (fun e => (hatt e).2.1) hnodes.1 hnodes.2
  refine ⟨fun e => (xs e).ord (g (src e)), fun i => (c i)⁻¹, fun i => inv_ne_zero (hc0 i), ?_, ?_⟩
  ·
    intro i
    have h := hvert i
    rw [hnodesum (fun j x => x.ord (g j)) i, Finset.sum_filter, Finset.sum_filter] at h
    rw [degree_eq_sum_of_isRational (Di i) (fun P hP => hratF i P (hdom i P hP))]
    have htgt : (∑ e, if tgt e = i then ((N e).sum fun _ k => k) - (xs e).ord (g (src e)) else 0) =
        ∑ e, if tgt e = i then (xt e).ord (g (tgt e)) else 0 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs
      · rw [(hedge e).1]; ring
      · rfl
    rw [htgt]
    linarith
  ·
    intro e
    obtain ⟨hmass, hprod⟩ := hedge e
    have hva : A.valuation (c (src e)) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc0 _)
    have hvb : A.valuation (c (tgt e)) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc0 _)
    rw [map_inv₀, map_inv₀, hprod, show ((N e).sum fun _ k => k) - (xs e).ord (g (src e)) = (xt e).ord (g (tgt e)) from
      by rw [hmass]; ring]
    field_simp

end S_AlgebraicCurve_exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne (solution)
