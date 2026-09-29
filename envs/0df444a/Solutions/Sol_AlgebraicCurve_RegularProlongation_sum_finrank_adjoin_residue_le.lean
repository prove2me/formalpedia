-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bcf9b2c2-5574-549f-bbf8-c9f4c90b9932

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero smul_const_ne_zero integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem mk ker_residue residue mk.injEq"
namespace W7XK3FI
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

section single

variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem residue_eq_zero_of_mem_nonunits (R : RegularProlongation A F Fbar) {w : F}
    (hw : w ∈ R.integers) (hn : w ∈ R.integers.nonunits) : R.residue ⟨w, hw⟩ = 0 := by
  have h1 : (⟨w, hw⟩ : R.integers) ∈ maximalIdeal R.integers :=
    (R.integers.valuation_lt_one_iff ⟨w, hw⟩).mpr ((R.integers.mem_nonunits_iff).mp hn)
  rw [← R.ker_residue] at h1
  exact h1

theorem integers_eq_of_le {Fbar' : Type*} [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (R₁ : RegularProlongation A F Fbar) (R₂ : RegularProlongation A F Fbar')
    (h : R₁.integers ≤ R₂.integers) : R₁.integers = R₂.integers := by
  refine le_antisymm h fun y hy₂ => ?_
  by_contra hy₁
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy₁ (zero_mem _)
  obtain ⟨c, hcy, hres⟩ := R₁.exists_smul_mem y hy0
  have hc0 : c ≠ 0 := R₁.smul_const_ne_zero hcy hres
  set v₁ := R₁.integers.valuation with hv₁
  set v₂ := R₂.integers.valuation with hv₂
  set cF : F := algebraMap L F c with hcF
  have hcF0 : cF ≠ 0 := by
    rw [hcF]; exact (map_ne_zero (algebraMap L F)).mpr hc0
  have hcy' : c • y = cF * y := Algebra.smul_def c y

  have hu : IsUnit (⟨c • y, hcy⟩ : R₁.integers) := R₁.isUnit_of_residue_ne_zero hres
  have h1 : v₁ (cF * y) = 1 := by
    have h' : v₁ (c • y) = 1 := (R₁.integers.valuation_eq_one_iff ⟨c • y, hcy⟩).mp hu
    rwa [hcy'] at h'

  have hy1 : 1 < v₁ y := by
    rw [← not_le]
    intro hle
    exact hy₁ ((R₁.integers.valuation_le_one_iff y).mp hle)

  have hc1 : v₁ cF < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have h' : 1 * v₁ y ≤ v₁ cF * v₁ y := mul_le_mul' hge le_rfl
    rw [one_mul, ← map_mul, h1] at h'
    exact (not_le.mpr hy1) h'

  have hcA : c ∈ A :=
    (R₁.algebraMap_mem_iff c).mp ((R₁.integers.valuation_le_one_iff cF).mp hc1.le)
  have hcinv : c⁻¹ ∉ A := by
    intro hinv
    have hmem : cF⁻¹ ∈ R₁.integers := by
      have := (R₁.algebraMap_mem_iff c⁻¹).mpr hinv
      rwa [map_inv₀] at this
    have hle : v₁ cF⁻¹ ≤ 1 := (R₁.integers.valuation_le_one_iff _).mpr hmem
    have h' : v₁ cF⁻¹ * v₁ cF ≤ 1 * v₁ cF := mul_le_mul' hle le_rfl
    rw [← map_mul, inv_mul_cancel₀ hcF0, map_one, one_mul] at h'
    exact (not_lt.mpr h') hc1

  have hcF2 : v₂ cF ≤ 1 :=
    (R₂.integers.valuation_le_one_iff cF).mpr ((R₂.algebraMap_mem_iff c).mpr hcA)
  have hy2 : v₂ y ≤ 1 := (R₂.integers.valuation_le_one_iff y).mpr hy₂
  have hinv1 : (cF * y)⁻¹ ∈ R₁.integers := by
    rw [← R₁.integers.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have hinv2 : v₂ (cF * y)⁻¹ ≤ 1 := (R₂.integers.valuation_le_one_iff _).mpr (h hinv1)
  have hcy0 : cF * y ≠ 0 := mul_ne_zero hcF0 hy0

  have hc2 : v₂ cF = 1 := by
    refine le_antisymm hcF2 ?_
    by_contra hlt
    rw [not_le] at hlt
    have hprod : v₂ (cF * y) < 1 := by
      rw [map_mul]
      calc v₂ cF * v₂ y ≤ v₂ cF * 1 := mul_le_mul' le_rfl hy2
        _ = v₂ cF := mul_one _
        _ < 1 := hlt
    have h' : v₂ (cF * y)⁻¹ * v₂ (cF * y) ≤ 1 * v₂ (cF * y) := mul_le_mul' hinv2 le_rfl
    rw [← map_mul, inv_mul_cancel₀ hcy0, map_one, one_mul] at h'
    exact (not_lt.mpr h') hprod

  have hmem2 : cF⁻¹ ∈ R₂.integers := by
    rw [← R₂.integers.valuation_le_one_iff, map_inv₀, hc2, inv_one]
  have : c⁻¹ ∈ A := by
    rw [← R₂.algebraMap_mem_iff, map_inv₀]
    exact hmem2
  exact hcinv this

theorem aeval_eq_linearCombination {K B : Type*} [CommRing K] [Ring B] [Algebra K B]
    (x : B) (p : Polynomial K) :
    Polynomial.aeval x p = Finsupp.linearCombination K (fun j : ℕ => x ^ j) p.toFinsupp.coeff := by
  rcases p with ⟨q⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp, Finsupp.linearCombination_apply,
    Finsupp.sum, Algebra.smul_def]

theorem linearIndependent_pow_iff_transcendental {K B : Type*} [Field K] [Ring B] [Algebra K B]
    (x : B) : LinearIndependent K (fun j : ℕ => x ^ j) ↔ Transcendental K x := by
  rw [linearIndependent_iff, transcendental_iff]
  constructor
  · intro h p hp
    have := h p.toFinsupp.coeff (by rw [← aeval_eq_linearCombination]; exact hp)
    exact Polynomial.toFinsupp_eq_zero.mp (AddMonoidAlgebra.coeff_eq_zero.mp this)
  · intro h l hl
    have := h ⟨.ofCoeff l⟩ (by rw [aeval_eq_linearCombination]; exact hl)
    exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp this)

end single

section several

variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

omit [Fintype ι] in
theorem eq_of_integers_le (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers) (i j : ι)
    (h : (R i).integers ≤ (R j).integers) : i = j :=
  hR (integers_eq_of_le (R i) (R j) h)

theorem exists_lift (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers) (i : ι) (x : Fb i) :
    ∃ z : F, ∃ hz : ∀ l, z ∈ (R l).integers,
      (R i).residue ⟨z, hz i⟩ = x ∧ ∀ l, l ≠ i → (R l).residue ⟨z, hz l⟩ = 0 := by
  classical
  obtain ⟨y, hy⟩ := (R i).residue_surjective x
  let a : ι → F := fun l => if l = i then (y : F) else 0
  have hai : a i = y := if_pos rfl
  have hal : ∀ l, l ≠ i → a l = 0 := fun l hl => if_neg hl
  have ha : ∀ l, a l ∈ (R l).integers := by
    intro l
    by_cases hl : l = i
    · rw [hl, hai]; exact y.2
    · rw [hal l hl]; exact zero_mem _
  obtain ⟨z, hz⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    (fun l => (R l).integers) (fun l l' hle => eq_of_integers_le R hR l l' hle) a ha
  refine ⟨z, fun l => (hz l).1, ?_, ?_⟩
  · have h0 := residue_eq_zero_of_mem_nonunits (R i) (sub_mem (hz i).1 (ha i)) (hz i).2
    have e : (⟨z - a i, sub_mem (hz i).1 (ha i)⟩ : (R i).integers) = ⟨z, (hz i).1⟩ - y := by
      apply Subtype.ext
      simp [hai]
    rw [e, map_sub, sub_eq_zero] at h0
    rw [h0, hy]
  · intro l hl
    have h0 := residue_eq_zero_of_mem_nonunits (R l) (sub_mem (hz l).1 (ha l)) (hz l).2
    have e : (⟨z - a l, sub_mem (hz l).1 (ha l)⟩ : (R l).integers) = ⟨z, (hz l).1⟩ := by
      apply Subtype.ext
      simp [hal l hl]
    rwa [e] at h0

theorem sum_card_le (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (s : ∀ i, Finset (Fb i))
    (hs : ∀ i, LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
      (fun x : s i => (x : Fb i))) :
    ∑ i, (s i).card ≤ Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  set k := ResidueField A
  set E := IntermediateField.adjoin L ({f} : Set F) with hE

  have h1 : ∀ i, LinearIndependent k
      (fun p : ℕ × s i => ((R i).residue ⟨f, hf i⟩) ^ p.1 * (p.2 : Fb i)) := by
    intro i
    have hgen : LinearIndependent k
        (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k ((R i).residue ⟨f, hf i⟩)) ^ j) := by
      apply LinearIndependent.of_comp
        ((IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))).val.toLinearMap)
      have : ((IntermediateField.adjoin k
            ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))).val.toLinearMap : _ → Fb i) ∘
          (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k ((R i).residue ⟨f, hf i⟩)) ^ j) =
          fun j : ℕ => ((R i).residue ⟨f, hf i⟩) ^ j := by
        funext j
        simp
      rw [this]
      exact (linearIndependent_pow_iff_transcendental _).mpr (htr i)
    have h := linearIndependent_smul hgen (hs i)
    convert h using 1
    funext p
    simp [Algebra.smul_def]

  choose z hz hzi hzl using fun τ : (Σ i, s i) => exists_lift R hR τ.1 (τ.2 : Fb τ.1)

  have h2 : LinearIndependent L (fun p : ℕ × (Σ i, s i) => f ^ p.1 * z p.2) := by
    rw [linearIndependent_iff']
    intro t g hsum
    by_contra hne
    obtain ⟨p₀, hp₀t, hgp₀⟩ := not_forall₂.mp hne
    obtain ⟨⟨j₁, i₁, x₁⟩, hp₁t, hmax⟩ :=
      t.exists_max_image (fun p => A.valuation (g p)) ⟨p₀, hp₀t⟩
    set p₁ : ℕ × (Σ i, s i) := (j₁, ⟨i₁, x₁⟩) with hp₁
    have hg₁ : g p₁ ≠ 0 := by
      intro h0
      have h := hmax p₀ hp₀t
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
      exact hgp₀ h
    have hv₁ : A.valuation (g p₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
    set c : L := (g p₁)⁻¹ with hc
    have hcA : ∀ p ∈ t, c * g p ∈ A := by
      intro p hp
      rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      calc (A.valuation (g p₁))⁻¹ * A.valuation (g p)
          ≤ (A.valuation (g p₁))⁻¹ * A.valuation (g p₁) := by gcongr; exact hmax p hp
        _ = 1 := inv_mul_cancel₀ hv₁
    have hc1 : c * g p₁ = 1 := inv_mul_cancel₀ hg₁
    let a : ℕ × (Σ i, s i) → A := fun p => if hp : p ∈ t then ⟨c * g p, hcA p hp⟩ else 0
    have ha : ∀ p ∈ t, (a p : L) = c * g p := fun p hp => by simp [a, dif_pos hp]

    let W : ℕ × (Σ i, s i) → (R i₁).integers := fun p =>
      ⟨f ^ p.1 * z p.2, mul_mem (pow_mem (hf i₁) _) (hz p.2 i₁)⟩
    have hWc : ∀ p, ((W p : (R i₁).integers) : F) = f ^ p.1 * z p.2 := fun p => rfl
    set X : (R i₁).integers := ∑ p ∈ t, constHom (R i₁) (a p) * W p with hX
    have hX0 : X = 0 := by
      apply Subtype.ext
      have : ((X : (R i₁).integers) : F) = ∑ p ∈ t, (c * g p) • (f ^ p.1 * z p.2) := by
        rw [hX]
        push_cast
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [coe_constHom, ha p hp, Algebra.smul_def, hWc]
      rw [this]
      simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
      rfl
    have hres : ∑ p ∈ t, (IsLocalRing.residue A (a p)) • (R i₁).residue (W p) = 0 := by
      have h := congrArg (R i₁).residue hX0
      rw [map_zero, hX, map_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul, residue_constHom, Algebra.smul_def]
    have hW : ∀ p, (R i₁).residue (W p) =
        ((R i₁).residue ⟨f, hf i₁⟩) ^ p.1 * (R i₁).residue ⟨z p.2, hz p.2 i₁⟩ := by
      intro p
      have e : W p = ⟨f, hf i₁⟩ ^ p.1 * ⟨z p.2, hz p.2 i₁⟩ := Subtype.ext (by simp [hWc])
      rw [e, map_mul, map_pow]

    let emb : ℕ × s i₁ → ℕ × (Σ i, s i) := fun q => (q.1, ⟨i₁, q.2⟩)
    have hemb : Function.Injective emb := by
      rintro ⟨j, x⟩ ⟨j', x'⟩ h
      simp only [emb, Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hvan : ∀ p ∈ t, p ∉ Set.range emb →
        (IsLocalRing.residue A (a p)) • (R i₁).residue (W p) = 0 := by
      rintro ⟨j, l, x⟩ _ hnot
      have hl : i₁ ≠ l := by
        intro hli
        subst hli
        exact hnot ⟨(j, x), rfl⟩
      rw [hW, hzl ⟨l, x⟩ i₁ hl, mul_zero, smul_zero]
    have hres' : ∑ q ∈ t.preimage emb hemb.injOn,
        (IsLocalRing.residue A (a (emb q))) •
          (((R i₁).residue ⟨f, hf i₁⟩) ^ q.1 * (q.2 : Fb i₁)) = 0 := by
      calc ∑ q ∈ t.preimage emb hemb.injOn, (IsLocalRing.residue A (a (emb q))) •
            (((R i₁).residue ⟨f, hf i₁⟩) ^ q.1 * (q.2 : Fb i₁))
          = ∑ q ∈ t.preimage emb hemb.injOn,
              (IsLocalRing.residue A (a (emb q))) • (R i₁).residue (W (emb q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [hW]
            exact congrArg (fun w => IsLocalRing.residue A (a (emb q)) •
              (((R i₁).residue ⟨f, hf i₁⟩) ^ q.1 * w)) (hzi ⟨i₁, q.2⟩).symm
        _ = ∑ p ∈ t, (IsLocalRing.residue A (a p)) • (R i₁).residue (W p) :=
            Finset.sum_preimage emb t hemb.injOn
              (fun p => (IsLocalRing.residue A (a p)) • (R i₁).residue (W p)) hvan
        _ = 0 := hres
    have hmem : (j₁, x₁) ∈ t.preimage emb hemb.injOn := by
      rw [Finset.mem_preimage]
      exact hp₁t
    have hall := linearIndependent_iff'.mp (h1 i₁) (t.preimage emb hemb.injOn)
      (fun q => IsLocalRing.residue A (a (emb q))) hres' (j₁, x₁) hmem
    have ha1 : a p₁ = 1 := Subtype.ext (by rw [ha p₁ hp₁t, hc1]; rfl)
    change IsLocalRing.residue A (a p₁) = 0 at hall
    rw [ha1, map_one] at hall
    exact one_ne_zero hall

  have h3 : LinearIndependent (Algebra.adjoin L ({f} : Set F)) (fun τ : (Σ i, s i) => z τ) := by
    rw [linearIndependent_iff']
    intro t g hsum
    have hg : ∀ τ, ∃ p : Polynomial L, Polynomial.aeval f p = (g τ : F) := fun τ => by
      have h : (g τ : F) ∈ (Polynomial.aeval (R := L) f).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g τ).2
      exact (AlgHom.mem_range _).1 h
    choose p hp using hg
    set N := t.sup (fun τ => (p τ).natDegree) + 1 with hN
    have hlt : ∀ τ ∈ t, (p τ).natDegree < N := fun τ hτ =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun τ => (p τ).natDegree) hτ)
    have hzero := linearIndependent_iff'.mp h2 (Finset.range N ×ˢ t)
      (fun q => (p q.2).coeff q.1) ?_
    · intro τ hτ
      have hpτ : p τ = 0 := by
        ext j
        by_cases hj : j < N
        · exact hzero (j, τ) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hτ)
        · rw [Polynomial.coeff_zero]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_lt_of_le (hlt τ hτ) (not_lt.mp hj))
      apply Subtype.ext
      rw [← hp τ, hpτ, map_zero]
      rfl
    · rw [Finset.sum_product_right, ← hsum]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [Subalgebra.smul_def, ← hp τ, Polynomial.aeval_eq_sum_range' (hlt τ hτ),
        Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul]
      exact (smul_mul_assoc _ _ _).symm
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h4 : LinearIndependent E (fun τ : (Σ i, s i) => z τ) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({f} : Set F)) E).mp h3
  have h5 := h4.fintype_card_le_finrank
  simpa using h5

theorem sum_finrank_adjoin_residue_le' (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F] :
    (∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) ∧
    ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      ≤ Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  set n := Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F with hn
  have key := sum_card_le R hR f hf htr

  have hrank : ∀ i, Module.rank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) ≤ n := by
    intro i
    apply rank_le
    intro s₀ hs₀
    set s : ∀ l, Finset (Fb l) := Function.update (fun l => (∅ : Finset (Fb l))) i s₀ with hsdef
    have hsi : s i = s₀ := by rw [hsdef, Function.update_self]
    have hsl : ∀ l, l ≠ i → s l = ∅ := fun l hl => by rw [hsdef, Function.update_of_ne hl]
    have hs : ∀ l, LinearIndependent (IntermediateField.adjoin (ResidueField A)
        ({(R l).residue ⟨f, hf l⟩} : Set (Fb l))) (fun x : s l => (x : Fb l)) := by
      intro l
      by_cases hl : l = i
      · subst hl
        rw [hsi]
        exact hs₀
      · rw [hsl l hl]
        exact linearIndependent_empty_type
    calc s₀.card = (s i).card := by rw [hsi]
      _ ≤ ∑ l, (s l).card :=
          Finset.single_le_sum (f := fun l => (s l).card) (fun l _ => Nat.zero_le _)
            (Finset.mem_univ i)
      _ ≤ n := key s hs
  haveI hfin : ∀ i, Module.Finite (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := fun i =>
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (hrank i) (Cardinal.natCast_lt_aleph0))
  refine ⟨hfin, ?_⟩

  let b : ∀ i, Module.Basis (Fin (Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i))) (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := fun i => Module.finBasis _ _
  let s : ∀ i, Finset (Fb i) := fun i => Finset.univ.image (b i)
  have hcard : ∀ i, (s i).card = Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := fun i => by
    simp only [s]
    rw [Finset.card_image_of_injective _ (b i).injective, Finset.card_univ, Fintype.card_fin]
  have hs : ∀ i, LinearIndependent (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (fun x : s i => (x : Fb i)) := fun i => by
    have h := (b i).linearIndependent.linearIndepOn_id
    have e : Set.range (b i) = (s i : Set (Fb i)) := by
      simp [s]
    rw [e] at h
    exact h
  calc ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
          ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
        = ∑ i, (s i).card := by simp_rw [hcard]
    _ ≤ n := key s hs

end several

end AlgebraicCurve.RegularProlongation.W7XK3FI
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve.RegularProlongation.W7XK3FI"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le.AlgebraicCurve"

open AlgebraicCurve.RegularProlongation.W7XK3FI in
theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F] :
    (∀ i, FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) ∧
    ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      ≤ Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F :=
  sum_finrank_adjoin_residue_le' R hR f hf htr

end S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le (solution)
