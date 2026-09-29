-- Prove2me | solution 1 for AlgebraicCurve.Place.eq_of_comap_toValuationSubring_eq_of_isRational
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0f63a886-87e4-557a-ac4d-b689924dffe7

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational
set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace RationalPlaceDescent

section OrdToolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

private theorem mem_iff_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨ord_nonneg_of_mem v, mem_of_ord_nonneg v hf⟩

private theorem exists_isUnit_of_ord_eq_zero (v : Place K F) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

private theorem ord_pos_of_residue_eq_zero (v : Place K F) {f : F} (hf : f ≠ 0) (hm : f ∈ v.toValuationSubring)
    (hres : IsLocalRing.residue v.toValuationSubring ⟨f, hm⟩ = 0) : 0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hm).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := exists_isUnit_of_ord_eq_zero v hf heq.symm
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu hres

private theorem ord_eq_zero_of_residue_ne_zero (v : Place K F) {f : F} (hm : f ∈ v.toValuationSubring)
    (hres : IsLocalRing.residue v.toValuationSubring ⟨f, hm⟩ ≠ 0) : v.ord f = 0 := by
  have h0 := v.ord_coe_unit ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hres).unit
  rwa [IsUnit.unit_spec] at h0

private theorem ord_pow (v : Place K F) {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => simp [v.ord_one]
  | succ m ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero m hf) hf, ih]
    push_cast
    ring

end OrdToolkit

section RegionF

private theorem mul_mem_span_range_of_mem {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra F F'] (V : Place K F) :
    ∀ x ∈ Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F))),
      ∀ y ∈ Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F))),
        x * y ∈ Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F))) := by
  intro x hx y hy
  have hxy := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at hxy
  refine Submodule.span_mono ?_ hxy
  rintro _ ⟨_, ⟨f, rfl⟩, _, ⟨g, rfl⟩, rfl⟩
  exact ⟨f * g, by simp⟩

private theorem exists_mem_span_div {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra F F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) (V : Place K F) (g : F') :
    ∃ b ∈ Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F))),
      ∃ b' ∈ Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F))),
        b' ≠ 0 ∧ g = b / b' := by
  have hmul := mul_mem_span_range_of_mem (K' := K') (F' := F') V
  have h1S : (1 : F') ∈
      Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F))) :=
    Submodule.subset_span ⟨1, by simp⟩
  have hg : g ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]
    exact IntermediateField.mem_top
  change g ∈ Subfield.closure (Set.range (algebraMap K' F') ∪ Set.range (algebraMap F F')) at hg
  induction hg using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨f, rfl⟩
      · refine ⟨algebraMap K' F' c, ?_, 1, h1S, one_ne_zero, (div_one _).symm⟩
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ c h1S
      · by_cases hf : f ∈ V.toValuationSubring
        · exact ⟨algebraMap F F' f, Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩, 1, h1S, one_ne_zero,
            (div_one _).symm⟩
        · have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ zero_mem _)
          have hfi : f⁻¹ ∈ V.toValuationSubring := (V.toValuationSubring.mem_or_inv_mem f).resolve_left hf
          refine ⟨1, h1S, algebraMap F F' f⁻¹, Submodule.subset_span ⟨⟨f⁻¹, hfi⟩, rfl⟩,
            (map_ne_zero (algebraMap F F')).mpr (inv_ne_zero hf0), ?_⟩
          rw [map_inv₀, one_div, inv_inv]
  | one => exact ⟨1, h1S, 1, h1S, one_ne_zero, (div_one 1).symm⟩
  | add x y _ _ hx hy =>
      obtain ⟨b, hb, b', hb', hb'0, rfl⟩ := hx
      obtain ⟨c, hc, c', hc', hc'0, rfl⟩ := hy
      exact ⟨b * c' + b' * c, add_mem (hmul b hb c' hc') (hmul b' hb' c hc), b' * c', hmul b' hb' c' hc',
        mul_ne_zero hb'0 hc'0, div_add_div b c hb'0 hc'0⟩
  | neg x _ hx =>
      obtain ⟨b, hb, b', hb', hb'0, rfl⟩ := hx
      exact ⟨-b, neg_mem hb, b', hb', hb'0, by ring⟩
  | inv x _ hx =>
      obtain ⟨b, hb, b', hb', hb'0, rfl⟩ := hx
      by_cases hb0 : b = 0
      · subst hb0
        exact ⟨0, zero_mem _, 1, h1S, one_ne_zero, by simp⟩
      · exact ⟨b', hb', b, hb, hb0, by rw [inv_div]⟩
  | mul x y _ _ hx hy =>
      obtain ⟨b, hb, b', hb', hb'0, rfl⟩ := hx
      obtain ⟨c, hc, c', hc', hc'0, rfl⟩ := hy
      exact ⟨b * c, hmul b hb c hc, b' * c', hmul b' hb' c' hc', mul_ne_zero hb'0 hc'0,
        by rw [div_mul_div_comm]⟩

end RegionF

section Descent

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra K K']
  [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

variable (K') in

private abbrev spanV (V : Place K F) : Submodule K' F' :=
  Submodule.span K' (Set.range (fun f : V.toValuationSubring => algebraMap F F' (f : F)))

private theorem exists_eq_algebraMap_add_mul (V : Place K F) (hV : V.IsRational) {π : V.toValuationSubring}
    (hπ : Irreducible π) {f : F} (hf : f ∈ V.toValuationSubring) :
    ∃ a : K, ∃ g ∈ V.toValuationSubring, f = algebraMap K F a + (π : F) * g := by
  obtain ⟨a, ha⟩ := hV (IsLocalRing.residue V.toValuationSubring ⟨f, hf⟩)
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  by_cases hd : f - algebraMap K F a = 0
  · refine ⟨a, 0, zero_mem _, ?_⟩
    rw [mul_zero, add_zero]
    exact (sub_eq_zero.mp hd).symm ▸ rfl
  · refine ⟨a, (f - algebraMap K F a) * (π : F)⁻¹, ?_, ?_⟩
    · have hdm : f - algebraMap K F a ∈ V.toValuationSubring := sub_mem hf (V.algebraMap_mem' a)
      have hres : IsLocalRing.residue V.toValuationSubring ⟨f - algebraMap K F a, hdm⟩ = 0 := by
        have hsplit : (⟨f - algebraMap K F a, hdm⟩ : V.toValuationSubring)
            = ⟨f, hf⟩ - algebraMap K V.toValuationSubring a := rfl
        rw [hsplit, map_sub, ← ha, IsScalarTower.algebraMap_apply K V.toValuationSubring V.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq, sub_self]
      have hpos : 0 < V.ord (f - algebraMap K F a) := ord_pos_of_residue_eq_zero V hd hdm hres
      rw [mem_iff_ord_nonneg V (mul_ne_zero hd (inv_ne_zero hπ0)), V.ord_mul hd (inv_ne_zero hπ0),
        Place.ord_inv, V.ord_coe_irreducible hπ]
      omega
    · rw [mul_left_comm, mul_inv_cancel₀ hπ0, mul_one]
      ring

private theorem algebraMap_algebraMap (a : K) :
    algebraMap F F' (algebraMap K F a) = algebraMap K' F' (algebraMap K K' a) := by
  rw [← IsScalarTower.algebraMap_apply K F F', IsScalarTower.algebraMap_apply K K' F']

private theorem exists_eq_algebraMap_add_mul_of_mem_spanV (V : Place K F) (hV : V.IsRational)
    {π : V.toValuationSubring} (hπ : Irreducible π) {b : F'} (hb : b ∈ spanV K' V) :
    ∃ c : K', ∃ b₁ ∈ spanV K' V, b = algebraMap K' F' c + algebraMap F F' (π : F) * b₁ := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨a, g, hg, hfg⟩ := exists_eq_algebraMap_add_mul V hV hπ f.2
    refine ⟨algebraMap K K' a, algebraMap F F' g, Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    simp only
    rw [hfg, map_add, map_mul, algebraMap_algebraMap (K' := K') a]
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨c, b₁, hb₁, rfl⟩ := ihx
    obtain ⟨d, b₂, hb₂, rfl⟩ := ihy
    refine ⟨c + d, b₁ + b₂, add_mem hb₁ hb₂, ?_⟩
    rw [map_add, mul_add]
    ring
  | smul r x _ ih =>
    obtain ⟨c, b₁, hb₁, rfl⟩ := ih
    refine ⟨r * c, r • b₁, Submodule.smul_mem _ r hb₁, ?_⟩
    simp only [smul_add, map_mul, Algebra.smul_def]
    ring

private theorem mem_of_mem_spanV (V : Place K F) (v : Place K' F')
    (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring) {b : F'} (hb : b ∈ spanV K' V) :
    b ∈ v.toValuationSubring := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    have hf : (f : F) ∈ v.toValuationSubring.comap (algebraMap F F') := by
      rw [hv]
      exact f.2
    exact (ValuationSubring.mem_comap).mp hf
  | zero => exact zero_mem _
  | add x y _ _ ihx ihy => exact add_mem ihx ihy
  | smul r x _ ih =>
    rw [Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' r) ih

private theorem ord_algebraMap_pos (V : Place K F) {π : V.toValuationSubring} (hπ : Irreducible π)
    (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring) :
    0 < v.ord (algebraMap F F' (π : F)) := by
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hinv : (π : F)⁻¹ ∉ V.toValuationSubring := by
    rw [mem_iff_ord_nonneg V (inv_ne_zero hπ0), Place.ord_inv, V.ord_coe_irreducible hπ]
    omega
  have hinv' : (algebraMap F F' (π : F))⁻¹ ∉ v.toValuationSubring := by
    intro h
    apply hinv
    have h2 : (π : F)⁻¹ ∈ v.toValuationSubring.comap (algebraMap F F') := by
      rw [ValuationSubring.mem_comap, map_inv₀]
      exact h
    rw [hv] at h2
    exact h2
  rw [mem_iff_ord_nonneg v (inv_ne_zero ((map_ne_zero _).mpr hπ0)), Place.ord_inv] at hinv'
  omega

private theorem unit_shape_mem (V : Place K F) {π : V.toValuationSubring} (hπ : Irreducible π)
    (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    (c : K') {b₁ : F'} (hb₁ : b₁ ∈ spanV K' V) :
    algebraMap K' F' c + algebraMap F F' (π : F) * b₁ ∈ v.toValuationSubring := by
  have hπ0 : algebraMap F F' (π : F) ≠ 0 :=
    (map_ne_zero _).mpr (by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero)
  exact add_mem (v.algebraMap_mem' c)
    (mul_mem (mem_of_ord_nonneg v hπ0 (ord_algebraMap_pos V hπ v hv).le) (mem_of_mem_spanV V v hv hb₁))

private theorem residue_unit_shape_ne_zero (V : Place K F) {π : V.toValuationSubring} (hπ : Irreducible π)
    (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    {c : K'} (hc : c ≠ 0) {b₁ : F'} (hb₁ : b₁ ∈ spanV K' V)
    (hm : algebraMap K' F' c + algebraMap F F' (π : F) * b₁ ∈ v.toValuationSubring) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K' F' c + algebraMap F F' (π : F) * b₁, hm⟩ ≠ 0 := by
  have hπ0 : algebraMap F F' (π : F) ≠ 0 :=
    (map_ne_zero _).mpr (by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero)
  have hm₁ : algebraMap F F' (π : F) * b₁ ∈ v.toValuationSubring :=
    mul_mem (mem_of_ord_nonneg v hπ0 (ord_algebraMap_pos V hπ v hv).le) (mem_of_mem_spanV V v hv hb₁)
  have hsplit : (⟨algebraMap K' F' c + algebraMap F F' (π : F) * b₁, hm⟩ : v.toValuationSubring)
      = algebraMap K' v.toValuationSubring c + ⟨algebraMap F F' (π : F) * b₁, hm₁⟩ := rfl
  have hres₁ : IsLocalRing.residue v.toValuationSubring ⟨algebraMap F F' (π : F) * b₁, hm₁⟩ = 0 := by
    by_contra hne
    have h0 := ord_eq_zero_of_residue_ne_zero v hm₁ hne
    have h1 := ord_algebraMap_pos V hπ v hv
    rcases eq_or_ne b₁ 0 with rfl | hb₁0
    · rw [mul_zero] at h0

      exact hne (by
        have hz : (⟨algebraMap F F' (π : F) * 0, hm₁⟩ : v.toValuationSubring) = 0 := Subtype.ext (mul_zero _)
        rw [hz, map_zero])
    · rw [v.ord_mul hπ0 hb₁0] at h0
      have h2 := ord_nonneg_of_mem v (mem_of_mem_spanV V v hv hb₁)
      omega
  rw [hsplit, map_add, hres₁, add_zero]
  intro h0
  have hmem := (IsLocalRing.residue_eq_zero_iff _).mp h0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
  exact hmem ((algebraMap K' v.toValuationSubring).isUnit_map (isUnit_iff_ne_zero.mpr hc))

private theorem ord_unit_shape_eq_zero (V : Place K F) {π : V.toValuationSubring} (hπ : Irreducible π)
    (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    {c : K'} (hc : c ≠ 0) {b₁ : F'} (hb₁ : b₁ ∈ spanV K' V) :
    v.ord (algebraMap K' F' c + algebraMap F F' (π : F) * b₁) = 0 :=
  ord_eq_zero_of_residue_ne_zero v (unit_shape_mem V hπ v hv c hb₁)
    (residue_unit_shape_ne_zero V hπ v hv hc hb₁ _)

private theorem unit_shape_ne_zero (V : Place K F) {π : V.toValuationSubring} (hπ : Irreducible π)
    (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    {c : K'} (hc : c ≠ 0) {b₁ : F'} (hb₁ : b₁ ∈ spanV K' V) :
    algebraMap K' F' c + algebraMap F F' (π : F) * b₁ ≠ 0 := by
  intro h0
  apply residue_unit_shape_ne_zero V hπ v hv hc hb₁ (unit_shape_mem V hπ v hv c hb₁)
  have hz : (⟨algebraMap K' F' c + algebraMap F F' (π : F) * b₁, unit_shape_mem V hπ v hv c hb₁⟩ :
      v.toValuationSubring) = 0 := Subtype.ext h0
  rw [hz, map_zero]

private theorem exists_pow_mul_of_mem_spanV (V : Place K F) (hV : V.IsRational) {π : V.toValuationSubring}
    (hπ : Irreducible π) (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    {b : F'} (hb : b ∈ spanV K' V) (hb0 : b ≠ 0) :
    ∃ n : ℕ, ∃ c : K', c ≠ 0 ∧ ∃ b₁ ∈ spanV K' V,
      b = algebraMap F F' (π : F) ^ n * (algebraMap K' F' c + algebraMap F F' (π : F) * b₁) := by
  have hπ0 : algebraMap F F' (π : F) ≠ 0 :=
    (map_ne_zero _).mpr (by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero)
  have hπpos := ord_algebraMap_pos V hπ v hv
  suffices H : ∀ m : ℕ, ∀ b : F', b ∈ spanV K' V → b ≠ 0 → (v.ord b).toNat = m →
      ∃ n : ℕ, ∃ c : K', c ≠ 0 ∧ ∃ b₁ ∈ spanV K' V,
        b = algebraMap F F' (π : F) ^ n * (algebraMap K' F' c + algebraMap F F' (π : F) * b₁) from
    H _ b hb hb0 rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro b hb hb0 hm
    obtain ⟨c, b₁, hb₁, rfl⟩ := exists_eq_algebraMap_add_mul_of_mem_spanV V hV hπ hb
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, zero_add] at hb0 hm
      have hb₁0 : b₁ ≠ 0 := by
        rintro rfl
        exact hb0 (mul_zero _)
      have hb₁nn := ord_nonneg_of_mem v (mem_of_mem_spanV V v hv hb₁)
      have hlt : (v.ord b₁).toNat < m := by
        rw [← hm, v.ord_mul hπ0 hb₁0]
        omega
      obtain ⟨n, d, hd, b₂, hb₂, hb₁eq⟩ := ih _ hlt b₁ hb₁ hb₁0 rfl
      refine ⟨n + 1, d, hd, b₂, hb₂, ?_⟩
      rw [map_zero, zero_add, hb₁eq, pow_succ]
      ring
    · exact ⟨0, c, hc, b₁, hb₁, by rw [pow_zero, one_mul]⟩

private theorem ord_pow_mul_unit_shape (V : Place K F) {π : V.toValuationSubring} (hπ : Irreducible π)
    (v : Place K' F') (hv : v.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    (n : ℕ) {c : K'} (hc : c ≠ 0) {b₁ : F'} (hb₁ : b₁ ∈ spanV K' V) :
    v.ord (algebraMap F F' (π : F) ^ n * (algebraMap K' F' c + algebraMap F F' (π : F) * b₁))
      = n * v.ord (algebraMap F F' (π : F)) := by
  have hπ0 : algebraMap F F' (π : F) ≠ 0 :=
    (map_ne_zero _).mpr (by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero)
  rw [v.ord_mul (pow_ne_zero n hπ0) (unit_shape_ne_zero V hπ v hv hc hb₁), ord_pow v hπ0,
    ord_unit_shape_eq_zero V hπ v hv hc hb₁, add_zero]

end Descent

end RationalPlaceDescent

open RationalPlaceDescent in
theorem solution
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra K K']
    [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (V : Place K F) (hV : V.IsRational) (w w' : Place K' F')
    (hw : w.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    (hw' : w'.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring) :
    w = w' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V.toValuationSubring
  have hπ0 : algebraMap F F' (π : F) ≠ 0 :=
    (map_ne_zero _).mpr (by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero)
  have hew := ord_algebraMap_pos V hπ w hw
  have hew' := ord_algebraMap_pos V hπ w' hw'
  have hsign : ∀ (n n' : ℕ) (e : ℤ), 0 < e → (0 ≤ (n : ℤ) * e - (n' : ℤ) * e ↔ (n' : ℤ) ≤ n) := by
    intro n n' e he
    rw [← sub_mul, mul_nonneg_iff_of_pos_right he, sub_nonneg]
  have key : ∀ g : F', g ∈ w.toValuationSubring ↔ g ∈ w'.toValuationSubring := by
    intro g
    rcases eq_or_ne g 0 with rfl | hg0
    · exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    obtain ⟨b, hb, b', hb', hb'0, rfl⟩ := exists_mem_span_div hgen V g
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (zero_div _)
    obtain ⟨n, c, hc, b₁, hb₁, rfl⟩ := exists_pow_mul_of_mem_spanV V hV hπ w hw hb hb0
    obtain ⟨n', c', hc', b₁', hb₁', rfl⟩ := exists_pow_mul_of_mem_spanV V hV hπ w hw hb' hb'0
    have hnum : algebraMap F F' (π : F) ^ n * (algebraMap K' F' c + algebraMap F F' (π : F) * b₁) ≠ 0 :=
      mul_ne_zero (pow_ne_zero n hπ0) (unit_shape_ne_zero V hπ w hw hc hb₁)
    have hden : algebraMap F F' (π : F) ^ n' * (algebraMap K' F' c' + algebraMap F F' (π : F) * b₁') ≠ 0 :=
      mul_ne_zero (pow_ne_zero n' hπ0) (unit_shape_ne_zero V hπ w hw hc' hb₁')
    rw [mem_iff_ord_nonneg w hg0, mem_iff_ord_nonneg w' hg0, div_eq_mul_inv,
      w.ord_mul hnum (inv_ne_zero hden), w'.ord_mul hnum (inv_ne_zero hden), Place.ord_inv, Place.ord_inv,
      ord_pow_mul_unit_shape V hπ w hw n hc hb₁, ord_pow_mul_unit_shape V hπ w hw n' hc' hb₁',
      ord_pow_mul_unit_shape V hπ w' hw' n hc hb₁, ord_pow_mul_unit_shape V hπ w' hw' n' hc' hb₁',
      ← sub_eq_add_neg, ← sub_eq_add_neg, hsign n n' _ hew, hsign n n' _ hew']
  exact Place.ext (SetLike.ext key)

end

end S_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational
end P2MW
export P2MW.S_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational (solution)
