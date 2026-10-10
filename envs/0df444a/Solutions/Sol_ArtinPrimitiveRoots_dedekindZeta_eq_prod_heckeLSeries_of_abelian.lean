-- Prove2me | solution 1 for ArtinPrimitiveRoots.dedekindZeta_eq_prod_heckeLSeries_of_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T09:13:02.509882+00:00
-- url     : https://prove2.me/submissions/099746ff-106c-4494-b02f-4fa88261d342

import Mathlib
import Definitions.Def_ArtinHecke
import Theorems.Thm_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
import Theorems.Thm_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0

section
set_option autoImplicit false
set_option linter.style.haveILetI false

open NumberField

namespace ABA

theorem card_absNorm_eq_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K₁) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 K₂) // Ideal.absNorm I = n} := by
  set f : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K₁), Ideal.absNorm (I.map f) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm
  have h1 : ∀ I : Ideal (𝓞 K₁), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 K₂), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map f, by rw [hnorm]; exact I.2⟩
      invFun := fun J => ⟨J.1.map f.symm, by rw [← hnorm, h2]; exact J.2⟩
      left_inv := fun I => Subtype.ext (h1 I.1)
      right_inv := fun J => Subtype.ext (h2 J.1) }

theorem dedekindZeta_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) : dedekindZeta K₁ = dedekindZeta K₂ := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [card_absNorm_eq_congr e n]


/-- `ℚ̄` is an algebraic closure of `ℚ` for the `ℚ`-algebra structure that elaboration picks
(`DivisionRing.toRatAlgebra`). -/
theorem isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have h : (AlgebraicClosure.instAlgebra ℚ (R := ℚ)) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have i : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  rw [h] at i
  exact ⟨inferInstance, i⟩

/-- If `M/ℚ` is finite Galois and `ψ : L →ₐ[ℚ] M`, then `ζ` of the fixed field of the fixing
subgroup of `ψ(L)` is `ζ_L`. -/
theorem dedekindZeta_fixedField_fixingSubgroup_fieldRange {L M : Type} [Field L] [NumberField L]
    [Field M] [NumberField M] [IsGalois ℚ M] (ψ : L →ₐ[ℚ] M) :
    dedekindZeta (IntermediateField.fixedField ψ.fieldRange.fixingSubgroup) =
      dedekindZeta L := by
  have h := IsGalois.fixedField_fixingSubgroup ψ.fieldRange
  rw [dedekindZeta_congr (IntermediateField.equivOfEq h).toRingEquiv]
  exact (dedekindZeta_congr (AlgEquiv.ofInjectiveField ψ).toRingEquiv).symm

end ABA
end

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.style.haveILetI false

open NumberField

namespace ABP

open scoped Classical

/-- An additive character of `Additive C` as a multiplicative character `C →* ℂˣ`. -/
noncomputable def charOf {C : Type*} [Group C] (ψ : AddChar (Additive C) ℂ) : C →* ℂˣ where
  toFun c := ⟨ψ (Additive.ofMul c), ψ (Additive.ofMul c⁻¹),
    by rw [← AddChar.map_add_eq_mul, ← ofMul_mul, mul_inv_cancel]; simp,
    by rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel]; simp⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [ofMul_mul, AddChar.map_add_eq_mul]

/-- `Ind(J, χ)(g)` by Frobenius' formula, as in 63e4cbfd. -/
noncomputable def ind {G : Type*} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ)
    (g : G) : ℂ :=
  (Nat.card J : ℂ)⁻¹ * ∑ x : G,
    if hx : x⁻¹ * g * x ∈ J then ((χ ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0

theorem pointwise {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) (hHK : H ≤ K)
    {A : Type*} [CommGroup A] [Fintype A] (π : K →* A) (hπ : ∀ k : K, π k = 1 ↔ (k : G) ∈ H)
    (hcard : (Nat.card K : ℂ) = Fintype.card A * Nat.card H) (y : G) :
    ∑ ψ : AddChar (Additive A) ℂ, (Nat.card K : ℂ)⁻¹ *
        (if hy : y ∈ K then (((charOf ψ).comp π ⟨y, hy⟩ : ℂˣ) : ℂ) else 0) =
      (Nat.card H : ℂ)⁻¹ * (if hy : y ∈ H then (((1 : H →* ℂˣ) ⟨y, hy⟩ : ℂˣ) : ℂ) else 0) := by
  have hA : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  by_cases hy : y ∈ K
  · simp only [dif_pos hy, ← Finset.mul_sum]
    have : ∑ ψ : AddChar (Additive A) ℂ, (((charOf ψ).comp π ⟨y, hy⟩ : ℂˣ) : ℂ) =
        ∑ ψ : AddChar (Additive A) ℂ, ψ (Additive.ofMul (π ⟨y, hy⟩)) := rfl
    rw [this, AddChar.sum_apply_eq_ite, hcard]
    have hiff : Additive.ofMul (π ⟨y, hy⟩) = 0 ↔ y ∈ H := by
      rw [← hπ ⟨y, hy⟩]; exact ofMul_eq_zero
    by_cases hyH : y ∈ H
    · rw [if_pos (hiff.2 hyH), dif_pos hyH]
      simp only [MonoidHom.one_apply, Units.val_one, mul_one,
        Fintype.card_congr Additive.toMul]
      field_simp
    · rw [if_neg (mt hiff.1 hyH), dif_neg hyH]; simp
  · have hyH : y ∉ H := fun h => hy (hHK h)
    simp [dif_neg hy, dif_neg hyH]

/-- The group identity `Ind(H,1) = Σ_ψ Ind(K, ψ ∘ π)` for an abelian quotient `π : K ↠ A` with
kernel `H`. -/
theorem ind_eq_sum {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) (hHK : H ≤ K)
    {A : Type*} [CommGroup A] [Fintype A] (π : K →* A) (hπ : ∀ k : K, π k = 1 ↔ (k : G) ∈ H)
    (hcard : (Nat.card K : ℂ) = Fintype.card A * Nat.card H) (g : G) :
    ind H 1 g = ∑ ψ : AddChar (Additive A) ℂ, ind K ((charOf ψ).comp π) g := by
  unfold ind
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => (pointwise H K hHK π hπ hcard _).symm

/-- The group identity with the characters indexed by `Fin n`, for `K/H` abelian. -/
theorem exists_ind_eq_sum {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) (hHK : H ≤ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ H) :
    ∃ (n : ℕ) (χ : Fin n → (K →* ℂˣ)), ∀ g : G, ind H 1 g = ∑ i, ind K (χ i) g := by
  set N := H.subgroupOf K
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hcomm g.1 g.2 n.1 n.2
    have h2 : (g * n * g⁻¹ : K).1 = (g.1 * n.1 * g.1⁻¹ * n.1⁻¹) * n.1 := by simp [mul_assoc]
    rw [h2]; exact H.mul_mem h1 hn⟩
  let Q := K ⧸ N
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := by
        intro a b
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := hcomm b⁻¹.1 (K.inv_mem b.2) a⁻¹.1 (K.inv_mem a.2)
        simpa [mul_assoc] using this }
  let π : K →* Q := QuotientGroup.mk' N
  have hπ : ∀ k : K, π k = 1 ↔ (k : G) ∈ H := fun k => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcard : (Nat.card K : ℂ) = Fintype.card Q * Nat.card H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_eq_fintype_card (α := Q),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
    push_cast; rfl
  let e := Fintype.equivFin (AddChar (Additive Q) ℂ)
  refine ⟨_, fun i => (charOf (e.symm i)).comp π, fun g => ?_⟩
  rw [ind_eq_sum H K hHK π hπ hcard g]
  exact (Equiv.sum_comp e.symm (fun ψ => ind K ((charOf ψ).comp π) g)).symm


/-! ### Step 1 in the `ℚ̄` model -/

theorem lSeries_one {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] :
    ArtinL.Abelian.LSeries (1 : (M ≃ₐ[K] M) →* ℂˣ) = dedekindZeta K := by
  funext s
  refine LSeries_congr (fun {n} hn => ?_) s
  have hloc : ∀ v, ArtinL.Abelian.localValue (1 : (M ≃ₐ[K] M) →* ℂˣ) v = 1 := by
    intro v
    simp [ArtinL.Abelian.localValue, ArtinL.Abelian.IsUnramifiedAt]
  have hval : ∀ I, ArtinL.Abelian.idealValue (1 : (M ≃ₐ[K] M) →* ℂˣ) I = 1 := by
    intro I
    simp [ArtinL.Abelian.idealValue, hloc]
  rw [ArtinL.Abelian.coeff, if_neg hn]
  simp only [hval, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Set.ncard_eq_toFinset_card _ _, ← Nat.card_coe_set_eq]
  rfl

theorem ofSubgroup_one {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]
    (H : Subgroup (F ≃ₐ[k] F)) : ArtinL.Abelian.ofSubgroup H (1 : H →* ℂˣ) = 1 := by
  simp [ArtinL.Abelian.ofSubgroup]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/-- Induction data: a subgroup with a character. -/
abbrev IndDatum (F : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
  Σ J : Subgroup (F ≃ₐ[ℚ] F), (J →* ℂˣ)

/-- `L(ψ)` for `ψ = ofSubgroup J χ`. -/
noncomputable def lf {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField F]
    [IsGalois ℚ F] (q : IndDatum F) (s : ℂ) : ℂ :=
  ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup q.1 q.2) s

theorem lf_one {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField F]
    [IsGalois ℚ F] (X : Subgroup (F ≃ₐ[ℚ] F)) :
    lf (⟨X, 1⟩ : IndDatum F) = dedekindZeta (IntermediateField.fixedField X) := by
  funext s
  rw [lf, ofSubgroup_one, lSeries_one]

/-- 63e4cbfd applied to the trivial one-dimensional representation (trace `1`). -/
theorem artin_trivial (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F]
    [IsGalois ℚ F] {k : ℕ} (p : Fin k → IndDatum F) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ∑ i : Fin k, (a i : ℂ) * ind (p i).1 (p i).2 g = 1)
    {s : ℂ} (hs : 1 < s.re) :
    _root_.LSeries (ArtinL.coeff (1 : Γℚ →* GL (Fin 1) ℂ)) s * ∏ i, lf (p i) s ^ (-a i).toNat =
      ∏ i, lf (p i) s ^ (a i).toNat :=
  ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum 1 F 1 (MonoidHom.one_comp _).symm
    (fun i => (p i).1) (fun i => (p i).2) a (fun g => by
      have h := htr g
      simp only [ind] at h
      rw [h]; simp) hs

/-- **Step 1 in `ℚ̄`**: for `H ≤ K` in `Gal(M/ℚ)` with `K/H` abelian,
`ζ_{M^H} = ∏_χ L(ofSubgroup K χ)` over the characters `χ` of `K` trivial on `H`. -/
theorem zeta_eq_prod (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField M]
    [IsGalois ℚ M] (H K : Subgroup (M ≃ₐ[ℚ] M)) (hHK : H ≤ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ H) :
    ∃ (n : ℕ) (χ : Fin n → (K →* ℂˣ)), ∀ s : ℂ, 1 < s.re →
      dedekindZeta (IntermediateField.fixedField H) s =
        ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup K (χ i)) s := by
  obtain ⟨n, χ, hid⟩ := exists_ind_eq_sum H K hHK hcomm
  refine ⟨n, χ, fun s hs => ?_⟩
  let pT : IndDatum M := ⟨⊤, 1⟩
  have htop : ∀ g : M ≃ₐ[ℚ] M, ind pT.1 pT.2 g = 1 := by
    intro g
    simp only [ind, pT, Subgroup.mem_top, dite_true, MonoidHom.one_apply, Units.val_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_eq_fintype_card]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  let p2 : Fin (n + 2) → IndDatum M :=
    Fin.cons pT (Fin.cons ⟨H, 1⟩ (fun i => ⟨K, χ i⟩))
  let a2 : Fin (n + 2) → ℤ := Fin.cons 1 (Fin.cons 1 (fun _ => -1))
  have h1 : _root_.LSeries (ArtinL.coeff (1 : Γℚ →* GL (Fin 1) ℂ)) s = lf pT s := by
    have := artin_trivial M (fun _ : Fin 1 => pT) (fun _ => 1) (fun g => by simp [htop g]) hs
    simpa using this
  have h2 : _root_.LSeries (ArtinL.coeff (1 : Γℚ →* GL (Fin 1) ℂ)) s *
      ∏ i, lf ⟨K, χ i⟩ s = lf pT s * lf ⟨H, 1⟩ s := by
    have := artin_trivial M p2 a2 (fun g => by
      have hg := hid g
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      change ((1 : ℤ) : ℂ) * ind pT.1 pT.2 g + (((1 : ℤ) : ℂ) * ind H 1 g +
        ∑ i : Fin n, ((-1 : ℤ) : ℂ) * ind K (χ i) g) = 1
      rw [htop g]
      simp only [Int.cast_one, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, one_mul]
      linear_combination hg) hs
    simpa [Fin.prod_univ_succ, p2, a2] using this
  have hT : lf pT s ≠ 0 := by
    rw [lf_one]
    exact NumberField.dedekindZeta_ne_zero_of_one_lt_re _ hs
  rw [h1] at h2
  have h' := mul_left_cancel₀ hT h2
  rw [lf_one] at h'
  rw [← h']
  rfl

/-! ### Transport to abstract `F ⊆ L` -/

/-- **Step 1** (product formula), with the base `fixedField K` inside a Galois `M ⊆ ℚ̄`. -/
theorem product_formula (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois F L] (hab : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ) :
    ∃ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField M) (_ : IsGalois ℚ M)
      (K : Subgroup (M ≃ₐ[ℚ] M)) (_ : F ≃+* IntermediateField.fixedField K)
      (n : ℕ) (χ : Fin n → (K →* ℂˣ)), ∀ s : ℂ, 1 < s.re →
        dedekindZeta L s = ∏ i, ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup K (χ i)) s := by
  let φ : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)
  haveI : NumberField M := ⟨⟩
  haveI := ABA.isAlgClosure_rat
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  haveI : IsGalois ℚ M := IsGalois.normalClosure ℚ L (AlgebraicClosure ℚ)
  let ψ : L →ₐ[ℚ] M := φ.codRestrict M.toSubalgebra
    (fun x => φ.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let ψK : F →ₐ[ℚ] M := ψ.comp (IsScalarTower.toAlgHom ℚ F L)
  set HL := ψ.fieldRange.fixingSubgroup with hHL
  set HK := ψK.fieldRange.fixingSubgroup with hHK
  have hle : HL ≤ HK := by
    apply IntermediateField.fixingSubgroup_antitone
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap F L x, rfl⟩
  have hcomm : ∀ a ∈ HK, ∀ b ∈ HK, a * b * a⁻¹ * b⁻¹ ∈ HL := by
    intro a ha b hb
    letI : Algebra F M := (ψK : F →+* M).toAlgebra
    letI : Algebra L M := (ψ : L →+* M).toAlgebra
    haveI : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let lift : ∀ k ∈ HK, M ≃ₐ[F] M := fun k hk => AlgEquiv.ofRingEquiv (f := k.toRingEquiv)
      (fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ ⟨x, rfl⟩)
    let la := lift a ha
    let lb := lift b hb
    have hc : ∀ m : M, (a * b * a⁻¹ * b⁻¹) m = (la * lb * la⁻¹ * lb⁻¹) m := fun m => rfl
    let r := AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L
    have hr : r (la * lb * la⁻¹ * lb⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hab (r la) (r lb)]
      group
    rw [hHL, IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨y, rfl⟩
    change (a * b * a⁻¹ * b⁻¹) (algebraMap L M y) = algebraMap L M y
    rw [hc, ← AlgEquiv.restrictNormal_commutes]
    change algebraMap L M (r (la * lb * la⁻¹ * lb⁻¹) y) = _
    rw [hr]; rfl
  obtain ⟨n, χ, hEq⟩ := zeta_eq_prod M HL HK hle hcomm
  have hK := IsGalois.fixedField_fixingSubgroup ψK.fieldRange
  refine ⟨M, inferInstance, inferInstance, HK,
    (AlgEquiv.ofInjectiveField ψK).toRingEquiv.trans
      (IntermediateField.equivOfEq hK).symm.toRingEquiv, n, χ, fun s hs => ?_⟩
  rw [← ABA.dedekindZeta_fixedField_fixingSubgroup_fieldRange ψ]
  exact hEq s hs

/-! ### Step 3: assembly -/

/-- What P needs from Q (step 2): Hecke characters for the characters of a Galois `M/K`. -/
def BridgeStatement : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ),
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧ ∃ η : ArtinPrimitiveRoots.HeckeChar K 𝔣,
      ∀ s : ℂ, 1 < s.re → η.LSeries s = ArtinL.Abelian.LSeries ψ s

theorem absNorm_map_ringEquiv {F F' : Type} [Field F] [NumberField F] [Field F']
    [NumberField F'] (f : 𝓞 F ≃+* 𝓞 F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map f) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm

/-- Transport of a `HeckeChar` along a ring isomorphism of number fields. -/
theorem heckeChar_transport {F F' : Type} [Field F] [NumberField F] [Field F']
    [NumberField F'] (e : F ≃+* F') {𝔣' : Ideal (𝓞 F')} (h𝔣 : 𝔣' ≠ ⊥)
    (η' : ArtinPrimitiveRoots.HeckeChar F' 𝔣') :
    ∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ ∃ η : ArtinPrimitiveRoots.HeckeChar F 𝔣,
      η.LSeries = η'.LSeries := by
  set f : 𝓞 F ≃+* 𝓞 F' := RingOfIntegers.mapRingEquiv e
  have h1 : ∀ I : Ideal (𝓞 F), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 F'), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  have htop : ∀ I : Ideal (𝓞 F), I.map f = ⊤ ↔ I = ⊤ := fun I => by
    constructor
    · intro h; rw [← h1 I, h, Ideal.map_top]
    · rintro rfl; exact Ideal.map_top _
  have hbot : ∀ I : Ideal (𝓞 F), I.map f = ⊥ ↔ I = ⊥ := fun I =>
    Ideal.map_eq_bot_iff_of_injective f.injective
  have hmc : (𝔣'.comap f).map f = 𝔣' := Ideal.map_comap_of_surjective _ f.surjective _
  refine ⟨𝔣'.comap f, fun h => h𝔣 (by rw [← hmc, h, Ideal.map_bot]), ?_⟩
  refine ⟨{ toFun := fun I => η'.toFun (I.map f)
            map_mul' := fun I J => by rw [Ideal.map_mul]; exact η'.map_mul' _ _
            eq_zero_iff' := fun I => by
              have hsup : I.map f ⊔ 𝔣' = (I ⊔ 𝔣'.comap f).map f := by
                rw [Ideal.map_sup, hmc]
              rw [η'.eq_zero_iff', hbot, hsup, Ne, htop]
            map_principal' := fun α hα h1α => by
              rw [Ideal.map_span, Set.image_singleton]
              refine η'.map_principal' (f α) (by simpa using hα) ?_
              rw [← map_one f, ← map_sub]
              exact h1α }, ?_⟩
  funext s
  refine LSeries_congr (fun {n} _ => ?_) s
  unfold ArtinPrimitiveRoots.HeckeChar.coeff
  refine finsum_mem_eq_of_bijOn (fun I => I.map f) ⟨?_, ?_, ?_⟩ (fun I _ => rfl)
  · intro I hI
    simp only [Set.mem_ofPred_eq] at hI ⊢
    rw [absNorm_map_ringEquiv, hI]
  · intro I _ J _ hIJ
    rw [← h1 I, ← h1 J]
    exact congrArg (Ideal.map f.symm) hIJ
  · intro J hJ
    refine ⟨J.map f.symm, ?_, h2 J⟩
    simp only [Set.mem_ofPred_eq] at hJ ⊢
    rw [← hJ, ← absNorm_map_ringEquiv f, h2]

/-- **Step 3**: 4e03429e from the bridge. -/
theorem goal_of_bridge (hQ : BridgeStatement) (F L : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L]
    (hab : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ) :
    ∃ (n : ℕ) (𝔪 : Fin n → Ideal (𝓞 F)), (∀ i, 𝔪 i ≠ ⊥) ∧
      ∃ η : (i : Fin n) → ArtinPrimitiveRoots.HeckeChar F (𝔪 i),
        ∀ s : ℂ, 1 < s.re → dedekindZeta L s = ∏ i, (η i).LSeries s := by
  obtain ⟨M, _, _, K, e, n, χ, hζ⟩ := product_formula F L hab
  letI : Algebra F (IntermediateField.fixedField K) := e.toRingHom.toAlgebra
  haveI : IsTotallyComplex (IntermediateField.fixedField K) := isTotallyComplex_of_algebra F _
  have hb := fun i => hQ (IntermediateField.fixedField K) M
    (ArtinL.Abelian.ofSubgroup K (χ i))
  choose 𝔣 h𝔣 η hη using hb
  have ht := fun i => heckeChar_transport e (h𝔣 i) (η i)
  choose 𝔪 h𝔪 η' hη' using ht
  refine ⟨n, 𝔪, h𝔪, η', fun s hs => ?_⟩
  rw [hζ s hs]
  exact Finset.prod_congr rfl fun i _ => by rw [hη' i, hη i s hs]

end ABP
end

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply nonZeroDivisors

namespace ABQ

section Coprime

variable {F : Type*} [Field F] [NumberField F]

theorem sup_eq_top_iff_forall {I 𝔣 : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ⊔ 𝔣 = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ 𝔣 → ¬ v.asIdeal ∣ I := by
  constructor
  · intro h v hf hI'
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← h]
    exact sup_le (Ideal.le_of_dvd hI') (Ideal.le_of_dvd hf)
  · intro h
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmb : m ≠ ⊥ := by
      intro hb
      apply hI
      rw [eq_bot_iff, ← hb]
      exact le_trans le_sup_left hle
    let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, hmb⟩
    exact h v (Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle))
      (Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle))

theorem mk0_mem_coprimeToModulus_iff {I 𝔣 : Ideal (𝓞 F)} (hI : I ∈ (Ideal (𝓞 F))⁰) :
    FractionalIdeal.mk0 F ⟨I, hI⟩ ∈ coprimeToModulus F 𝔣 ↔ I ⊔ 𝔣 = ⊤ := by
  have hI0 : I ≠ 0 := nonZeroDivisors.ne_zero hI
  rw [mem_coprimeToModulus_iff, sup_eq_top_iff_forall hI0]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
  constructor
  · intro h hd
    exact (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mpr hd h
  · intro h
    by_contra hc
    exact h ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hc)

omit [NumberField F] in
theorem cond_mul {I J 𝔣 : Ideal (𝓞 F)} :
    (I * J ≠ ⊥ ∧ I * J ⊔ 𝔣 = ⊤) ↔ ((I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤) ∧ (J ≠ ⊥ ∧ J ⊔ 𝔣 = ⊤)) := by
  rw [Ne, Ideal.mul_eq_bot, ← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_left_iff,
    Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_iff_sup_eq]
  tauto

end Coprime

section Hecke

variable {F : Type*} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)}

open Classical in
/-- The ideal-theoretic function attached to a narrow ray class character: the character of the
class of `I` when `I` is nonzero and coprime to `𝔣`, and `0` otherwise. -/
noncomputable def heckeFun (χ : NarrowRayClassGroup F 𝔣 →* ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  if h : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ then
    χ (NarrowRayClassGroup.mk F 𝔣
      ⟨FractionalIdeal.mk0 F ⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩,
        (mk0_mem_coprimeToModulus_iff _).2 h.2⟩)
  else 0

theorem heckeFun_of (χ : NarrowRayClassGroup F 𝔣 →* ℂ) {I : Ideal (𝓞 F)}
    (hI : I ∈ (Ideal (𝓞 F))⁰) (hc : FractionalIdeal.mk0 F ⟨I, hI⟩ ∈ coprimeToModulus F 𝔣) :
    heckeFun χ I = χ (NarrowRayClassGroup.mk F 𝔣 ⟨FractionalIdeal.mk0 F ⟨I, hI⟩, hc⟩) := by
  rw [heckeFun, dif_pos ⟨nonZeroDivisors.ne_zero hI, (mk0_mem_coprimeToModulus_iff hI).1 hc⟩]

theorem heckeFun_of_not (χ : NarrowRayClassGroup F 𝔣 →* ℂ) {I : Ideal (𝓞 F)}
    (h : ¬ (I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤)) : heckeFun χ I = 0 := by
  rw [heckeFun, dif_neg h]

theorem map_ne_zero_of_group {G : Type*} [Group G] (χ : G →* ℂ) (g : G) : χ g ≠ 0 := by
  have h := map_mul χ g g⁻¹
  rw [mul_inv_cancel, map_one] at h
  exact left_ne_zero_of_mul_eq_one h.symm

theorem heckeFun_mul (χ : NarrowRayClassGroup F 𝔣 →* ℂ) (I J : Ideal (𝓞 F)) :
    heckeFun χ (I * J) = heckeFun χ I * heckeFun χ J := by
  by_cases hI : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤
  · by_cases hJ : J ≠ ⊥ ∧ J ⊔ 𝔣 = ⊤
    · have hIJ : I * J ≠ ⊥ ∧ I * J ⊔ 𝔣 = ⊤ := cond_mul.2 ⟨hI, hJ⟩
      rw [heckeFun, dif_pos hIJ, heckeFun, dif_pos hI, heckeFun, dif_pos hJ, ← map_mul, ← map_mul]
      apply congrArg
      apply congrArg
      apply Subtype.ext
      show FractionalIdeal.mk0 F ⟨I * J, _⟩ =
        FractionalIdeal.mk0 F ⟨I, _⟩ * FractionalIdeal.mk0 F ⟨J, _⟩
      rw [← map_mul]
      rfl
    · rw [heckeFun_of_not χ hJ, mul_zero, heckeFun_of_not χ (fun h => hJ (cond_mul.1 h).2)]
  · rw [heckeFun_of_not χ hI, zero_mul, heckeFun_of_not χ (fun h => hI (cond_mul.1 h).1)]

theorem heckeFun_eq_zero_iff (χ : NarrowRayClassGroup F 𝔣 →* ℂ) (I : Ideal (𝓞 F)) :
    heckeFun χ I = 0 ↔ (I = ⊥ ∨ I ⊔ 𝔣 ≠ ⊤) := by
  by_cases h : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤
  · rw [heckeFun, dif_pos h]
    simp only [map_ne_zero_of_group, false_iff, not_or, not_not]
    exact h
  · rw [heckeFun_of_not χ h]
    simp only [true_iff]
    tauto

/-- A narrow ray class character that is trivial on principal ideals `(α)` with `α ≡ 1 (mod 𝔣)`
(no sign condition) is a `HeckeChar F 𝔣`. -/
noncomputable def toHeckeChar (χ : NarrowRayClassGroup F 𝔣 →* ℂ)
    (hsign : ∀ (α : 𝓞 F) (hα : α ≠ 0) (hc : principalUnit F α hα ∈ coprimeToModulus F 𝔣),
      α - 1 ∈ 𝔣 → χ (NarrowRayClassGroup.mk F 𝔣 ⟨principalUnit F α hα, hc⟩) = 1) :
    ArtinPrimitiveRoots.HeckeChar F 𝔣 where
  toFun := heckeFun χ
  map_mul' := heckeFun_mul χ
  eq_zero_iff' := heckeFun_eq_zero_iff χ
  map_principal' := by
    intro α hα h1
    have hspan : Ideal.span {α} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hα
    have hsup : Ideal.span {α} ⊔ 𝔣 = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have h : (1 : 𝓞 F) = α - (α - 1) := by ring
      rw [h]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
        (Ideal.mem_sup_right h1)
    rw [heckeFun, dif_pos ⟨hspan, hsup⟩]
    exact hsign α hα _ h1

end Hecke

section Factor

variable {F : Type*} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)}

theorem hasFiniteMulSupport_pow_count (f : HeightOneSpectrum (𝓞 F) → ℂ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  by_contra hd
  apply hv
  have : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
    by_contra hc
    exact hd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hc)
  simp only [this, pow_zero]

open Classical in
theorem count_prime_eq (v w : HeightOneSpectrum (𝓞 F)) :
    (Associates.mk v.asIdeal).count (Associates.mk w.asIdeal).factors = if v = w then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Associates.count_self v.associates_irreducible
  · by_contra hc
    have hd := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).mp hc
    apply h
    exact HeightOneSpectrum.ext
      ((w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)).symm)

/-- A `HeckeChar` is determined on nonzero ideals by its values at primes. -/
theorem heckeChar_eq_finprod (η : ArtinPrimitiveRoots.HeckeChar F 𝔣)
    (f : HeightOneSpectrum (𝓞 F) → ℂ) (hf : ∀ v : HeightOneSpectrum (𝓞 F), η.toFun v.asIdeal = f v)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    η.toFun I = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      f v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  revert hI
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _
    rw [Ideal.isUnit_iff] at hx
    subst hx
    have h1 : η.toFun ⊤ = 1 := by
      have := η.map_principal' 1 one_ne_zero (by rw [sub_self]; exact Ideal.zero_mem _)
      rwa [Ideal.span_singleton_one] at this
    rw [h1, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    exact (finprod_eq_one_of_forall_eq_one fun v => by
      rw [Associates.count_zero v.associates_irreducible, pow_zero]).symm
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := ha
    let v₀ : HeightOneSpectrum (𝓞 F) := HeightOneSpectrum.ofPrime hp
    have hp0 : p ≠ 0 := hp.ne_zero
    rw [η.map_mul', ih ha']
    have hcount : ∀ v : HeightOneSpectrum (𝓞 F),
        (Associates.mk v.asIdeal).count (Associates.mk (p * a)).factors =
          (Associates.mk v.asIdeal).count (Associates.mk p).factors +
            (Associates.mk v.asIdeal).count (Associates.mk a).factors := by
      intro v
      rw [← Associates.mk_mul_mk]
      exact Associates.count_mul (Associates.mk_ne_zero.mpr hp0) (Associates.mk_ne_zero.mpr ha)
        v.associates_irreducible
    simp_rw [hcount, pow_add]
    rw [finprod_mul_distrib (hasFiniteMulSupport_pow_count f (I := p) hp0)
      (hasFiniteMulSupport_pow_count f ha')]
    congr 1
    have hp' : p = v₀.asIdeal := rfl
    rw [hp', hf v₀, finprod_eq_single _ v₀]
    · rw [count_prime_eq, if_pos rfl, pow_one]
    · intro v hv
      rw [count_prime_eq, if_neg hv, pow_zero]

end Factor

section Conductor

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

omit [IsGalois K M] in
theorem conductor_ne_bot (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ArtinL.Abelian.conductor ψ ≠ ⊥ := by
  unfold ArtinL.Abelian.conductor
  refine finprod_induction (fun I : Ideal (𝓞 K) => I ≠ ⊥) ?_ ?_ ?_
  · rw [Ideal.one_eq_top]
    exact top_ne_bot
  · intro x y hx hy
    rw [Ne, Ideal.mul_eq_bot]
    tauto
  · intro v
    exact pow_ne_zero _ v.ne_bot

omit [IsGalois K M] in
theorem conductorExponent_eq_zero (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hu : ArtinL.Abelian.IsUnramifiedAt ψ v) : ArtinL.Abelian.conductorExponent ψ v = 0 := by
  have hs : ArtinL.Abelian.swanConductor ψ v = 0 := by
    unfold ArtinL.Abelian.swanConductor
    refine (finsum_congr fun i => ?_).trans finsum_zero
    rw [if_pos, mul_zero]
    intro σ hσ
    apply hu
    intro x
    exact Ideal.pow_le_self (by omega) (hσ x)
  rw [ArtinL.Abelian.conductorExponent, if_pos hu, hs]
  simp

omit [IsGalois K M] in
theorem not_isUnramifiedAt_of_dvd_conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ ArtinL.Abelian.conductor ψ) :
    ¬ ArtinL.Abelian.IsUnramifiedAt ψ v := by
  intro hu
  have he := conductorExponent_eq_zero ψ v hu
  unfold ArtinL.Abelian.conductor at hv
  set g := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal ^ ArtinL.Abelian.conductorExponent ψ w
    with hg
  by_cases hfin : Function.HasFiniteMulSupport g
  · rw [finprod_eq_prod g hfin] at hv
    obtain ⟨w, hw, hdw⟩ := (Prime.dvd_finsetProd_iff v.prime _).mp hv
    have hw' : w ∈ Function.mulSupport g := by rwa [Set.Finite.mem_toFinset] at hw
    have hvw : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow hdw
    have hveq : v = w := HeightOneSpectrum.ext
      ((w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hvw)).symm)
    subst hveq
    apply hw'
    simp only [hg, he, pow_zero]
  · rw [finprod_of_infinite_mulSupport hfin] at hv
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← Ideal.one_eq_top]
    exact Ideal.le_of_dvd hv

theorem localValue_eq_zero_of_dvd_conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ ArtinL.Abelian.conductor ψ) :
    ArtinL.Abelian.localValue ψ v = 0 := by
  rw [ArtinL.Abelian.localValue, if_neg (not_isUnramifiedAt_of_dvd_conductor ψ v hv)]

end Conductor

/-- **Exported.** A character of `Gal(M/F)`, `F` totally complex, is a `HeckeChar F 𝔣` with
`𝔣 ≠ ⊥` (the Artin conductor) whose L-series is the Artin L-series of `ψ`, everywhere. -/
theorem exists_heckeChar_lSeries_eq (F M : Type) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field M] [NumberField M] [Algebra F M] [IsGalois F M]
    (ψ : (M ≃ₐ[F] M) →* ℂˣ) :
    ∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ ∃ η : ArtinPrimitiveRoots.HeckeChar F 𝔣,
      ∀ s : ℂ, η.LSeries s = ArtinL.Abelian.LSeries ψ s := by
  classical
  obtain ⟨χ, hχv, -, hχsign, -⟩ :=
    ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 F M ψ
  have hsign : ∀ (α : 𝓞 F) (hα : α ≠ 0)
      (hc : principalUnit F α hα ∈ coprimeToModulus F (ArtinL.Abelian.conductor ψ)),
      α - 1 ∈ ArtinL.Abelian.conductor ψ →
        χ (NarrowRayClassGroup.mk F (ArtinL.Abelian.conductor ψ)
          ⟨principalUnit F α hα, hc⟩) = 1 := by
    intro α hα hc h1
    rw [hχsign α hα hc h1]
    apply Finset.prod_eq_one
    intro w _
    exact absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.mpr
      (NumberField.IsTotallyComplex.isComplex w.1))
  let η := toHeckeChar χ hsign
  refine ⟨ArtinL.Abelian.conductor ψ, conductor_ne_bot ψ, η, fun s => ?_⟩
  have hprime : ∀ v : HeightOneSpectrum (𝓞 F), η.toFun v.asIdeal = ArtinL.Abelian.localValue ψ v := by
    intro v
    by_cases hv : v.asIdeal ∣ ArtinL.Abelian.conductor ψ
    · rw [localValue_eq_zero_of_dvd_conductor ψ v hv]
      show heckeFun χ v.asIdeal = 0
      rw [heckeFun_eq_zero_iff]
      right
      rw [sup_eq_left.mpr (Ideal.le_of_dvd hv)]
      exact v.isPrime.ne_top
    · show heckeFun χ v.asIdeal = _
      rw [heckeFun_of χ _ (primeUnit_mem_coprimeToModulus F hv)]
      exact hχv v hv
  have key : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → η.toFun I = ArtinL.Abelian.idealValue ψ I :=
    fun I hI => heckeChar_eq_finprod η _ hprime I hI
  unfold ArtinPrimitiveRoots.HeckeChar.LSeries ArtinL.Abelian.LSeries
  apply LSeries_congr
  intro n hn
  rw [ArtinPrimitiveRoots.HeckeChar.coeff, ArtinL.Abelian.coeff, if_neg hn,
    finsum_mem_eq_finite_toFinset_sum _ (Ideal.finite_setOfPred_absNorm_eq n)]
  refine Finset.sum_congr rfl fun I hI => key I ?_
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
  rintro rfl
  rw [Ideal.absNorm_bot] at hI
  exact hn hI.symm

end ABQ

end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots

end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (F L : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L]
    (hab : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ) :
    ∃ (n : ℕ) (𝔪 : Fin n → Ideal (𝓞 F)), (∀ i, 𝔪 i ≠ ⊥) ∧
      ∃ η : (i : Fin n) → HeckeChar F (𝔪 i),
        ∀ s : ℂ, 1 < s.re → dedekindZeta L s = ∏ i, (η i).LSeries s :=
  ABP.goal_of_bridge (fun K M _ _ _ _ _ _ _ ψ => by
    obtain ⟨𝔣, h𝔣, η, hη⟩ := ABQ.exists_heckeChar_lSeries_eq K M ψ
    exact ⟨𝔣, h𝔣, η, fun s _ => hη s⟩) F L hab
end
