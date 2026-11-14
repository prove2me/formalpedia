-- Prove2me | Definitions.Def_RPLib_S3_HypParC
-- name    : RPLib_S3_HypParC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:12:38.192492+00:00
-- url     : https://prove2.me/theorems/f01e8209-0346-4fee-87a3-5aa91343300b
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part C: trace-down to $SL_2(\mathbb{Z})$
-- statement:
--   Vectors of exact order $M$ in $(\mathbb{Z}/M)^2$ fibre in pairs $\{v, -v\}$ over $SL_2(\mathbb{Z}) / \pm\Gamma_1(M)$ ($M \ge 3$); hence the integral of the hyperbolic-parabolic part over $\Gamma_1(M) \backslash \mathbb{H}$ equals an integral over the standard fundamental domain of a sum weighted by level-vector counts.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_EllipticTerm
import Definitions.Def_RPLib_S3_ConjClassesB

/-!
# S3-HypParTerms, part C: trace-down of the rest part to `SL₂(ℤ)`

* `card_exact_filter`: exact-order vectors fibre over `SL₂(ℤ)/±Γ₁(M)` in pairs `{v, -v}` (`M ≥ 3`).
* `levelCount_eq`: `levelCount M δ' g = 2 · #{c ∈ SL₂(ℤ)/±Γ₁(M) : g (c e₁) = δ' (c e₁)}`.
* `levelCount_conj`, `isRest_conj`: conjugation invariance.
* **`traceDown`**: `∫_{fdom Γ₁(M)} restPart = ∫_𝒟 Ktil`, `Ktil z = Σ'_g [det g = n, g rest] (levelCount g / 2) φ_g(z)`.
-/

open MeasureTheory Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal MatrixGroups Modular Pointwise RamanujanPetersson.S3.Conj

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RP.FundDomain RP.Petersson RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl

/-! ## Counting cosets through level vectors -/

section Count

variable {M : ℕ} [NeZero M]

lemma neg_smul_SL (x : SL(2, ℤ)) (v : Fin 2 → ZMod M) : (-x) • v = -(x • v) := by
  rw [S3.Conj.vsmul_def, S3.Conj.vsmul_def, Matrix.SpecialLinearGroup.coe_neg]
  simp [S3.Conj.redMat]
  exact ⟨add_comm _ _, add_comm _ _⟩

lemma smul_neg_SL (x : SL(2, ℤ)) (v : Fin 2 → ZMod M) : x • (-v) = -(x • v) := by
  rw [S3.Conj.vsmul_def, S3.Conj.vsmul_def, Matrix.mulVec_neg]

lemma isExact_neg {v : Fin 2 → ZMod M} (hv : S3.Conj.IsExact M v) : S3.Conj.IsExact M (-v) := by
  intro d hd hd0 h
  apply hv d hd hd0
  rw [smul_neg, neg_eq_zero] at h
  exact h

lemma ne_neg_of_isExact (hM : 3 ≤ M) {v : Fin 2 → ZMod M} (hv : S3.Conj.IsExact M v) : v ≠ -v := by
  intro h
  apply hv 2 (Finset.mem_range.2 (by omega)) (by norm_num)
  rw [two_nsmul]
  nth_rewrite 2 [h]
  exact add_neg_cancel v

lemma eig_neg (δ' : ZMod M) (g : S3.Conj.Mat) (v : Fin 2 → ZMod M) :
    S3.Conj.Eig M δ' g (-v) ↔ S3.Conj.Eig M δ' g v := by
  unfold S3.Conj.Eig
  rw [Matrix.mulVec_neg, smul_neg, neg_inj]

lemma mk_rep_eq_iff {v : Fin 2 → ZMod M} (hv : S3.Conj.IsExact M v) (c : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) :
    ((S3.Conj.rep v : SL(2, ℤ)) : SL(2, ℤ) ⧸ pmSL (Gamma1 M)) = c ↔
      v = c.out • S3.Conj.e1 M ∨ v = -(c.out • S3.Conj.e1 M) := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rw [QuotientGroup.eq, mem_pmSL, S3.Conj.mem_Gamma1_iff, S3.Conj.mem_Gamma1_iff, neg_smul_SL, mul_smul,
    inv_smul_eq_iff, neg_eq_iff_eq_neg, inv_smul_eq_iff, smul_neg_SL, S3.Conj.rep_spec hv]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])

open Classical in
theorem card_exact_filter (hM : 3 ≤ M) (P : (Fin 2 → ZMod M) → Prop) (hP : ∀ v, P (-v) ↔ P v) :
    (Finset.univ.filter fun v => S3.Conj.IsExact M v ∧ P v).card =
      2 * Nat.card {c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) // P (c.out • S3.Conj.e1 M)} := by
  have : (pmSL (Gamma1 M)).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL _)
  let _ : Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M)) := Fintype.ofFinite _
  set S := Finset.univ.filter fun v => S3.Conj.IsExact M v ∧ P v with hS
  let f : (Fin 2 → ZMod M) → SL(2, ℤ) ⧸ pmSL (Gamma1 M) := fun v => (S3.Conj.rep v : SL(2, ℤ))
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
      (S.filter fun v => f v = c).card = 2 * (if P (c.out • S3.Conj.e1 M) then 1 else 0) := by
    intro c
    set w := c.out • S3.Conj.e1 M with hw
    have hwe : S3.Conj.IsExact M w := S3.Conj.isExact_smul (S3.Conj.isExact_e1 M) _
    by_cases hPw : P w
    · rw [if_pos hPw, mul_one]
      have : (S.filter fun v => f v = c) = {w, -w} := by
        ext v
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hv, -⟩, hf⟩
          exact (mk_rep_eq_iff hv c).1 hf
        · rintro (h | h)
          · subst h
            exact ⟨⟨hwe, hPw⟩, (mk_rep_eq_iff hwe c).2 (Or.inl rfl)⟩
          · subst h
            exact ⟨⟨isExact_neg hwe, (hP w).2 hPw⟩, (mk_rep_eq_iff (isExact_neg hwe) c).2 (Or.inr rfl)⟩
      rw [this, Finset.card_pair (ne_neg_of_isExact hM hwe)]
    · rw [if_neg hPw, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv hf
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases (mk_rep_eq_iff hv.1 c).1 hf with h | h
      · rw [h] at hv; exact hPw hv.2
      · rw [h] at hv; exact hPw ((hP w).1 hv.2)
  rw [Finset.sum_congr rfl fun c _ => hfib c, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem levelCount_eq (hM : 3 ≤ M) (δ' : ZMod M) (g : S3.Conj.Mat) :
    S3.levelCount M δ' g =
      2 * Nat.card {c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) // S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M)} := by
  classical
  rw [← card_exact_filter hM _ (eig_neg δ' g), S3.levelCount]
  exact congrArg Finset.card (Finset.filter_congr fun v _ => Iff.rfl)

/-- `conj h g ∈ Δ ↔ det g = n ∧ g (h⁻¹ e₁) = δ' (h⁻¹ e₁)`. -/
lemma conj_mem_DeltaSet_iff (h : SL(2, ℤ)) (g : S3.Conj.Mat) (n : ℤ) (δ' : ZMod M) :
    S3.Conj.conj h⁻¹ g ∈ DeltaSet M n δ' ↔ g.det = n ∧ S3.Conj.Eig M δ' g (h • S3.Conj.e1 M) := by
  rw [mem_DeltaSet, S3.Conj.det_conj, ← S3.Conj.eig_conj_iff δ' h⁻¹ g (h • S3.Conj.e1 M), inv_smul_smul,
    S3.Conj.eig_e1_iff]
  exact and_congr_right fun _ => and_comm

/-- `levelCount` is invariant under `SL₂(ℤ)`-conjugation. -/
theorem levelCount_conj (δ' : ZMod M) (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    S3.levelCount M δ' (S3.Conj.conj h g) = S3.levelCount M δ' g := by
  classical
  unfold S3.levelCount
  refine Finset.card_bij' (fun v _ => h⁻¹ • v) (fun v _ => h • v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    refine ⟨S3.Conj.isExact_smul hv.1 _, ?_⟩
    have e := (S3.Conj.eig_conj_iff δ' h g (h⁻¹ • v)).1
    rw [smul_inv_smul] at e
    exact e hv.2
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨S3.Conj.isExact_smul hv.1 _, (S3.Conj.eig_conj_iff δ' h g v).2 hv.2⟩
  · intro v _; exact smul_inv_smul h v
  · intro v _; exact inv_smul_smul h v

end Count

/-! ## The rest predicate -/

/-- Not scalar and not elliptic. -/
abbrev IsRest (g : S3.Conj.Mat) : Prop :=
  ¬ ((g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) ∨ (g 0 0 + g 1 1) ^ 2 < 4 * g.det)

lemma scal_conj {h : SL(2, ℤ)} {g : S3.Conj.Mat} (hs : g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) :
    S3.Conj.conj h g 1 0 = 0 ∧ S3.Conj.conj h g 0 1 = 0 ∧ S3.Conj.conj h g 0 0 = S3.Conj.conj h g 1 1 := by
  obtain ⟨e00, e01, e10, e11⟩ := conj_entries h g
  obtain ⟨h10, h01, hd⟩ := hs
  rw [e00, e01, e10, e11, h10, h01, hd]
  refine ⟨by ring, by ring, by ring⟩

lemma scal_conj_iff (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    (S3.Conj.conj h g 1 0 = 0 ∧ S3.Conj.conj h g 0 1 = 0 ∧ S3.Conj.conj h g 0 0 = S3.Conj.conj h g 1 1) ↔
      (g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) := by
  refine ⟨fun hs => ?_, scal_conj⟩
  have := scal_conj (h := h⁻¹) hs
  rwa [S3.Conj.conj_inv_conj] at this

lemma trace_conj' (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    S3.Conj.conj h g 0 0 + S3.Conj.conj h g 1 1 = g 0 0 + g 1 1 := by
  have := S3.Conj.trace_conj h g
  rwa [Matrix.trace_fin_two, Matrix.trace_fin_two] at this

lemma isRest_conj (h : SL(2, ℤ)) (g : S3.Conj.Mat) : IsRest (S3.Conj.conj h g) ↔ IsRest g := by
  unfold IsRest
  rw [trace_conj', S3.Conj.det_conj, scal_conj_iff]

lemma phiG_smul (k : ℕ) (h : SL(2, ℤ)) (g : S3.Conj.Mat) (z : ℍ) :
    phiG k (S3.Conj.conj h g) (h • z) = phiG k g z := phiG_conj k h g z

/-! ## Trace-down -/

section TraceDown

variable {M : ℕ} [NeZero M]

open Classical in
/-- The traced-down rest kernel on `𝒟`. -/
def Ktil (k M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (z : ℍ) : ℂ :=
  ∑' g : S3.Conj.Mat, if g.det = n ∧ IsRest g then ((S3.levelCount M δ' g : ℂ) / 2) * phiG k g z else 0

/-- The conjugation `g ↦ h g h⁻¹` as a permutation of the integer matrices. -/
def conjEquiv (h : SL(2, ℤ)) : S3.Conj.Mat ≃ S3.Conj.Mat where
  toFun := S3.Conj.conj h
  invFun := S3.Conj.conj h⁻¹
  left_inv g := S3.Conj.conj_inv_conj h g
  right_inv g := S3.Conj.conj_conj_inv h g

open Classical in
lemma restPart_smul_aux {k : ℕ} (hk : 3 ≤ k) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (h : SL(2, ℤ)) (z : ℍ) :
    Summable (fun g : S3.Conj.Mat =>
        if S3.Conj.conj h g ∈ DeltaSet M n δ' ∧ IsRest g then phiG k g z else 0) ∧
      restPart k M n δ' (h • z) = ∑' g : S3.Conj.Mat,
        if S3.Conj.conj h g ∈ DeltaSet M n δ' ∧ IsRest g then phiG k g z else 0 := by
  set F : S3.Conj.Mat → ℂ := (DeltaSet M n δ').indicator
    (fun x => if IsRest x then phiG k x (h • z) else 0) with hF
  have hsF : Summable F := by
    rw [hF, ← summable_subtype_iff_indicator]
    exact summable_ite hk hn δ' (h • z) IsRest
  have hpt : ∀ g, F (conjEquiv h g) =
      if S3.Conj.conj h g ∈ DeltaSet M n δ' ∧ IsRest g then phiG k g z else 0 := by
    intro g
    show (DeltaSet M n δ').indicator _ (S3.Conj.conj h g) = _
    by_cases hm : S3.Conj.conj h g ∈ DeltaSet M n δ'
    · rw [Set.indicator_of_mem hm]
      by_cases hr : IsRest g
      · rw [if_pos ((isRest_conj h g).2 hr), if_pos ⟨hm, hr⟩, phiG_smul]
      · rw [if_neg (fun h' => hr ((isRest_conj h g).1 h')), if_neg (fun h' => hr h'.2)]
    · rw [Set.indicator_of_notMem hm, if_neg (fun h' => hm h'.1)]
  refine ⟨?_, ?_⟩
  · rw [← funext hpt]
    exact (conjEquiv h).summable_iff.2 hsF
  · rw [← funext hpt, (conjEquiv h).tsum_eq F, hF, ← tsum_subtype]
    rfl

open Classical in
lemma Ktil_eq_sum (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    [Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M))] (z : ℍ) :
    Ktil k M n δ' z = ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), restPart k M n δ' (c.out⁻¹ • z) := by
  rw [Finset.sum_congr rfl fun c _ => (restPart_smul_aux hk hn δ' (c.out)⁻¹ z).2]
  rw [← Summable.tsum_finsetSum (fun c _ => (restPart_smul_aux hk hn δ' _ z).1), Ktil]
  refine tsum_congr fun g => ?_
  simp_rw [conj_mem_DeltaSet_iff]
  by_cases hg : g.det = n ∧ IsRest g
  · rw [if_pos hg]
    have e : ∀ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
        (if (g.det = n ∧ S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M)) ∧ IsRest g then phiG k g z else 0) =
          (if S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M) then 1 else 0) * phiG k g z := by
      intro c
      by_cases he : S3.Conj.Eig M δ' g (c.out • S3.Conj.e1 M)
      · rw [if_pos ⟨⟨hg.1, he⟩, hg.2⟩, if_pos he, one_mul]
      · rw [if_neg (fun h' => he h'.1.2), if_neg he, zero_mul]
    rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.sum_mul, Finset.sum_boole, levelCount_eq hM,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    push_cast
    ring
  · rw [if_neg hg]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun h' => hg ⟨h'.1.1, h'.2⟩).symm

/-- **Trace-down (O2).** `∫_{fdom Γ₁(M)} restPart = ∫_𝒟 Ktil`, and `Ktil` is integrable on `𝒟`. -/
theorem traceDown (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) {n : ℤ} (hn : 0 < n) (δ' : ZMod M)
    (hfi : IntegrableOn (restPart k M n δ') (fdom (Gamma1 M))) :
    IntegrableOn (Ktil k M n δ') 𝒟 ∧
      ∫ z in fdom (Gamma1 M), restPart k M n δ' z = ∫ z in 𝒟, Ktil k M n δ' z := by
  have : (pmSL (Gamma1 M)).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL _)
  let _ : Fintype (SL(2, ℤ) ⧸ pmSL (Gamma1 M)) := Fintype.ofFinite _
  have hpiece : ∀ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M),
      IntegrableOn (fun z => restPart k M n δ' (c.out⁻¹ • z)) 𝒟 := by
    intro c
    have h1 : IntegrableOn (restPart k M n δ') ((c.out)⁻¹ • 𝒟) :=
      hfi.mono_set (subset_iUnion (fun c : SL(2, ℤ) ⧸ pmSL (Gamma1 M) => (c.out)⁻¹ • 𝒟) c)
    rw [← toPGLR_smul_set, ← Set.image_smul,
      (measurePreserving_smul (toPGLR (c.out)⁻¹) volume).integrableOn_image
        (measurableEmbedding_const_smul _)] at h1
    refine h1.congr_fun (fun z _ => ?_) ModularGroup.isClosed_fd.measurableSet
    simp only [Function.comp, toPGLR_smul]
  have hK : Ktil k M n δ' = fun z => ∑ c : SL(2, ℤ) ⧸ pmSL (Gamma1 M), restPart k M n δ' (c.out⁻¹ • z) :=
    funext fun z => Ktil_eq_sum hM hk hn δ' z
  refine ⟨?_, ?_⟩
  · rw [hK]
    exact integrable_finsetSum _ fun c _ => hpiece c
  · have hA := setIntegral_iUnion_inv_smul_fd (Gamma1 M) Quotient.out Quotient.out_eq hfi
    rw [fdom, hA, tsum_fintype, ← integral_finsetSum _ fun c _ => hpiece c, hK]

end TraceDown

end RamanujanPetersson.HypPar


