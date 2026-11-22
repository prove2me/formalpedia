-- Prove2me | solution 1 for AllocationIndices.Precedence.eps_fi_star_near_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:42:03.153813+00:00
-- url     : https://prove2.me/submissions/26a066f6-d15e-4e12-9a60-0a28726f595b

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace EpsFIStarProof

open AllocationIndices.Precedence

/-! ### Section 1: Basic measure and discount properties -/

section MeasureBasics

variable {n : ℕ}

instance instIsProbService {F : JobFamily n} (i : Fin n) :
    IsProbabilityMeasure (F.service i : Measure ℝ) :=
  (F.service i).prop

instance instIsProbServiceLaw {F : JobFamily n} : IsProbabilityMeasure (serviceLaw F) := by
  unfold serviceLaw
  infer_instance

variable (F : JobFamily n)

private lemma ae_pos_coord (i : Fin n) :
    ∀ᵐ x ∂(F.service i : Measure ℝ), 0 < x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ (0 < x)} = Set.Iic 0 := by
    ext x; simp [not_lt]
  rw [hset]
  exact F.service_pos i

private lemma ae_pos_all : ∀ᵐ ω ∂serviceLaw F, ∀ i : Fin n, 0 < ω i := by
  rw [ae_all_iff]
  intro i
  have hmp : MeasurePreserving (Function.eval i) (serviceLaw F) (F.service i : Measure ℝ) := by
    unfold serviceLaw
    exact measurePreserving_eval (fun j => (F.service j : Measure ℝ)) i
  exact hmp.quasiMeasurePreserving.ae (ae_pos_coord F i)

private noncomputable def phi (i : Fin n) : ℝ :=
  ∫ x, Real.exp (-F.γ * x) ∂(F.service i : Measure ℝ)

private lemma integrable_exp_service (i : Fin n) :
    Integrable (fun x : ℝ => Real.exp (-F.γ * x)) (F.service i : Measure ℝ) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.aestronglyMeasurable
  · filter_upwards [ae_pos_coord F i] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos])

private lemma phi_pos (i : Fin n) : 0 < phi F i := by
  unfold phi
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (integrable_exp_service F i)]
  have hsupp : Function.support (fun x : ℝ => Real.exp (-F.γ * x)) = Set.univ := by
    ext x; simp [(Real.exp_pos _).ne']
  rw [hsupp, measure_univ]
  exact zero_lt_one

private lemma phi_lt_one (i : Fin n) : phi F i < 1 := by
  have hsub : 0 < ∫ x, (1 - Real.exp (-F.γ * x)) ∂(F.service i : Measure ℝ) := by
    have hint : Integrable (fun x : ℝ => 1 - Real.exp (-F.γ * x)) (F.service i : Measure ℝ) :=
      (integrable_const 1).sub (integrable_exp_service F i)
    have hnn : 0 ≤ᵐ[(F.service i : Measure ℝ)] fun x : ℝ => 1 - Real.exp (-F.γ * x) := by
      filter_upwards [ae_pos_coord F i] with x hx
      have hlt : Real.exp (-F.γ * x) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [F.γ_pos])
      exact sub_nonneg.mpr hlt.le
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    have hsub_set : Set.Ioi (0 : ℝ) ⊆ Function.support (fun x : ℝ => 1 - Real.exp (-F.γ * x)) := by
      intro x hx
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      exact (Real.exp_lt_one_iff.mpr (by nlinarith [F.γ_pos, Set.mem_Ioi.mp hx])).ne'
    calc (0 : ENNReal) < 1 := zero_lt_one
      _ = (F.service i : Measure ℝ) (Set.Ioi 0) := by
          have hc : (Set.Iic (0 : ℝ))ᶜ = Set.Ioi 0 := Set.compl_Iic
          rw [← hc, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
            F.service_pos i, tsub_zero]
      _ ≤ (F.service i : Measure ℝ) (Function.support (fun x : ℝ => 1 - Real.exp (-F.γ * x))) :=
          measure_mono hsub_set
  rw [integral_sub (integrable_const 1) (integrable_exp_service F i),
    integral_const, probReal_univ, one_smul] at hsub
  unfold phi
  linarith

private noncomputable def aVal (i : Fin n) : ℝ := F.reward i * phi F i
private noncomputable def cVal (i : Fin n) : ℝ := F.γ⁻¹ * (1 - phi F i)
private noncomputable def wVal (lam : ℝ) (i : Fin n) : ℝ := aVal F i - lam * cVal F i

private lemma aVal_pos (i : Fin n) : 0 < aVal F i :=
  mul_pos (F.reward_pos i) (phi_pos F i)

private lemma cVal_pos (i : Fin n) : 0 < cVal F i :=
  mul_pos (inv_pos.mpr F.γ_pos) (sub_pos.mpr (phi_lt_one F i))

end MeasureBasics

/-! ### Section 2: Coordinate splitting & Fubini on `serviceLaw F` -/

section ProductSplitting

variable {n : ℕ}

private noncomputable def subLaw (F : JobFamily n) (S : Finset (Fin n)) :
    Measure ({i : Fin n // i ∈ S} → ℝ) :=
  @Measure.pi {i : Fin n // i ∈ S} (fun _ => ℝ) (Subtype.fintype (· ∈ S)) _
    (fun i => (F.service i.1 : Measure ℝ))

private noncomputable def complLaw (F : JobFamily n) (S : Finset (Fin n)) :
    Measure ({i : Fin n // i ∉ S} → ℝ) :=
  @Measure.pi {i : Fin n // i ∉ S} (fun _ => ℝ) (Subtype.fintype (· ∉ S)) _
    (fun i => (F.service i.1 : Measure ℝ))

instance instIsProbSubLaw {F : JobFamily n} {S : Finset (Fin n)} :
    IsProbabilityMeasure (subLaw F S) := by
  unfold subLaw
  exact @Measure.pi.instIsProbabilityMeasure _ _ (Subtype.fintype (· ∈ S)) _ _ _

instance instIsProbComplLaw {F : JobFamily n} {S : Finset (Fin n)} :
    IsProbabilityMeasure (complLaw F S) := by
  unfold complLaw
  exact @Measure.pi.instIsProbabilityMeasure _ _ (Subtype.fintype (· ∉ S)) _ _ _

instance instIsFiniteSubLaw {F : JobFamily n} {S : Finset (Fin n)} :
    IsFiniteMeasure (subLaw F S) :=
  ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩

instance instIsFiniteComplLaw {F : JobFamily n} {S : Finset (Fin n)} :
    IsFiniteMeasure (complLaw F S) :=
  ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩

instance instSFiniteSubLaw {F : JobFamily n} {S : Finset (Fin n)} :
    SFinite (subLaw F S) :=
  @instSFiniteOfSigmaFinite _ _ (subLaw F S) (IsFiniteMeasure.toSigmaFinite (subLaw F S))

instance instSFiniteComplLaw {F : JobFamily n} {S : Finset (Fin n)} :
    SFinite (complLaw F S) :=
  @instSFiniteOfSigmaFinite _ _ (complLaw F S) (IsFiniteMeasure.toSigmaFinite (complLaw F S))

private def splitEquiv (S : Finset (Fin n)) :
    (Fin n → ℝ) ≃ᵐ ({i : Fin n // i ∈ S} → ℝ) × ({i : Fin n // i ∉ S} → ℝ) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (· ∈ S)

private lemma measurePreserving_split (F : JobFamily n) (S : Finset (Fin n)) :
    MeasurePreserving (splitEquiv S) (serviceLaw F) ((subLaw F S).prod (complLaw F S)) := by
  unfold splitEquiv serviceLaw subLaw complLaw
  exact measurePreserving_piEquivPiSubtypeProd (fun i => (F.service i : Measure ℝ)) (· ∈ S)

private lemma splitEquiv_symm_mem {S : Finset (Fin n)}
    (u : {i : Fin n // i ∈ S} → ℝ) (v : {i : Fin n // i ∉ S} → ℝ)
    {i : Fin n} (hi : i ∈ S) :
    (splitEquiv S).symm (u, v) i = u ⟨i, hi⟩ := by
  simp [splitEquiv, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

private lemma splitEquiv_symm_not_mem {S : Finset (Fin n)}
    (u : {i : Fin n // i ∈ S} → ℝ) (v : {i : Fin n // i ∉ S} → ℝ)
    {i : Fin n} (hi : i ∉ S) :
    (splitEquiv S).symm (u, v) i = v ⟨i, hi⟩ := by
  simp [splitEquiv, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

private lemma integral_mul_coord_of_indep (F : JobFamily n) (j : Fin n) {f : (Fin n → ℝ) → ℝ}
    {ψ : ℝ → ℝ}
    (_hf : Integrable f (serviceLaw F))
    (hf_indep : ∀ ω ω' : Fin n → ℝ, (∀ i, i ≠ j → ω i = ω' i) → f ω = f ω')
    (hψ : Integrable ψ (F.service j : Measure ℝ)) :
    ∫ ω, f ω * ψ (ω j) ∂serviceLaw F =
      (∫ ω, f ω ∂serviceLaw F) * (∫ x, ψ x ∂(F.service j : Measure ℝ)) := by
  let S : Finset (Fin n) := {j}
  have hmp := measurePreserving_split F S
  have hmp_symm := hmp.symm
  let u₀ : {i : Fin n // i ∈ S} → ℝ := fun _ => 0
  let g : ({i : Fin n // i ∉ S} → ℝ) → ℝ := fun v => f ((splitEquiv S).symm (u₀, v))
  have hf_eq : ∀ u v, f ((splitEquiv S).symm (u, v)) = g v := by
    intro u v
    apply hf_indep
    intro i hi
    have hiS : i ∉ S := by simp [S, hi]
    rw [splitEquiv_symm_not_mem u v hiS, splitEquiv_symm_not_mem u₀ v hiS]
  have hjS : j ∈ S := by simp [S]
  have hψ_eq : ∀ u v, ψ ((splitEquiv S).symm (u, v) j) = ψ (u ⟨j, hjS⟩) := by
    intro u v
    rw [splitEquiv_symm_mem u v hjS]
  have h1 : ∫ ω, f ω * ψ (ω j) ∂serviceLaw F =
      ∫ p : ({i : Fin n // i ∈ S} → ℝ) × ({i : Fin n // i ∉ S} → ℝ),
        ψ (p.1 ⟨j, hjS⟩) * g p.2 ∂((subLaw F S).prod (complLaw F S)) := by
    rw [← hmp_symm.integral_comp']
    congr 1; ext ⟨u, v⟩
    rw [hf_eq u v, hψ_eq u v, mul_comm]
  rw [h1, integral_prod_mul (f := fun u : {i : Fin n // i ∈ S} → ℝ => ψ (u ⟨j, hjS⟩)) (g := g)]
  have heval : MeasurePreserving (Function.eval ⟨j, hjS⟩) (subLaw F S) (F.service j : Measure ℝ) := by
    unfold subLaw
    exact @measurePreserving_eval {i : Fin n // i ∈ S} (fun _ => ℝ) (Subtype.fintype (· ∈ S)) _
      (fun i => (F.service i.1 : Measure ℝ)) _ ⟨j, hjS⟩
  have hI1 : ∫ u, ψ (u ⟨j, hjS⟩) ∂subLaw F S = ∫ x, ψ x ∂(F.service j : Measure ℝ) := by
    rw [← heval.map_eq, integral_map heval.measurable.aemeasurable
      (by rw [heval.map_eq]; exact hψ.aestronglyMeasurable)]
  have hI2 : ∫ v, g v ∂complLaw F S = ∫ ω, f ω ∂serviceLaw F := by
    rw [← hmp_symm.integral_comp']
    have : ∫ p : ({i : Fin n // i ∈ S} → ℝ) × ({i : Fin n // i ∉ S} → ℝ),
        f ((splitEquiv S).symm p) ∂((subLaw F S).prod (complLaw F S)) =
      ∫ p : ({i : Fin n // i ∈ S} → ℝ) × ({i : Fin n // i ∉ S} → ℝ),
        (1 : ℝ) * g p.2 ∂((subLaw F S).prod (complLaw F S)) := by
      congr 1; ext ⟨u, v⟩; rw [one_mul, hf_eq u v]
    rw [this, integral_prod_mul (f := fun _ : {i : Fin n // i ∈ S} → ℝ => (1 : ℝ)) (g := g),
      integral_const, probReal_univ, one_smul, one_mul]
  rw [hI1, hI2, mul_comm]

end ProductSplitting

/-! ### Section 3: Pure combinatorial DP and the Master Lemma -/

section CombinatorialDP

variable {n : ℕ} (F : JobFamily n)

private noncomputable def availFinset (D : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsAvailable F D)

private lemma mem_availFinset {D : Finset (Fin n)} {j : Fin n} :
    j ∈ availFinset F D ↔ IsAvailable F D j := by
  classical
  simp [availFinset]

private lemma availFinset_nonempty {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    (availFinset F D).Nonempty := by
  have hne : (Set.univ \ (D : Set (Fin n))).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
    apply hD
    ext x
    simp only [Finset.mem_univ, iff_true]
    exact h (Set.mem_univ x)
  have htrans : IsTrans (Fin n) (Relation.TransGen F.prec) :=
    ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩
  have hirrefl : Std.Irrefl (Relation.TransGen F.prec) := ⟨F.prec_acyclic⟩
  have hwf : WellFounded (Relation.TransGen F.prec) :=
    Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen F.prec)
  obtain ⟨j, hj, hmin⟩ := hwf.has_min (Set.univ \ (D : Set (Fin n))) hne
  refine ⟨j, (mem_availFinset F).mpr ⟨?_, ?_⟩⟩
  · exact hj.2
  · intro i hij
    by_contra hi
    exact hmin i ⟨Set.mem_univ i, hi⟩ (Relation.TransGen.single hij)

private lemma card_sub_insert_lt {D : Finset (Fin n)} {j : Fin n} (hj : j ∉ D) :
    n - (insert j D).card < n - D.card := by
  rw [Finset.card_insert_of_notMem hj]
  have hlt : D.card < n := by
    have hle : (insert j D).card ≤ n := by
      simpa using (insert j D).card_le_univ
    rw [Finset.card_insert_of_notMem hj] at hle
    omega
  omega

private noncomputable def UVal (w φ : Fin n → ℝ) (D : Finset (Fin n)) : ℝ :=
  if hD : D = Finset.univ then 0
  else (availFinset F D).attach.sup' (availFinset_nonempty F hD).attach
    fun j => w j.1 + φ j.1 * UVal w φ (insert j.1 D)
termination_by n - D.card
decreasing_by
  exact card_sub_insert_lt ((mem_availFinset F).mp j.2).1

private lemma UVal_univ (w φ : Fin n → ℝ) : UVal F w φ Finset.univ = 0 := by
  rw [UVal]; simp

private lemma le_UVal (w φ : Fin n → ℝ) {D : Finset (Fin n)} {j : Fin n}
    (hj : IsAvailable F D j) :
    w j + φ j * UVal F w φ (insert j D) ≤ UVal F w φ D := by
  have hD : D ≠ Finset.univ := fun h => hj.1 (by rw [h]; exact Finset.mem_univ j)
  conv_rhs => rw [UVal, dif_neg hD]
  have hj' : ⟨j, (mem_availFinset F).mpr hj⟩ ∈ (availFinset F D).attach := Finset.mem_attach _ _
  exact Finset.le_sup' (f := fun x : {x // x ∈ availFinset F D} =>
    w x.1 + φ x.1 * UVal F w φ (insert x.1 D)) hj'

private lemma exists_UVal_eq (w φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    ∃ j : Fin n, IsAvailable F D j ∧ UVal F w φ D = w j + φ j * UVal F w φ (insert j D) := by
  obtain ⟨⟨j, hj⟩, _, heq⟩ := Finset.exists_mem_eq_sup' (availFinset_nonempty F hD).attach
    (fun x : {x // x ∈ availFinset F D} => w x.1 + φ x.1 * UVal F w φ (insert x.1 D))
  refine ⟨j, (mem_availFinset F).mp hj, ?_⟩
  conv_lhs => rw [UVal, dif_neg hD]
  exact heq

private noncomputable def GVal (w φ : Fin n → ℝ) (D : Finset (Fin n)) : ℝ :=
  if hD : D = Finset.univ then 0
  else max 0 ((availFinset F D).attach.sup' (availFinset_nonempty F hD).attach
    fun j => w j.1 + φ j.1 * GVal w φ (insert j.1 D))
termination_by n - D.card
decreasing_by
  exact card_sub_insert_lt ((mem_availFinset F).mp j.2).1

private noncomputable def HVal (w φ : Fin n → ℝ) (D : Finset (Fin n)) (hD : D ≠ Finset.univ) : ℝ :=
  (availFinset F D).sup' (availFinset_nonempty F hD)
    fun j => w j + φ j * GVal F w φ (insert j D)

private lemma GVal_univ (w φ : Fin n → ℝ) : GVal F w φ Finset.univ = 0 := by
  rw [GVal]; simp

private lemma GVal_nonneg (w φ : Fin n → ℝ) (D : Finset (Fin n)) : 0 ≤ GVal F w φ D := by
  rw [GVal]
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

private lemma GVal_eq_max_HVal (w φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    GVal F w φ D = max 0 (HVal F w φ D hD) := by
  rw [GVal, dif_neg hD]
  congr 1
  unfold HVal
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
    exact Finset.le_sup' (f := fun j => w j + φ j * GVal F w φ (insert j D)) hj
  · refine Finset.sup'_le _ _ fun j hj => ?_
    exact Finset.le_sup' (f := fun x : {x // x ∈ availFinset F D} =>
      w x.1 + φ x.1 * GVal F w φ (insert x.1 D)) (Finset.mem_attach _ ⟨j, hj⟩)

private lemma le_HVal (w φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) {j : Fin n}
    (hj : IsAvailable F D j) :
    w j + φ j * GVal F w φ (insert j D) ≤ HVal F w φ D hD :=
  Finset.le_sup' (f := fun j => w j + φ j * GVal F w φ (insert j D)) ((mem_availFinset F).mpr hj)

private lemma le_GVal (w φ : Fin n → ℝ) {D : Finset (Fin n)} {j : Fin n}
    (hj : IsAvailable F D j) :
    w j + φ j * GVal F w φ (insert j D) ≤ GVal F w φ D := by
  have hD : D ≠ Finset.univ := fun h => hj.1 (by rw [h]; exact Finset.mem_univ j)
  rw [GVal_eq_max_HVal F w φ hD]
  exact le_trans (le_HVal F w φ hD hj) (le_max_right _ _)

private lemma exists_HVal_eq (w φ : Fin n → ℝ) {D : Finset (Fin n)} (hD : D ≠ Finset.univ) :
    ∃ j : Fin n, IsAvailable F D j ∧ HVal F w φ D hD = w j + φ j * GVal F w φ (insert j D) := by
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (availFinset_nonempty F hD)
    (fun j => w j + φ j * GVal F w φ (insert j D))
  exact ⟨j, (mem_availFinset F).mp hj, heq⟩

private lemma exists_GVal_eq_of_pos (w φ : Fin n → ℝ) {D : Finset (Fin n)}
    (hpos : 0 < GVal F w φ D) :
    ∃ j : Fin n, IsAvailable F D j ∧ GVal F w φ D = w j + φ j * GVal F w φ (insert j D) := by
  have hD : D ≠ Finset.univ := by
    intro h; rw [h, GVal_univ] at hpos; exact lt_irrefl _ hpos
  rw [GVal_eq_max_HVal F w φ hD] at hpos ⊢
  have hH : 0 < HVal F w φ D hD := by
    by_contra hle; push Not at hle
    rw [max_eq_left hle] at hpos; exact lt_irrefl _ hpos
  rw [max_eq_right hH.le]
  exact exists_HVal_eq F w φ hD

private noncomputable def GIn (w φ : Fin n → ℝ) (T D : Finset (Fin n)) : ℝ :=
  if hne : (availFinset F D ∩ T).Nonempty then
    max 0 ((availFinset F D ∩ T).attach.sup' hne.attach
      fun j => w j.1 + φ j.1 * GIn w φ T (insert j.1 D))
  else 0
termination_by n - D.card
decreasing_by
  exact card_sub_insert_lt ((mem_availFinset F).mp (Finset.mem_inter.mp j.2).1).1

private lemma GIn_nonneg (w φ : Fin n → ℝ) (T D : Finset (Fin n)) : 0 ≤ GIn F w φ T D := by
  rw [GIn]
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

private lemma GIn_empty (w φ : Fin n → ℝ) (D : Finset (Fin n)) : GIn F w φ ∅ D = 0 := by
  rw [GIn]; simp

private lemma le_GIn (w φ : Fin n → ℝ) {T D : Finset (Fin n)} {j : Fin n}
    (hj : IsAvailable F D j) (hjT : j ∈ T) :
    w j + φ j * GIn F w φ T (insert j D) ≤ GIn F w φ T D := by
  have hmem : j ∈ availFinset F D ∩ T := Finset.mem_inter.mpr ⟨(mem_availFinset F).mpr hj, hjT⟩
  have hne : (availFinset F D ∩ T).Nonempty := ⟨j, hmem⟩
  conv_rhs => rw [GIn, dif_pos hne]
  exact le_trans (Finset.le_sup' (f := fun x : {x // x ∈ availFinset F D ∩ T} =>
    w x.1 + φ x.1 * GIn F w φ T (insert x.1 D)) (Finset.mem_attach _ ⟨j, hmem⟩)) (le_max_right _ _)

private lemma GIn_le_GVal (w φ : Fin n → ℝ) (hφ0 : ∀ i, 0 ≤ φ i) (T : Finset (Fin n)) :
    ∀ D : Finset (Fin n), GIn F w φ T D ≤ GVal F w φ D := by
  intro D
  induction hk : n - D.card using Nat.strong_induction_on generalizing D with
  | h k ih =>
    rw [GIn]
    split_ifs with hne
    · refine max_le (GVal_nonneg F w φ D) ?_
      refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
      have hjAv : IsAvailable F D j := (mem_availFinset F).mp (Finset.mem_inter.mp hj).1
      have hlt : n - (insert j D).card < k := by rw [← hk]; exact card_sub_insert_lt hjAv.1
      have hih := ih (n - (insert j D).card) hlt (insert j D) rfl
      calc w j + φ j * GIn F w φ T (insert j D)
          ≤ w j + φ j * GVal F w φ (insert j D) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hih (hφ0 j))
        _ ≤ GVal F w φ D := le_GVal F w φ hjAv
    · exact GVal_nonneg F w φ D

private lemma GIn_erase_of_mem (w φ : Fin n → ℝ) (T : Finset (Fin n)) {x : Fin n} :
    ∀ D : Finset (Fin n), x ∈ D → GIn F w φ (T.erase x) D = GIn F w φ T D := by
  intro D hxD
  induction hk : n - D.card using Nat.strong_induction_on generalizing D with
  | h k ih =>
    have heqSet : availFinset F D ∩ T.erase x = availFinset F D ∩ T := by
      ext j
      simp only [Finset.mem_inter, mem_availFinset, Finset.mem_erase]
      constructor
      · rintro ⟨hj, _, hjT⟩; exact ⟨hj, hjT⟩
      · rintro ⟨hj, hjT⟩
        exact ⟨hj, fun h => hj.1 (h ▸ hxD), hjT⟩
    conv_lhs => rw [GIn]
    conv_rhs => rw [GIn]
    by_cases h1 : (availFinset F D ∩ T.erase x).Nonempty
    · have h2 : (availFinset F D ∩ T).Nonempty := heqSet ▸ h1
      rw [dif_pos h1, dif_pos h2]
      congr 1
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
        have hj' : j ∈ availFinset F D ∩ T := heqSet ▸ hj
        have hjAv : IsAvailable F D j := (mem_availFinset F).mp (Finset.mem_inter.mp hj').1
        have hlt : n - (insert j D).card < k := by rw [← hk]; exact card_sub_insert_lt hjAv.1
        dsimp only
        rw [ih _ hlt (insert j D) (Finset.mem_insert_of_mem hxD) rfl]
        exact Finset.le_sup' (f := fun y : {y // y ∈ availFinset F D ∩ T} =>
          w y.1 + φ y.1 * GIn F w φ T (insert y.1 D)) (Finset.mem_attach _ ⟨j, hj'⟩)
      · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
        have hj' : j ∈ availFinset F D ∩ T.erase x := heqSet.symm ▸ hj
        have hjAv : IsAvailable F D j := (mem_availFinset F).mp (Finset.mem_inter.mp hj).1
        have hlt : n - (insert j D).card < k := by rw [← hk]; exact card_sub_insert_lt hjAv.1
        dsimp only
        rw [← ih _ hlt (insert j D) (Finset.mem_insert_of_mem hxD) rfl]
        exact Finset.le_sup' (f := fun y : {y // y ∈ availFinset F D ∩ T.erase x} =>
          w y.1 + φ y.1 * GIn F w φ (T.erase x) (insert y.1 D)) (Finset.mem_attach _ ⟨j, hj'⟩)
    · have h2 : ¬ (availFinset F D ∩ T).Nonempty := heqSet ▸ h1
      rw [dif_neg h1, dif_neg h2]

private lemma GIn_insert_of_no_prec (w φ : Fin n → ℝ) (T : Finset (Fin n)) {x : Fin n}
    (hxT : x ∉ T) (hno : ∀ y ∈ T, ¬ F.prec x y) :
    ∀ D : Finset (Fin n), GIn F w φ T (insert x D) = GIn F w φ T D := by
  intro D
  induction hk : n - D.card using Nat.strong_induction_on generalizing D with
  | h k ih =>
    have heqSet : availFinset F (insert x D) ∩ T = availFinset F D ∩ T := by
      ext j
      simp only [Finset.mem_inter, mem_availFinset, IsAvailable, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨⟨_, hjD⟩, hprec⟩, hjT⟩
        refine ⟨⟨hjD, fun i hij => ?_⟩, hjT⟩
        rcases hprec i hij with rfl | hiD
        · exact absurd hij (hno j hjT)
        · exact hiD
      · rintro ⟨⟨hjD, hprec⟩, hjT⟩
        refine ⟨⟨⟨fun h => hxT (h ▸ hjT), hjD⟩, fun i hij => Or.inr (hprec i hij)⟩, hjT⟩
    conv_lhs => rw [GIn]
    conv_rhs => rw [GIn]
    by_cases h1 : (availFinset F (insert x D) ∩ T).Nonempty
    · have h2 : (availFinset F D ∩ T).Nonempty := heqSet ▸ h1
      rw [dif_pos h1, dif_pos h2]
      congr 1
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
        have hj' : j ∈ availFinset F D ∩ T := heqSet ▸ hj
        have hjAv : IsAvailable F D j := (mem_availFinset F).mp (Finset.mem_inter.mp hj').1
        have hlt : n - (insert j D).card < k := by rw [← hk]; exact card_sub_insert_lt hjAv.1
        dsimp only
        rw [Finset.insert_comm j x D, ih _ hlt (insert j D) rfl]
        exact Finset.le_sup' (f := fun y : {y // y ∈ availFinset F D ∩ T} =>
          w y.1 + φ y.1 * GIn F w φ T (insert y.1 D)) (Finset.mem_attach _ ⟨j, hj'⟩)
      · refine Finset.sup'_le _ _ fun ⟨j, hj⟩ _ => ?_
        have hj' : j ∈ availFinset F (insert x D) ∩ T := heqSet.symm ▸ hj
        have hjAv : IsAvailable F D j := (mem_availFinset F).mp (Finset.mem_inter.mp hj).1
        have hlt : n - (insert j D).card < k := by rw [← hk]; exact card_sub_insert_lt hjAv.1
        dsimp only
        rw [← ih _ hlt (insert j D) rfl, ← Finset.insert_comm j x D]
        exact Finset.le_sup' (f := fun y : {y // y ∈ availFinset F (insert x D) ∩ T} =>
          w y.1 + φ y.1 * GIn F w φ T (insert y.1 (insert x D))) (Finset.mem_attach _ ⟨j, hj'⟩)
    · have h2 : ¬ (availFinset F D ∩ T).Nonempty := heqSet ▸ h1
      rw [dif_neg h1, dif_neg h2]

private def IsLowerIn (D T : Finset (Fin n)) : Prop :=
  Disjoint T D ∧ ∀ y ∈ T, ∀ z : Fin n, z ∉ D → F.prec z y → z ∈ T

private def prodPhi (φ : Fin n → ℝ) (T : Finset (Fin n)) : ℝ :=
  ∏ i ∈ T, φ i

private lemma prodPhi_nonneg {φ : Fin n → ℝ} (hφ0 : ∀ i, 0 ≤ φ i) (T : Finset (Fin n)) :
    0 ≤ prodPhi φ T :=
  Finset.prod_nonneg fun i _ => hφ0 i

private lemma prodPhi_le_one {φ : Fin n → ℝ} (hφ0 : ∀ i, 0 ≤ φ i) (hφ1 : ∀ i, φ i ≤ 1)
    (T : Finset (Fin n)) : prodPhi φ T ≤ 1 :=
  Finset.prod_le_one (fun i _ => hφ0 i) (fun i _ => hφ1 i)

private lemma master_lower_set_bound (w φ : Fin n → ℝ) (hφ0 : ∀ i, 0 ≤ φ i) (hφ1 : ∀ i, φ i ≤ 1) :
    ∀ (D T : Finset (Fin n)), IsLowerIn F D T →
      UVal F w φ D - prodPhi φ T * UVal F w φ (D ∪ T) ≤
        (1 - prodPhi φ T) * GVal F w φ D + prodPhi φ T * GIn F w φ T D := by
  intro D
  induction hk : n - D.card using Nat.strong_induction_on generalizing D with
  | h k ih =>
    intro T hT
    by_cases hTe : T = ∅
    · subst hTe
      simp [prodPhi, GIn_empty]
    · have hD : D ≠ Finset.univ := by
        intro h
        apply hTe
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        exact Finset.disjoint_left.mp hT.1 hy (h ▸ Finset.mem_univ y)
      obtain ⟨x, hxAv, hUeq⟩ := exists_UVal_eq F w φ hD
      have hlt : n - (insert x D).card < k := by rw [← hk]; exact card_sub_insert_lt hxAv.1
      by_cases hxT : x ∈ T
      · let T' := T.erase x
        have hT' : IsLowerIn F (insert x D) T' := by
          refine ⟨?_, ?_⟩
          · rw [Finset.disjoint_insert_right]
            exact ⟨Finset.notMem_erase x T, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hT.1⟩
          · intro y hy z hz hzy
            rw [Finset.mem_insert, not_or] at hz
            exact Finset.mem_erase.mpr ⟨hz.1, hT.2 y (Finset.mem_of_mem_erase hy) z hz.2 hzy⟩
        have hunion : insert x D ∪ T' = D ∪ T := by
          ext y
          simp only [Finset.mem_union, Finset.mem_insert, T', Finset.mem_erase]
          by_cases hyx : y = x
          · subst hyx; simp [hxT]
          · simp [hyx]
        have hprod : prodPhi φ T = φ x * prodPhi φ T' := by
          unfold prodPhi T'
          rw [← Finset.mul_prod_erase T φ hxT]
        have hih := ih _ hlt (insert x D) rfl T' hT'
        rw [hunion] at hih
        have hGIn_eq : GIn F w φ T' (insert x D) = GIn F w φ T (insert x D) :=
          GIn_erase_of_mem F w φ T (insert x D) (Finset.mem_insert_self x D)
        rw [hGIn_eq] at hih
        have hP0 : 0 ≤ prodPhi φ T' := prodPhi_nonneg hφ0 T'
        have hP1 : prodPhi φ T' ≤ 1 := prodPhi_le_one hφ0 hφ1 T'
        have h1 : w x + φ x * GVal F w φ (insert x D) ≤ GVal F w φ D := le_GVal F w φ hxAv
        have h2 : w x + φ x * GIn F w φ T (insert x D) ≤ GIn F w φ T D := le_GIn F w φ hxAv hxT
        have h3 : GIn F w φ T D ≤ GVal F w φ D := GIn_le_GVal F w φ hφ0 T D
        have hstep1 : UVal F w φ D - prodPhi φ T * UVal F w φ (D ∪ T) =
            w x + φ x * (UVal F w φ (insert x D) - prodPhi φ T' * UVal F w φ (D ∪ T)) := by
          rw [hUeq, hprod]; ring
        have hstep2 : w x + φ x * (UVal F w φ (insert x D) - prodPhi φ T' * UVal F w φ (D ∪ T)) ≤
            w x + φ x * ((1 - prodPhi φ T') * GVal F w φ (insert x D) +
              prodPhi φ T' * GIn F w φ T (insert x D)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hih (hφ0 x))
        have hstep3 : w x + φ x * ((1 - prodPhi φ T') * GVal F w φ (insert x D) +
              prodPhi φ T' * GIn F w φ T (insert x D)) =
            (1 - prodPhi φ T') * (w x + φ x * GVal F w φ (insert x D)) +
              prodPhi φ T' * (w x + φ x * GIn F w φ T (insert x D)) := by ring
        have hstep4 : (1 - prodPhi φ T') * (w x + φ x * GVal F w φ (insert x D)) +
              prodPhi φ T' * (w x + φ x * GIn F w φ T (insert x D)) ≤
            (1 - prodPhi φ T') * GVal F w φ D + prodPhi φ T' * GIn F w φ T D :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith))
            (mul_le_mul_of_nonneg_left h2 hP0)
        have hstep5 : (1 - prodPhi φ T') * GVal F w φ D + prodPhi φ T' * GIn F w φ T D ≤
            (1 - prodPhi φ T) * GVal F w φ D + prodPhi φ T * GIn F w φ T D := by
          rw [hprod]
          have hdiff : ((1 - φ x * prodPhi φ T') * GVal F w φ D +
              φ x * prodPhi φ T' * GIn F w φ T D) -
            ((1 - prodPhi φ T') * GVal F w φ D + prodPhi φ T' * GIn F w φ T D) =
            prodPhi φ T' * (1 - φ x) * (GVal F w φ D - GIn F w φ T D) := by ring
          have hnn : 0 ≤ prodPhi φ T' * (1 - φ x) * (GVal F w φ D - GIn F w φ T D) :=
            mul_nonneg (mul_nonneg hP0 (by linarith [hφ1 x])) (by linarith)
          linarith
        linarith
      · have hT' : IsLowerIn F (insert x D) T := by
          refine ⟨?_, ?_⟩
          · rw [Finset.disjoint_insert_right]
            exact ⟨hxT, hT.1⟩
          · intro y hy z hz hzy
            rw [Finset.mem_insert, not_or] at hz
            exact hT.2 y hy z hz.2 hzy
        have hno : ∀ y ∈ T, ¬ F.prec x y := fun y hy hxy =>
          hxT (hT.2 y hy x hxAv.1 hxy)
        have hxAvUT : IsAvailable F (D ∪ T) x := by
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_union, not_or]; exact ⟨hxAv.1, hxT⟩
          · intro i hix; exact Finset.mem_union_left T (hxAv.2 i hix)
        have hUUT : w x + φ x * UVal F w φ (insert x (D ∪ T)) ≤ UVal F w φ (D ∪ T) :=
          le_UVal F w φ hxAvUT
        have hunion : insert x (D ∪ T) = insert x D ∪ T := by
          ext y; simp
        rw [hunion] at hUUT
        have hih := ih _ hlt (insert x D) rfl T hT'
        have hGIn_eq : GIn F w φ T (insert x D) = GIn F w φ T D :=
          GIn_insert_of_no_prec F w φ T hxT hno D
        rw [hGIn_eq] at hih
        have hP0 : 0 ≤ prodPhi φ T := prodPhi_nonneg hφ0 T
        have hP1 : prodPhi φ T ≤ 1 := prodPhi_le_one hφ0 hφ1 T
        have h1 : w x + φ x * GVal F w φ (insert x D) ≤ GVal F w φ D := le_GVal F w φ hxAv
        have hGIn0 : 0 ≤ GIn F w φ T D := GIn_nonneg F w φ T D
        have hstep1 : UVal F w φ D - prodPhi φ T * UVal F w φ (D ∪ T) ≤
            (1 - prodPhi φ T) * w x +
              φ x * (UVal F w φ (insert x D) - prodPhi φ T * UVal F w φ (insert x D ∪ T)) := by
          have := mul_le_mul_of_nonneg_left hUUT hP0
          rw [hUeq]; linarith
        have hstep2 : (1 - prodPhi φ T) * w x +
              φ x * (UVal F w φ (insert x D) - prodPhi φ T * UVal F w φ (insert x D ∪ T)) ≤
            (1 - prodPhi φ T) * w x +
              φ x * ((1 - prodPhi φ T) * GVal F w φ (insert x D) +
                prodPhi φ T * GIn F w φ T D) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hih (hφ0 x))
        have hstep3 : (1 - prodPhi φ T) * w x +
              φ x * ((1 - prodPhi φ T) * GVal F w φ (insert x D) +
                prodPhi φ T * GIn F w φ T D) =
            (1 - prodPhi φ T) * (w x + φ x * GVal F w φ (insert x D)) +
              prodPhi φ T * (φ x * GIn F w φ T D) := by ring
        have hstep4 : (1 - prodPhi φ T) * (w x + φ x * GVal F w φ (insert x D)) +
              prodPhi φ T * (φ x * GIn F w φ T D) ≤
            (1 - prodPhi φ T) * GVal F w φ D + prodPhi φ T * GIn F w φ T D := by
          refine add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith)) ?_
          exact mul_le_mul_of_nonneg_left (by nlinarith [hφ1 x]) hP0
        linarith

private lemma UVal_sub_prod_le_GVal (w φ : Fin n → ℝ) (hφ0 : ∀ i, 0 ≤ φ i) (hφ1 : ∀ i, φ i ≤ 1)
    {D T : Finset (Fin n)} (hT : IsLowerIn F D T) :
    UVal F w φ D - prodPhi φ T * UVal F w φ (D ∪ T) ≤ GVal F w φ D := by
  have h1 := master_lower_set_bound F w φ hφ0 hφ1 D T hT
  have h2 := GIn_le_GVal F w φ hφ0 T D
  have hP0 := prodPhi_nonneg hφ0 T
  nlinarith

private lemma exists_zero_lower_set (w φ : Fin n → ℝ) (hφ0 : ∀ i, 0 ≤ φ i) :
    ∀ D : Finset (Fin n), ∃ S : Finset (Fin n), IsLowerIn F D S ∧
      GVal F w φ (D ∪ S) = 0 ∧
      GVal F w φ D - UVal F w φ D ≤ -(prodPhi φ S * UVal F w φ (D ∪ S)) := by
  intro D
  induction hk : n - D.card using Nat.strong_induction_on generalizing D with
  | h k ih =>
    by_cases hG0 : GVal F w φ D = 0
    · refine ⟨∅, ⟨Finset.disjoint_empty_left D, by simp⟩, by simpa using hG0, ?_⟩
      simp [prodPhi, hG0]
    · have hpos : 0 < GVal F w φ D := lt_of_le_of_ne (GVal_nonneg F w φ D) (Ne.symm hG0)
      obtain ⟨l, hlAv, hGeq⟩ := exists_GVal_eq_of_pos F w φ hpos
      have hUle : w l + φ l * UVal F w φ (insert l D) ≤ UVal F w φ D := le_UVal F w φ hlAv
      have hlt : n - (insert l D).card < k := by rw [← hk]; exact card_sub_insert_lt hlAv.1
      obtain ⟨S', hS'low, hS'zero, hS'ineq⟩ := ih _ hlt (insert l D) rfl
      refine ⟨insert l S', ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [Finset.disjoint_insert_left]
          exact ⟨hlAv.1, Finset.disjoint_of_subset_right (Finset.subset_insert l D) hS'low.1⟩
        · intro y hy z hz hzy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hyS'
          · exact absurd (hlAv.2 z hzy) hz
          · by_cases hzl : z = l
            · exact hzl ▸ Finset.mem_insert_self l S'
            · refine Finset.mem_insert_of_mem (hS'low.2 y hyS' z ?_ hzy)
              rw [Finset.mem_insert, not_or]; exact ⟨hzl, hz⟩
      · have hunion : D ∪ insert l S' = insert l D ∪ S' := by
          ext y; simp
        rw [hunion]; exact hS'zero
      · have hunion : D ∪ insert l S' = insert l D ∪ S' := by
          ext y; simp
        have hlS' : l ∉ S' := fun hl =>
          Finset.disjoint_left.mp hS'low.1 hl (Finset.mem_insert_self l D)
        have hprod : prodPhi φ (insert l S') = φ l * prodPhi φ S' := by
          unfold prodPhi; rw [Finset.prod_insert hlS']
        rw [hunion, hprod]
        have h1 : GVal F w φ D - UVal F w φ D ≤
            φ l * (GVal F w φ (insert l D) - UVal F w φ (insert l D)) := by
          rw [hGeq]; linarith
        have h2 := mul_le_mul_of_nonneg_left hS'ineq (hφ0 l)
        linarith

private lemma delta_step (w φ : Fin n → ℝ) (hφ0 : ∀ i, 0 ≤ φ i) (hφ1 : ∀ i, φ i ≤ 1)
    {D : Finset (Fin n)} {j : Fin n} (hj : IsAvailable F D j) :
    φ j * (GVal F w φ (insert j D) - UVal F w φ (insert j D)) ≤
      GVal F w φ D - UVal F w φ D := by
  obtain ⟨S, hSlow, _, hSineq⟩ := exists_zero_lower_set F w φ hφ0 (insert j D)
  let T := insert j S
  have hTlow : IsLowerIn F D T := by
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_insert_left]
      exact ⟨hj.1, Finset.disjoint_of_subset_right (Finset.subset_insert j D) hSlow.1⟩
    · intro y hy z hz hzy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hyS
      · exact absurd (hj.2 z hzy) hz
      · by_cases hzj : z = j
        · exact hzj ▸ Finset.mem_insert_self j S
        · refine Finset.mem_insert_of_mem (hSlow.2 y hyS z ?_ hzy)
          rw [Finset.mem_insert, not_or]; exact ⟨hzj, hz⟩
  have hjS : j ∉ S := fun h => Finset.disjoint_left.mp hSlow.1 h (Finset.mem_insert_self j D)
  have hunion : D ∪ T = insert j D ∪ S := by ext y; simp [T]
  have hprod : prodPhi φ T = φ j * prodPhi φ S := by
    unfold prodPhi T; rw [Finset.prod_insert hjS]
  have hmaster := UVal_sub_prod_le_GVal F w φ hφ0 hφ1 hTlow
  rw [hunion, hprod] at hmaster
  have hmul := mul_le_mul_of_nonneg_left hSineq (hφ0 j)
  linarith

private lemma UVal_wVal (lam : ℝ) :
    ∀ D : Finset (Fin n),
      UVal F (wVal F lam) (phi F) D =
        UVal F (aVal F) (phi F) D - lam * F.γ⁻¹ * (1 - prodPhi (phi F) Dᶜ) := by
  intro D
  induction hk : n - D.card using Nat.strong_induction_on generalizing D with
  | h k ih =>
    by_cases hD : D = Finset.univ
    · subst hD; simp [UVal_univ, prodPhi]
    · have hshift : ∀ j ∈ availFinset F D,
          wVal F lam j + phi F j * UVal F (wVal F lam) (phi F) (insert j D) =
            (aVal F j + phi F j * UVal F (aVal F) (phi F) (insert j D)) -
              lam * F.γ⁻¹ * (1 - prodPhi (phi F) Dᶜ) := by
        intro j hj
        have hjAv : IsAvailable F D j := (mem_availFinset F).mp hj
        have hlt : n - (insert j D).card < k := by rw [← hk]; exact card_sub_insert_lt hjAv.1
        rw [ih _ hlt (insert j D) rfl]
        have hcompl : Dᶜ = insert j (insert j D)ᶜ := by
          ext i; simp only [Finset.mem_compl, Finset.mem_insert, not_or]
          by_cases hij : i = j
          · subst hij; simp [hjAv.1]
          · simp [hij]
        have hjnot : j ∉ (insert j D)ᶜ := by simp
        have hprod : prodPhi (phi F) Dᶜ = phi F j * prodPhi (phi F) (insert j D)ᶜ := by
          unfold prodPhi; rw [hcompl, Finset.prod_insert hjnot]
        unfold wVal cVal
        rw [hprod]
        ring
      apply le_antisymm
      · obtain ⟨j, hjAv, hEq⟩ := exists_UVal_eq F (wVal F lam) (phi F) hD
        rw [hEq, hshift j ((mem_availFinset F).mpr hjAv)]
        linarith [le_UVal F (aVal F) (phi F) hjAv]
      · obtain ⟨j, hjAv, hEq⟩ := exists_UVal_eq F (aVal F) (phi F) hD
        have hle := le_UVal F (wVal F lam) (phi F) hjAv
        rw [hshift j ((mem_availFinset F).mpr hjAv)] at hle
        linarith

private noncomputable def deltaTilde (lam : ℝ) (D : Finset (Fin n)) : ℝ :=
  GVal F (wVal F lam) (phi F) D - UVal F (aVal F) (phi F) D + lam * F.γ⁻¹

private lemma deltaTilde_step (lam : ℝ) {D : Finset (Fin n)} {j : Fin n}
    (hj : IsAvailable F D j) :
    phi F j * deltaTilde F lam (insert j D) ≤ deltaTilde F lam D := by
  have hφ0 : ∀ i, 0 ≤ phi F i := fun i => (phi_pos F i).le
  have hφ1 : ∀ i, phi F i ≤ 1 := fun i => (phi_lt_one F i).le
  have hds := delta_step F (wVal F lam) (phi F) hφ0 hφ1 hj
  rw [UVal_wVal F lam (insert j D), UVal_wVal F lam D] at hds
  have hcompl : Dᶜ = insert j (insert j D)ᶜ := by
    ext i; simp only [Finset.mem_compl, Finset.mem_insert, not_or]
    by_cases hij : i = j
    · subst hij; simp [hj.1]
    · simp [hij]
  have hjnot : j ∉ (insert j D)ᶜ := by simp
  have hprod : prodPhi (phi F) Dᶜ = phi F j * prodPhi (phi F) (insert j D)ᶜ := by
    unfold prodPhi; rw [hcompl, Finset.prod_insert hjnot]
  unfold deltaTilde
  rw [hprod] at hds
  linarith

end CombinatorialDP

/-! ### Section 4: Policy / Stage structure, measurability, integrability, and telescoping -/

section PolicyStage

variable {n : ℕ}

private lemma history_elapsed_nil : History.elapsed ([] : History n) = 0 := rfl

private lemma history_elapsed_append (h₁ h₂ : History n) :
    (h₁ ++ h₂).elapsed = h₁.elapsed + h₂.elapsed := by
  simp [History.elapsed, List.map_append, List.sum_append]

private lemma history_jobs_nil : History.jobs ([] : History n) = ∅ := by
  simp [History.jobs]

private lemma history_jobs_append (h₁ h₂ : History n) :
    (h₁ ++ h₂).jobs = h₁.jobs ∪ h₂.jobs := by
  simp [History.jobs, List.map_append, List.toFinset_append]

private lemma hist_length (π : Policy n) (ω : Fin n → ℝ) :
    ∀ k : ℕ, (π.hist ω k).length = k
  | 0 => rfl
  | k + 1 => by simp [Policy.hist, hist_length π ω k]

private lemma hist_jobs_zero (π : Policy n) (ω : Fin n → ℝ) :
    (π.hist ω 0).jobs = ∅ := by
  simp [Policy.hist, History.jobs]

private lemma hist_jobs_succ (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    (π.hist ω (k + 1)).jobs = insert (π.job ω k) (π.hist ω k).jobs := by
  simp [Policy.hist, Policy.job, History.jobs, Finset.union_comm]

private lemma hist_jobs_eq_image (π : Policy n) (ω : Fin n → ℝ) :
    ∀ k : ℕ, (π.hist ω k).jobs = (Finset.range k).image (π.job ω)
  | 0 => by simp [hist_jobs_zero]
  | k + 1 => by
    rw [hist_jobs_succ, Finset.range_add_one, Finset.image_insert, hist_jobs_eq_image π ω k]

private lemma startTime_zero (π : Policy n) (ω : Fin n → ℝ) :
    π.startTime ω 0 = 0 := rfl

private lemma completionTime_eq_startTime_succ (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    π.completionTime ω k = π.startTime ω (k + 1) := rfl

private lemma completionTime_eq_add (π : Policy n) (ω : Fin n → ℝ) (k : ℕ) :
    π.completionTime ω k = π.startTime ω k + ω (π.job ω k) := by
  simp [Policy.completionTime, Policy.startTime, Policy.hist, Policy.job, History.elapsed]

private lemma startTime_nonneg (π : Policy n) {ω : Fin n → ℝ} (hpos : ∀ i, 0 < ω i) :
    ∀ k : ℕ, 0 ≤ π.startTime ω k
  | 0 => le_rfl
  | k + 1 => by
    rw [← completionTime_eq_startTime_succ, completionTime_eq_add]
    linarith [startTime_nonneg π hpos k, hpos (π.job ω k)]

private lemma completionTime_pos (π : Policy n) {ω : Fin n → ℝ} (hpos : ∀ i, 0 < ω i) (k : ℕ) :
    0 < π.completionTime ω k := by
  rw [completionTime_eq_add]
  linarith [startTime_nonneg π hpos k, hpos (π.job ω k)]

private lemma hist_congr_of_agree (π : Policy n) {ω ω' : Fin n → ℝ} :
    ∀ {k : ℕ}, (∀ i ∈ (π.hist ω k).jobs, ω i = ω' i) → π.hist ω k = π.hist ω' k
  | 0, _ => rfl
  | k + 1, h => by
    have hk : ∀ i ∈ (π.hist ω k).jobs, ω i = ω' i := fun i hi =>
      h i (by rw [hist_jobs_succ]; exact Finset.mem_insert_of_mem hi)
    have hprev := hist_congr_of_agree π hk
    have hj : ω (π.job ω k) = ω' (π.job ω k) :=
      h (π.job ω k) (by rw [hist_jobs_succ]; exact Finset.mem_insert_self _ _)
    simp only [Policy.hist, hprev]
    congr 2
    have : π.next (π.hist ω' k) = π.job ω k := by rw [← hprev]; rfl
    rw [this, hj]

private lemma numRemaining_eq_zero_iff (A : Finset (Fin n)) :
    numRemaining A = 0 ↔ A = Finset.univ := by
  unfold numRemaining
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  constructor
  · intro h
    exact Finset.eq_univ_of_card A (by simp; omega)
  · intro h; subst h; simp

private lemma feasible_card {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) (ω : Fin n → ℝ) :
    ∀ {k : ℕ}, k ≤ numRemaining B → (B ∪ (g.hist ω k).jobs).card = B.card + k
  | 0, _ => by simp [hist_jobs_zero]
  | k + 1, hk => by
    have hlt : k < numRemaining B := by omega
    have hav := hg ω k hlt
    rw [hist_jobs_succ, Finset.union_insert, Finset.card_insert_of_notMem hav.1,
      feasible_card hg ω hlt.le]
    omega

private lemma feasible_jobs_card {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) (ω : Fin n → ℝ) :
    ∀ {k : ℕ}, k ≤ numRemaining B →
      (g.hist ω k).jobs.card = k ∧ Disjoint (g.hist ω k).jobs B
  | 0, _ => by simp [hist_jobs_zero]
  | k + 1, hk => by
    have hlt : k < numRemaining B := by omega
    have hav1 := (hg ω k hlt).1
    have ⟨hcard, hdisj⟩ := feasible_jobs_card hg ω hlt.le
    rw [Finset.mem_union, not_or] at hav1
    refine ⟨?_, ?_⟩
    · rw [hist_jobs_succ, Finset.card_insert_of_notMem hav1.2, hcard]
    · rw [hist_jobs_succ, Finset.disjoint_insert_left]
      exact ⟨hav1.1, hdisj⟩

private lemma feasible_jobs_univ {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) (ω : Fin n → ℝ) :
    B ∪ (g.hist ω (numRemaining B)).jobs = Finset.univ := by
  have hle : B.card ≤ n := by simpa using B.card_le_univ
  apply Finset.eq_univ_of_card
  rw [feasible_card hg ω le_rfl]
  unfold numRemaining
  simp; omega

private lemma feasible_job_not_mem_hist {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) (ω : Fin n → ℝ) {k : ℕ} (hk : k < numRemaining B) :
    g.job ω k ∉ (g.hist ω k).jobs :=
  (not_or.mp (by simpa [Finset.mem_union] using (hg ω k hk).1)).2

/-! #### Measurability of `Policy` and `Stage` -/

private lemma ofFn_snoc {α : Type*} {k : ℕ} (v : Fin k → α) (a : α) :
    List.ofFn (Fin.snoc v a : Fin (k + 1) → α) = List.ofFn v ++ [a] := by
  refine List.ext_getElem ?_ ?_
  · simp
  · intro i hi1 hi2
    rw [List.getElem_ofFn]
    by_cases h : i < k
    · rw [List.getElem_append_left (by simp [h]), List.getElem_ofFn]
      have : (⟨i, by omega⟩ : Fin (k + 1)) = (⟨i, h⟩ : Fin k).castSucc := rfl
      rw [this, Fin.snoc_castSucc]
    · have hi : i = k := by simp at hi1; omega
      subst i
      rw [List.getElem_append_right (by simp)]
      have : (⟨k, by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [this, Fin.snoc_last]
      simp

private lemma ofFn_append {α : Type*} {m k : ℕ} (u : Fin m → α) (v : Fin k → α) :
    List.ofFn (Fin.append u v : Fin (m + k) → α) = List.ofFn u ++ List.ofFn v := by
  refine List.ext_getElem ?_ ?_
  · simp
  · intro i hi1 hi2
    rw [List.getElem_ofFn]
    by_cases h : i < m
    · rw [List.getElem_append_left (by simp [h]), List.getElem_ofFn]
      have : (⟨i, by omega⟩ : Fin (m + k)) = Fin.castAdd k ⟨i, h⟩ := rfl
      rw [this, Fin.append_left]
    · rw [List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      have hi1' : i < m + k := by simpa [List.length_ofFn] using hi1
      have : (⟨i, hi1'⟩ : Fin (m + k)) = Fin.natAdd m ⟨i - m, by omega⟩ := by
        ext; simp; omega
      rw [this, Fin.append_right]
      simp

private def histVec (π : Policy n) : (k : ℕ) → (Fin n → ℝ) → (Fin k → Fin n × ℝ)
  | 0, _ => Fin.elim0
  | k + 1, ω =>
    let v := histVec π k ω
    let j := π.next (List.ofFn v)
    Fin.snoc v (j, ω j)

private lemma histVec_ofFn (π : Policy n) (ω : Fin n → ℝ) :
    ∀ k : ℕ, List.ofFn (histVec π k ω) = π.hist ω k
  | 0 => by simp [histVec, Policy.hist]
  | k + 1 => by
    simp only [histVec, Policy.hist]
    rw [ofFn_snoc, histVec_ofFn π ω k]

private lemma measurable_eval_pair :
    Measurable (fun p : (Fin n → ℝ) × Fin n => p.1 p.2) :=
  measurable_from_prod_countable_left fun j => measurable_pi_apply j

private lemma measurable_histVec (π : Policy n) :
    ∀ k : ℕ, Measurable (histVec π k)
  | 0 => by
    rw [measurable_pi_iff]
    intro i; exact i.elim0
  | k + 1 => by
    have ih := measurable_histVec π k
    have hj : Measurable (fun ω : Fin n → ℝ => π.next (List.ofFn (histVec π k ω))) :=
      (π.measurable_next k).comp ih
    have hval : Measurable (fun ω : Fin n → ℝ => ω (π.next (List.ofFn (histVec π k ω)))) :=
      measurable_eval_pair.comp (measurable_id.prodMk hj)
    have hpair : Measurable (fun ω : Fin n → ℝ =>
        (π.next (List.ofFn (histVec π k ω)), ω (π.next (List.ofFn (histVec π k ω))))) :=
      hj.prodMk hval
    rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [histVec, Fin.snoc_last] using hpair
    · intro i'
      simp only [histVec, Fin.snoc_castSucc]
      exact (measurable_pi_apply i').comp ih

private lemma measurable_job (π : Policy n) (k : ℕ) : Measurable (fun ω => π.job ω k) := by
  have heq : (fun ω => π.job ω k) = fun ω => π.next (List.ofFn (histVec π k ω)) := by
    ext ω; simp [Policy.job, histVec_ofFn]
  rw [heq]
  exact (π.measurable_next k).comp (measurable_histVec π k)

private lemma measurable_startTime (π : Policy n) (k : ℕ) :
    Measurable (fun ω => π.startTime ω k) := by
  have heq : (fun ω => π.startTime ω k) =
      fun ω => ∑ i : Fin k, (histVec π k ω i).2 := by
    ext ω
    simp [Policy.startTime, History.elapsed, ← histVec_ofFn, List.map_ofFn, List.sum_ofFn]
  rw [heq]
  exact Finset.measurable_sum Finset.univ fun i _ =>
    measurable_snd.comp ((measurable_pi_apply i).comp (measurable_histVec π k))

private lemma measurable_completionTime (π : Policy n) (k : ℕ) :
    Measurable (fun ω => π.completionTime ω k) :=
  measurable_startTime π (k + 1)

private lemma measurable_hist_jobs (π : Policy n) (k : ℕ) :
    Measurable (fun ω => (π.hist ω k).jobs) := by
  have heq : (fun ω => (π.hist ω k).jobs) =
      (fun v : Fin k → Fin n => Finset.univ.image v) ∘ (fun ω i => (histVec π k ω i).1) := by
    ext ω x
    simp only [Function.comp_apply, Finset.mem_image, Finset.mem_univ, true_and,
      History.jobs, List.mem_toFinset, List.mem_map, ← histVec_ofFn, List.mem_ofFn]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨i, hi⟩, rfl⟩
      exact ⟨i, by rw [hi]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨histVec π k ω i, ⟨i, rfl⟩, rfl⟩
  rw [heq]
  refine Measurable.comp (measurable_of_countable _) ?_
  rw [measurable_pi_iff]
  intro i
  exact measurable_fst.comp ((measurable_pi_apply i).comp (measurable_histVec π k))

private lemma measurable_stage_stop (p : Stage n) (l : ℕ) :
    Measurable (fun ω => p.stop (p.toPolicy.hist ω l)) := by
  have heq : (fun ω => p.stop (p.toPolicy.hist ω l)) =
      fun ω => p.stop (List.ofFn (histVec p.toPolicy l ω)) := by
    ext ω; rw [histVec_ofFn]
  rw [heq]
  exact (p.measurable_stop l).comp (measurable_histVec p.toPolicy l)

private lemma measurableSet_inStage (p : Stage n) (B : Finset (Fin n)) (k : ℕ) :
    MeasurableSet {ω | p.InStage B ω k} := by
  unfold Stage.InStage
  rw [Set.ofPred_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  have heq : {ω | ∀ l ∈ Finset.Icc 1 k, p.stop (p.toPolicy.hist ω l) = false} =
      ⋂ l ∈ Finset.Icc 1 k, {ω | p.stop (p.toPolicy.hist ω l) = false} := by
    ext ω; simp
  rw [heq]
  exact Finset.measurableSet_biInter _ fun l _ =>
    (measurable_stage_stop p l) (measurableSet_singleton false)

/-! #### Stage stopping count `stageSteps` -/

private noncomputable def stageSteps (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) : ℕ := by
  classical
  exact ((Finset.range (numRemaining B)).filter (p.InStage B ω)).card

private lemma inStage_mono {B : Finset (Fin n)} {p : Stage n} {ω : Fin n → ℝ} {k₁ k₂ : ℕ}
    (h12 : k₁ ≤ k₂) (h2 : p.InStage B ω k₂) : p.InStage B ω k₁ :=
  ⟨lt_of_le_of_lt h12 h2.1, fun l hl =>
    h2.2 l (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hl).1, le_trans (Finset.mem_Icc.mp hl).2 h12⟩)⟩

private lemma filter_inStage_eq_range (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) :
    letI := Classical.decPred (p.InStage B ω)
    (Finset.range (numRemaining B)).filter (p.InStage B ω) = Finset.range (stageSteps B p ω) := by
  classical
  set S := (Finset.range (numRemaining B)).filter (p.InStage B ω)
  have hdown : ∀ a b, a ≤ b → b ∈ S → a ∈ S := by
    intro a b hab hb
    rw [Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨lt_of_le_of_lt hab hb.1, inStage_mono hab hb.2⟩
  -- Every downward-closed subset of `ℕ` of card `m` equals `Finset.range m`
  have hsub : Finset.range S.card ⊆ S := by
    intro a ha
    rw [Finset.mem_range] at ha
    by_contra haS
    have hSsub : S ⊆ Finset.range a := by
      intro b hb
      rw [Finset.mem_range]
      by_contra hba; push Not at hba
      exact haS (hdown a b hba hb)
    have hcard := Finset.card_le_card hSsub
    rw [Finset.card_range] at hcard
    omega
  exact (Finset.eq_of_subset_of_card_le hsub (by simp)).symm

private lemma inStage_iff_lt_stageSteps (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) (k : ℕ) :
    p.InStage B ω k ↔ k < stageSteps B p ω := by
  classical
  have h := filter_inStage_eq_range B p ω
  constructor
  · intro hk
    have : k ∈ Finset.range (stageSteps B p ω) := by
      rw [← h, Finset.mem_filter, Finset.mem_range]
      exact ⟨hk.1, hk⟩
    exact Finset.mem_range.mp this
  · intro hk
    have : k ∈ (Finset.range (numRemaining B)).filter (p.InStage B ω) := by
      rw [h]; exact Finset.mem_range.mpr hk
    exact (Finset.mem_filter.mp this).2

private lemma stageSteps_le (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) :
    stageSteps B p ω ≤ numRemaining B := by
  classical
  unfold stageSteps
  calc ((Finset.range (numRemaining B)).filter (p.InStage B ω)).card
      ≤ (Finset.range (numRemaining B)).card := Finset.card_filter_le _ _
    _ = numRemaining B := Finset.card_range _

private lemma stageSteps_pos {B : Finset (Fin n)} (hB : B ≠ Finset.univ) (p : Stage n)
    (ω : Fin n → ℝ) : 1 ≤ stageSteps B p ω := by
  have hpos : 0 < numRemaining B := Nat.pos_of_ne_zero fun h => hB ((numRemaining_eq_zero_iff B).mp h)
  have h0 : p.InStage B ω 0 := ⟨hpos, by simp⟩
  exact (inStage_iff_lt_stageSteps B p ω 0).mp h0

private lemma jobsDone_eq_hist_jobs (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ) :
    p.jobsDone B ω = (p.toPolicy.hist ω (stageSteps B p ω)).jobs := by
  classical
  unfold Stage.jobsDone
  rw [hist_jobs_eq_image]
  congr 1
  exact filter_inStage_eq_range B p ω

private lemma stageSteps_eq_card_jobsDone {F : JobFamily n} {B : Finset (Fin n)} {p : Stage n}
    (hp : p.Feasible F B) (ω : Fin n → ℝ) :
    stageSteps B p ω = (p.jobsDone B ω).card := by
  rw [jobsDone_eq_hist_jobs]
  exact (feasible_jobs_card hp ω (stageSteps_le B p ω)).1.symm

private lemma jobsDone_disjoint {F : JobFamily n} {B : Finset (Fin n)} {p : Stage n}
    (hp : p.Feasible F B) (ω : Fin n → ℝ) :
    Disjoint (p.jobsDone B ω) B := by
  rw [jobsDone_eq_hist_jobs]
  exact (feasible_jobs_card hp ω (stageSteps_le B p ω)).2

private lemma jobsDone_nonempty {F : JobFamily n} {B : Finset (Fin n)} {p : Stage n}
    (hp : p.Feasible F B) (hB : B ≠ Finset.univ) (ω : Fin n → ℝ) :
    (p.jobsDone B ω).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have h1 := stageSteps_pos hB p ω
  rw [stageSteps_eq_card_jobsDone hp ω, h, Finset.card_empty] at h1
  omega

private lemma inStage_congr_of_agree {B : Finset (Fin n)} {p : Stage n} {ω ω' : Fin n → ℝ}
    {k : ℕ} (h : ∀ i ∈ (p.toPolicy.hist ω k).jobs, ω i = ω' i) :
    p.InStage B ω k ↔ p.InStage B ω' k := by
  have hhist : ∀ l ≤ k, p.toPolicy.hist ω l = p.toPolicy.hist ω' l := by
    intro l hl
    apply hist_congr_of_agree
    intro i hi
    apply h i
    rw [hist_jobs_eq_image] at hi ⊢
    rcases Finset.mem_image.mp hi with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) hl), rfl⟩
  unfold Stage.InStage
  constructor
  · rintro ⟨hk, hstop⟩
    refine ⟨hk, fun l hl => ?_⟩
    rw [← hhist l (Finset.mem_Icc.mp hl).2]
    exact hstop l hl
  · rintro ⟨hk, hstop⟩
    refine ⟨hk, fun l hl => ?_⟩
    rw [hhist l (Finset.mem_Icc.mp hl).2]
    exact hstop l hl

private lemma stageSteps_congr_of_jobsDone {B : Finset (Fin n)} {p : Stage n} {ω ω' : Fin n → ℝ}
    (h : ∀ i ∈ p.jobsDone B ω, ω i = ω' i) :
    stageSteps B p ω = stageSteps B p ω' ∧
      p.toPolicy.hist ω (stageSteps B p ω) = p.toPolicy.hist ω' (stageSteps B p ω') ∧
      p.jobsDone B ω = p.jobsDone B ω' := by
  set τ := stageSteps B p ω
  have hjobs : (p.toPolicy.hist ω τ).jobs = p.jobsDone B ω := (jobsDone_eq_hist_jobs B p ω).symm
  have hhist : ∀ l ≤ τ, p.toPolicy.hist ω l = p.toPolicy.hist ω' l := by
    intro l hl
    apply hist_congr_of_agree
    intro i hi
    apply h i
    rw [← hjobs]
    rw [hist_jobs_eq_image] at hi ⊢
    rcases Finset.mem_image.mp hi with ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) hl), rfl⟩
  have hτ : stageSteps B p ω' = τ := by
    have hlt : ∀ k < τ, p.InStage B ω' k := by
      intro k hk
      have h1 := (inStage_iff_lt_stageSteps B p ω k).mpr hk
      refine ⟨h1.1, fun l hl => ?_⟩
      rw [← hhist l (le_trans (Finset.mem_Icc.mp hl).2 hk.le)]
      exact h1.2 l hl
    have hge : ¬ p.InStage B ω' τ := by
      intro h1
      have h2 : p.InStage B ω τ := by
        refine ⟨h1.1, fun l hl => ?_⟩
        rw [hhist l (Finset.mem_Icc.mp hl).2]
        exact h1.2 l hl
      exact lt_irrefl τ ((inStage_iff_lt_stageSteps B p ω τ).mp h2)
    have hle : stageSteps B p ω' ≤ τ := by
      by_contra hgt; push Not at hgt
      exact hge ((inStage_iff_lt_stageSteps B p ω' τ).mpr hgt)
    have hge' : τ ≤ stageSteps B p ω' := by
      by_contra hlt'; push Not at hlt'
      have := hlt (stageSteps B p ω') hlt'
      exact lt_irrefl _ ((inStage_iff_lt_stageSteps B p ω' (stageSteps B p ω')).mp this)
    omega
  refine ⟨hτ.symm, ?_, ?_⟩
  · rw [hτ]; exact hhist τ le_rfl
  · rw [jobsDone_eq_hist_jobs, jobsDone_eq_hist_jobs, hτ, hhist τ le_rfl]

private lemma measurable_stageSteps (B : Finset (Fin n)) (p : Stage n) :
    Measurable (stageSteps B p) := by
  classical
  have heq : stageSteps B p =
      fun ω => ∑ k ∈ Finset.range (numRemaining B), if p.InStage B ω k then (1 : ℕ) else 0 := by
    ext ω; unfold stageSteps; rw [Finset.card_filter]
  rw [heq]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_inStage p B k) measurable_const measurable_const

private lemma measurable_stageEndTime (B : Finset (Fin n)) (p : Stage n) :
    Measurable (fun ω => p.toPolicy.startTime ω (stageSteps B p ω)) := by
  have heq : (fun ω => p.toPolicy.startTime ω (stageSteps B p ω)) =
      fun ω => ∑ t ∈ Finset.range (numRemaining B + 1),
        if stageSteps B p ω = t then p.toPolicy.startTime ω t else 0 := by
    ext ω
    rw [Finset.sum_ite_eq (Finset.range (numRemaining B + 1)) (stageSteps B p ω)]
    rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (stageSteps_le B p ω)))]
  rw [heq]
  refine Finset.measurable_sum _ fun t _ => ?_
  exact Measurable.ite ((measurable_stageSteps B p) (measurableSet_singleton t))
    (measurable_startTime p.toPolicy t) measurable_const

private lemma measurable_jobsDone (B : Finset (Fin n)) (p : Stage n) :
    Measurable (fun ω => p.jobsDone B ω) := by
  have h1 : ∀ S : Finset (Fin n), MeasurableSet {ω | p.jobsDone B ω = S} := by
    intro S
    have heq : {ω | p.jobsDone B ω = S} =
        ⋃ t ∈ Finset.range (numRemaining B + 1),
          {ω | stageSteps B p ω = t} ∩ {ω | (p.toPolicy.hist ω t).jobs = S} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range]
      constructor
      · intro h
        refine ⟨stageSteps B p ω, Nat.lt_succ_of_le (stageSteps_le B p ω), rfl, ?_⟩
        rwa [← jobsDone_eq_hist_jobs]
      · rintro ⟨t, _, rfl, h⟩
        rwa [jobsDone_eq_hist_jobs]
    rw [heq]
    refine Finset.measurableSet_biUnion _ fun t _ => ?_
    exact ((measurable_stageSteps B p) (measurableSet_singleton t)).inter
      ((measurable_hist_jobs p.toPolicy t) (measurableSet_singleton S))
  intro s _
  have hs : (fun ω => p.jobsDone B ω) ⁻¹' s = ⋃ S ∈ s, {ω | p.jobsDone B ω = S} := by
    ext ω; simp
  rw [hs]
  exact Set.Finite.measurableSet_biUnion (Set.toFinite s) fun S _ => h1 S

/-! #### Integrability & Step-by-Step Expectation Formulas -/

private lemma integrable_bounded_on_pos {F : JobFamily n} {f : (Fin n → ℝ) → ℝ}
    (hmeas : Measurable f) (C : ℝ) (hbdd : ∀ ω : Fin n → ℝ, (∀ i, 0 < ω i) → ‖f ω‖ ≤ C) :
    Integrable f (serviceLaw F) :=
  Integrable.of_bound hmeas.aestronglyMeasurable C
    (by filter_upwards [ae_pos_all F] with ω hpos; exact hbdd ω hpos)

private lemma integrable_step_start {F : JobFamily n} (B : Finset (Fin n)) (g : Policy n)
    (k : ℕ) {P : (Fin n → ℝ) → Prop} [DecidablePred P] (hP : MeasurableSet {ω | P ω})
    (f : Finset (Fin n) → Fin n → ℝ) :
    Integrable (fun ω => if P ω then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0)
      (serviceLaw F) := by
  classical
  let C : ℝ := ∑ D : Finset (Fin n), ∑ j : Fin n, |f D j|
  have hmeas : Measurable (fun ω => if P ω then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0) := by
    refine Measurable.ite hP ?_ measurable_const
    refine (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_startTime g k))).mul ?_
    have hf_pair : Measurable (fun p : Finset (Fin n) × Fin n => f p.1 p.2) :=
      measurable_of_countable _
    have hD : Measurable (fun ω => B ∪ (g.hist ω k).jobs) :=
      (measurable_of_countable (fun S : Finset (Fin n) => B ∪ S)).comp (measurable_hist_jobs g k)
    exact hf_pair.comp (hD.prodMk (measurable_job g k))
  refine integrable_bounded_on_pos hmeas C fun ω hpos => ?_
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-F.γ * g.startTime ω k) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos, startTime_nonneg g hpos k])
    have hfC : |f (B ∪ (g.hist ω k).jobs) (g.job ω k)| ≤ C := by
      have h1 : |f (B ∪ (g.hist ω k).jobs) (g.job ω k)| ≤
          ∑ j : Fin n, |f (B ∪ (g.hist ω k).jobs) j| :=
        Finset.single_le_sum (f := fun j => |f (B ∪ (g.hist ω k).jobs) j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ (g.job ω k))
      have h2 : ∑ j : Fin n, |f (B ∪ (g.hist ω k).jobs) j| ≤ C :=
        Finset.single_le_sum (f := fun D => ∑ j : Fin n, |f D j|)
          (fun D _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ _)
      linarith
    calc Real.exp (-F.γ * g.startTime ω k) * |f (B ∪ (g.hist ω k).jobs) (g.job ω k)|
        ≤ 1 * |f (B ∪ (g.hist ω k).jobs) (g.job ω k)| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ ≤ C := by linarith
  · simp only [norm_zero]
    exact Finset.sum_nonneg fun D _ => Finset.sum_nonneg fun j _ => abs_nonneg _

private lemma integrable_step_compl {F : JobFamily n} (B : Finset (Fin n)) (g : Policy n)
    (k : ℕ) {P : (Fin n → ℝ) → Prop} [DecidablePred P] (hP : MeasurableSet {ω | P ω})
    (f : Finset (Fin n) → Fin n → ℝ) :
    Integrable (fun ω => if P ω then
      Real.exp (-F.γ * g.completionTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0)
      (serviceLaw F) := by
  classical
  let C : ℝ := ∑ D : Finset (Fin n), ∑ j : Fin n, |f D j|
  have hmeas : Measurable (fun ω => if P ω then
      Real.exp (-F.γ * g.completionTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0) := by
    refine Measurable.ite hP ?_ measurable_const
    refine (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_completionTime g k))).mul ?_
    have hf_pair : Measurable (fun p : Finset (Fin n) × Fin n => f p.1 p.2) :=
      measurable_of_countable _
    have hD : Measurable (fun ω => B ∪ (g.hist ω k).jobs) :=
      (measurable_of_countable (fun S : Finset (Fin n) => B ∪ S)).comp (measurable_hist_jobs g k)
    exact hf_pair.comp (hD.prodMk (measurable_job g k))
  refine integrable_bounded_on_pos hmeas C fun ω hpos => ?_
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-F.γ * g.completionTime ω k) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos, completionTime_pos g hpos k])
    have hfC : |f (B ∪ (g.hist ω k).jobs) (g.job ω k)| ≤ C := by
      have h1 : |f (B ∪ (g.hist ω k).jobs) (g.job ω k)| ≤
          ∑ j : Fin n, |f (B ∪ (g.hist ω k).jobs) j| :=
        Finset.single_le_sum (f := fun j => |f (B ∪ (g.hist ω k).jobs) j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ (g.job ω k))
      have h2 : ∑ j : Fin n, |f (B ∪ (g.hist ω k).jobs) j| ≤ C :=
        Finset.single_le_sum (f := fun D => ∑ j : Fin n, |f D j|)
          (fun D _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ _)
      linarith
    calc Real.exp (-F.γ * g.completionTime ω k) * |f (B ∪ (g.hist ω k).jobs) (g.job ω k)|
        ≤ 1 * |f (B ∪ (g.hist ω k).jobs) (g.job ω k)| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ ≤ C := by linarith
  · simp only [norm_zero]
    exact Finset.sum_nonneg fun D _ => Finset.sum_nonneg fun j _ => abs_nonneg _

private lemma integral_step_exp_mul {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) {k : ℕ} (hk : k < numRemaining B)
    {P : (Fin n → ℝ) → Prop} [DecidablePred P] (hP : MeasurableSet {ω | P ω})
    (hP_indep : ∀ ω ω' : Fin n → ℝ, (∀ i ∈ (g.hist ω k).jobs, ω i = ω' i) → (P ω ↔ P ω'))
    (f : Finset (Fin n) → Fin n → ℝ) :
    ∫ ω, (if P ω then
        Real.exp (-F.γ * g.completionTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k)
      else 0) ∂serviceLaw F =
    ∫ ω, (if P ω then
        Real.exp (-F.γ * g.startTime ω k) * (phi F (g.job ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k))
      else 0) ∂serviceLaw F := by
  classical
  have hsplitL : (fun ω => if P ω then
      Real.exp (-F.γ * g.completionTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0) =
    fun ω => ∑ j : Fin n, (if P ω ∧ g.job ω k = j then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) *
      Real.exp (-F.γ * ω j) := by
    ext ω
    rw [Finset.sum_eq_single (g.job ω k)]
    · by_cases hPw : P ω
      · simp only [hPw, true_and, ↓reduceIte, completionTime_eq_add, mul_add, Real.exp_add]
        ring
      · simp [hPw]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsplitR : (fun ω => if P ω then
      Real.exp (-F.γ * g.startTime ω k) * (phi F (g.job ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k))
      else 0) =
    fun ω => ∑ j : Fin n, (if P ω ∧ g.job ω k = j then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) * phi F j := by
    ext ω
    rw [Finset.sum_eq_single (g.job ω k)]
    · by_cases hPw : P ω
      · simp only [hPw, true_and, ↓reduceIte]; ring
      · simp [hPw]
    · intro j _ hj; simp [Ne.symm hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsplitL, hsplitR]
  have hintL : ∀ j : Fin n, Integrable (fun ω => (if P ω ∧ g.job ω k = j then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) *
      Real.exp (-F.γ * ω j)) (serviceLaw F) := by
    intro j
    have heq : (fun ω => (if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) *
        Real.exp (-F.γ * ω j)) =
      fun ω => if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.completionTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0 := by
      ext ω
      split_ifs with h
      · rw [completionTime_eq_add, h.2, mul_add, Real.exp_add]; ring
      · simp
    rw [heq]
    exact integrable_step_compl (P := fun ω => P ω ∧ g.job ω k = j) B g k
      (hP.inter ((measurable_job g k) (measurableSet_singleton j))) f
  have hintR : ∀ j : Fin n, Integrable (fun ω => (if P ω ∧ g.job ω k = j then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) * phi F j)
      (serviceLaw F) := by
    intro j
    have heq : (fun ω => (if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) * phi F j) =
      fun ω => if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.startTime ω k) * (f (B ∪ (g.hist ω k).jobs) (g.job ω k) * phi F (g.job ω k))
      else 0 := by
      ext ω
      split_ifs with h
      · rw [h.2]; ring
      · simp
    rw [heq]
    exact integrable_step_start (P := fun ω => P ω ∧ g.job ω k = j) B g k
      (hP.inter ((measurable_job g k) (measurableSet_singleton j)))
      (fun D i => f D i * phi F i)
  rw [integral_finsetSum _ fun j _ => hintL j, integral_finsetSum _ fun j _ => hintR j]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hf_int : Integrable (fun ω => if P ω ∧ g.job ω k = j then
      Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) (serviceLaw F) := by
    have heq : (fun ω => if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) =
      fun ω => if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) (g.job ω k) else 0 := by
      ext ω; split_ifs with h <;> simp_all
    rw [heq]
    exact integrable_step_start (P := fun ω => P ω ∧ g.job ω k = j) B g k
      (hP.inter ((measurable_job g k) (measurableSet_singleton j))) f
  have hf_indep : ∀ ω ω' : Fin n → ℝ, (∀ i, i ≠ j → ω i = ω' i) →
      (if P ω ∧ g.job ω k = j then
        Real.exp (-F.γ * g.startTime ω k) * f (B ∪ (g.hist ω k).jobs) j else 0) =
      (if P ω' ∧ g.job ω' k = j then
        Real.exp (-F.γ * g.startTime ω' k) * f (B ∪ (g.hist ω' k).jobs) j else 0) := by
    intro ω ω' hagree
    have hdir : ∀ a b : Fin n → ℝ, (∀ i, i ≠ j → a i = b i) → g.job a k = j →
        g.hist a k = g.hist b k ∧ (P a ↔ P b) := by
      intro a b hab hja
      have hjnot : j ∉ (g.hist a k).jobs := hja ▸ feasible_job_not_mem_hist hg a hk
      have hdom : ∀ i ∈ (g.hist a k).jobs, a i = b i := fun i hi =>
        hab i (fun hij => hjnot (hij ▸ hi))
      exact ⟨hist_congr_of_agree g hdom, hP_indep a b hdom⟩
    by_cases h1 : g.job ω k = j
    · obtain ⟨hh, hPP⟩ := hdir ω ω' hagree h1
      have h1' : g.job ω' k = j := by simp only [Policy.job, ← hh]; exact h1
      have hS : g.startTime ω k = g.startTime ω' k := by simp [Policy.startTime, hh]
      simp [h1, h1', hPP, hh, hS]
    · have h1' : g.job ω' k ≠ j := by
        intro h2
        obtain ⟨hh, _⟩ := hdir ω' ω (fun i hi => (hagree i hi).symm) h2
        exact h1 (by simp only [Policy.job, ← hh]; exact h2)
      simp [h1, h1']
  rw [integral_mul_coord_of_indep F j hf_int hf_indep (integrable_exp_service F j)]
  rw [integral_mul_const]
  rfl

private lemma payoff_eq_aVal {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) :
    g.payoff F B = ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      Real.exp (-F.γ * g.startTime ω k) * aVal F (g.job ω k) ∂serviceLaw F := by
  unfold Policy.payoff
  have h1 : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => F.reward (g.job ω k) * Real.exp (-F.γ * g.completionTime ω k))
        (serviceLaw F) := by
    intro k _
    have heq : (fun ω => F.reward (g.job ω k) * Real.exp (-F.γ * g.completionTime ω k)) =
      fun ω => if True then
        Real.exp (-F.γ * g.completionTime ω k) * F.reward (g.job ω k) else 0 := by
      ext ω; simp [mul_comm]
    rw [heq]
    exact integrable_step_compl B g k MeasurableSet.univ (fun _ j => F.reward j)
  have h2 : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => Real.exp (-F.γ * g.startTime ω k) * aVal F (g.job ω k))
        (serviceLaw F) := by
    intro k _
    have heq : (fun ω => Real.exp (-F.γ * g.startTime ω k) * aVal F (g.job ω k)) =
      fun ω => if True then
        Real.exp (-F.γ * g.startTime ω k) * aVal F (g.job ω k) else 0 := by
      ext ω; simp
    rw [heq]
    exact integrable_step_start B g k MeasurableSet.univ (fun _ j => aVal F j)
  rw [integral_finsetSum _ h1, integral_finsetSum _ h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hstep := integral_step_exp_mul hg (Finset.mem_range.mp hk) MeasurableSet.univ
    (fun _ _ _ => Iff.rfl) (fun _ j => F.reward j)
  simpa [aVal, mul_comm, mul_left_comm, mul_assoc] using hstep

open Classical in
private lemma stage_reward_eq_aVal {F : JobFamily n} {B : Finset (Fin n)} {p : Stage n}
    (hp : p.Feasible F B) :
    p.reward F B = ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k)
      else 0) ∂serviceLaw F := by
  classical
  unfold Stage.reward
  have h1 : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k)
      else 0) (serviceLaw F) := by
    intro k _
    have heq : (fun ω => if p.InStage B ω k then
        F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k) else 0) =
      fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.reward (p.toPolicy.job ω k) else 0 := by
      ext ω; split_ifs <;> ring
    rw [heq]
    exact integrable_step_compl B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => F.reward j)
  have h2 : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) else 0)
        (serviceLaw F) := fun k _ =>
    integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => aVal F j)
  rw [integral_finsetSum _ h1, integral_finsetSum _ h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hstep := integral_step_exp_mul hp (Finset.mem_range.mp hk) (measurableSet_inStage p B k)
    (fun _ _ h => inStage_congr_of_agree h) (fun _ j => F.reward j)
  have heqL : (fun ω => if p.InStage B ω k then
      F.reward (p.toPolicy.job ω k) * Real.exp (-F.γ * p.toPolicy.completionTime ω k) else 0) =
    fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.reward (p.toPolicy.job ω k) else 0 := by
    ext ω; split_ifs <;> ring
  have heqR : (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        (phi F (p.toPolicy.job ω k) * F.reward (p.toPolicy.job ω k)) else 0) =
    fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) else 0 := by
    ext ω; split_ifs <;> simp [aVal, mul_comm]
  rw [heqL, hstep, heqR]

open Classical in
private lemma stage_time_eq_cVal {F : JobFamily n} {B : Finset (Fin n)} {p : Stage n}
    (hp : p.Feasible F B) :
    p.time F B = ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k)
      else 0) ∂serviceLaw F := by
  classical
  unfold Stage.time
  have h1 : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) (serviceLaw F) := by
    intro k _
    have heq : (fun ω => if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) =
      fun ω => (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) * F.γ⁻¹ else 0) -
        (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.γ⁻¹ else 0) := by
      ext ω; split_ifs <;> ring
    rw [heq]
    exact (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ _ => F.γ⁻¹)).sub
      (integrable_step_compl B p.toPolicy k (measurableSet_inStage p B k) (fun _ _ => F.γ⁻¹))
  have h2 : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0)
        (serviceLaw F) := fun k _ =>
    integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => cVal F j)
  rw [integral_finsetSum _ h1, integral_finsetSum _ h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  have heq : (fun ω => if p.InStage B ω k then
      F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
        Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) =
    fun ω => (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) * F.γ⁻¹ else 0) -
      (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.completionTime ω k) * F.γ⁻¹ else 0) := by
    ext ω; split_ifs <;> ring
  rw [heq, integral_sub
    (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ _ => F.γ⁻¹))
    (integrable_step_compl B p.toPolicy k (measurableSet_inStage p B k) (fun _ _ => F.γ⁻¹))]
  rw [integral_step_exp_mul hp (Finset.mem_range.mp hk) (measurableSet_inStage p B k)
    (fun _ _ h => inStage_congr_of_agree h) (fun _ _ => F.γ⁻¹)]
  rw [← integral_sub
    (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ _ => F.γ⁻¹))
    (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => phi F j * F.γ⁻¹))]
  congr 1; ext ω; split_ifs
  · simp [cVal]; ring
  · ring

private lemma integrable_stageEnd_mul {F : JobFamily n} (B : Finset (Fin n)) (p : Stage n)
    (V : Finset (Fin n) → ℝ) :
    Integrable (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
      V (B ∪ p.jobsDone B ω)) (serviceLaw F) := by
  let C : ℝ := ∑ D : Finset (Fin n), |V D|
  have hmeas : Measurable (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
      V (B ∪ p.jobsDone B ω)) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_stageEndTime B p))).mul
      ((measurable_of_countable (fun S : Finset (Fin n) => V (B ∪ S))).comp (measurable_jobsDone B p))
  refine integrable_bounded_on_pos hmeas C fun ω hpos => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [F.γ_pos, startTime_nonneg p.toPolicy hpos (stageSteps B p ω)])
  have hV : |V (B ∪ p.jobsDone B ω)| ≤ C :=
    Finset.single_le_sum (f := fun D => |V D|) (fun D _ => abs_nonneg _) (Finset.mem_univ _)
  calc Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) * |V (B ∪ p.jobsDone B ω)|
      ≤ 1 * |V (B ∪ p.jobsDone B ω)| := mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ ≤ C := by linarith

private lemma sum_telescope_stage (B : Finset (Fin n)) (p : Stage n) (ω : Fin n → ℝ)
    (f : ℕ → ℝ) :
    letI := Classical.decPred (p.InStage B ω)
    ∑ k ∈ Finset.range (numRemaining B), (if p.InStage B ω k then f k - f (k + 1) else 0) =
      f 0 - f (stageSteps B p ω) := by
  classical
  rw [← Finset.sum_filter, filter_inStage_eq_range]
  induction stageSteps B p ω with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma stage_time_eq_one_sub_exp {F : JobFamily n} (B : Finset (Fin n)) (p : Stage n) :
    p.time F B = F.γ⁻¹ * (1 - ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω))
      ∂serviceLaw F) := by
  classical
  unfold Stage.time
  have hpt : ∀ ω : Fin n → ℝ,
      ∑ k ∈ Finset.range (numRemaining B),
        (if p.InStage B ω k then
          F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
            Real.exp (-F.γ * p.toPolicy.completionTime ω k))
        else 0) =
      F.γ⁻¹ * (1 - Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω))) := by
    intro ω
    have h1 : ∀ k, (if p.InStage B ω k then
        F.γ⁻¹ * (Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k)) else 0) =
      F.γ⁻¹ * (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) -
          Real.exp (-F.γ * p.toPolicy.startTime ω (k + 1)) else 0) := by
      intro k; split_ifs <;> simp [completionTime_eq_startTime_succ]
    simp_rw [h1, ← Finset.mul_sum]
    rw [sum_telescope_stage B p ω (fun k => Real.exp (-F.γ * p.toPolicy.startTime ω k))]
    simp [startTime_zero]
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrable_const 1)]
  · rw [integral_const, probReal_univ, one_smul]
  · simpa using integrable_stageEnd_mul (F := F) B p (fun _ => 1)

private lemma stage_time_pos {F : JobFamily n} {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    {p : Stage n} (hp : p.Feasible F B) : 0 < p.time F B := by
  classical
  rw [stage_time_eq_cVal hp]
  have h0 : 0 < numRemaining B := Nat.pos_of_ne_zero fun h => hB ((numRemaining_eq_zero_iff B).mp h)
  have hterm0 : ∀ ω, (∀ i, 0 < ω i) →
      cVal F (p.toPolicy.job ω 0) ≤ ∑ k ∈ Finset.range (numRemaining B),
        (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0) := by
    intro ω hpos
    have hle := Finset.single_le_sum (s := Finset.range (numRemaining B))
      (f := fun k => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0)
      (fun k _ => by
        split_ifs
        · exact mul_nonneg (Real.exp_pos _).le (cVal_pos F _).le
        · exact le_rfl)
      (Finset.mem_range.mpr h0)
    have hIn0 : p.InStage B ω 0 := ⟨h0, by simp⟩
    simpa [hIn0, startTime_zero] using hle
  have hjob0 : ∀ ω, p.toPolicy.job ω 0 = p.toPolicy.next [] := fun _ => rfl
  let j₀ := p.toPolicy.next []
  have hint_sum : Integrable (fun ω => ∑ k ∈ Finset.range (numRemaining B),
      if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0)
      (serviceLaw F) :=
    integrable_finsetSum _ fun k _ =>
      integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => cVal F j)
  have hle_int : cVal F j₀ ≤ ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0)
      ∂serviceLaw F := by
    calc cVal F j₀ = ∫ _ : Fin n → ℝ, cVal F j₀ ∂serviceLaw F := by
          rw [integral_const, probReal_univ, one_smul]
      _ ≤ _ := by
          refine integral_mono_ae (integrable_const _) hint_sum ?_
          filter_upwards [ae_pos_all F] with ω hpos
          simpa [j₀, hjob0] using hterm0 ω hpos
  linarith [cVal_pos F j₀]

private lemma stage_ratio_bddAbove {F : JobFamily n} {B : Finset (Fin n)} (hB : B ≠ Finset.univ) :
    BddAbove {x : ℝ | ∃ p : Stage n, p.Feasible F B ∧ x = p.ratio F B} := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    obtain ⟨j, hj⟩ := availFinset_nonempty F hB
    exact ⟨j, Finset.mem_univ j⟩
  let M : ℝ := Finset.univ.sup' hne fun i => aVal F i / cVal F i
  refine ⟨M, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  unfold Stage.ratio
  rw [div_le_iff₀ (stage_time_pos hB hp)]
  rw [stage_reward_eq_aVal hp, stage_time_eq_cVal hp, ← integral_const_mul]
  have hintL : Integrable (fun ω => ∑ k ∈ Finset.range (numRemaining B),
      if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) else 0)
      (serviceLaw F) :=
    integrable_finsetSum _ fun k _ =>
      integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => aVal F j)
  have hintR : Integrable (fun ω => M * ∑ k ∈ Finset.range (numRemaining B),
      if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0)
      (serviceLaw F) :=
    (integrable_finsetSum _ fun k _ =>
      integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => cVal F j)).const_mul M
  refine integral_mono hintL hintR fun ω => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs
  · have hM : aVal F (p.toPolicy.job ω k) ≤ M * cVal F (p.toPolicy.job ω k) := by
      have h1 : aVal F (p.toPolicy.job ω k) / cVal F (p.toPolicy.job ω k) ≤ M :=
        Finset.le_sup' (f := fun i => aVal F i / cVal F i) (Finset.mem_univ _)
      exact (div_le_iff₀ (cVal_pos F _)).mp h1
    calc Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k)
        ≤ Real.exp (-F.γ * p.toPolicy.startTime ω k) * (M * cVal F (p.toPolicy.job ω k)) :=
          mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
      _ = M * (Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k)) := by ring
  · simp

private lemma payoff_le_UVal {F : JobFamily n} {B : Finset (Fin n)} {g : Policy n}
    (hg : g.Feasible F B) :
    g.payoff F B ≤ UVal F (aVal F) (phi F) B := by
  let U := UVal F (aVal F) (phi F)
  have htel : U B = ∫ ω, ∑ k ∈ Finset.range (numRemaining B),
      (Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs) -
        Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs)) ∂serviceLaw F := by
    have hpt : ∀ ω : Fin n → ℝ,
        ∑ k ∈ Finset.range (numRemaining B),
          (Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs) -
            Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs)) = U B := by
      intro ω
      have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m,
          (Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs) -
            Real.exp (-F.γ * g.startTime ω (k + 1)) * U (B ∪ (g.hist ω (k + 1)).jobs)) =
          U B - Real.exp (-F.γ * g.startTime ω m) * U (B ∪ (g.hist ω m).jobs) := by
        intro m
        induction m with
        | zero => simp [startTime_zero, hist_jobs_zero]
        | succ m ih => rw [Finset.sum_range_succ, ih]; ring
      simp_rw [completionTime_eq_startTime_succ]
      rw [hsum (numRemaining B), feasible_jobs_univ hg ω]
      simp [U, UVal_univ]
    simp_rw [hpt]
    rw [integral_const, probReal_univ, one_smul]
  have hstep_int : ∀ k ∈ Finset.range (numRemaining B),
      ∫ ω, (Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs) -
        Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs)) ∂serviceLaw F =
      ∫ ω, Real.exp (-F.γ * g.startTime ω k) *
        (U (B ∪ (g.hist ω k).jobs) - phi F (g.job ω k) * U (insert (g.job ω k) (B ∪ (g.hist ω k).jobs)))
        ∂serviceLaw F := by
    intro k hk
    have h1 : Integrable (fun ω => Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs))
        (serviceLaw F) := by
      simpa using integrable_step_start (F := F) B g k MeasurableSet.univ (fun D _ => U D)
    have h2eq : (fun ω => Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs)) =
        fun ω => if True then Real.exp (-F.γ * g.completionTime ω k) *
          U (insert (g.job ω k) (B ∪ (g.hist ω k).jobs)) else 0 := by
      ext ω; simp [hist_jobs_succ, Finset.union_insert]
    have h2 : Integrable (fun ω => Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs))
        (serviceLaw F) := by
      rw [h2eq]
      exact integrable_step_compl B g k MeasurableSet.univ (fun D j => U (insert j D))
    rw [integral_sub h1 h2, h2eq,
      integral_step_exp_mul hg (Finset.mem_range.mp hk) MeasurableSet.univ (fun _ _ _ => Iff.rfl)
        (fun D j => U (insert j D))]
    have h2' : Integrable (fun ω => if True then Real.exp (-F.γ * g.startTime ω k) *
        (phi F (g.job ω k) * U (insert (g.job ω k) (B ∪ (g.hist ω k).jobs))) else 0) (serviceLaw F) :=
      integrable_step_start B g k MeasurableSet.univ (fun D j => phi F j * U (insert j D))
    rw [← integral_sub h1 h2']
    congr 1; ext ω; simp; ring
  have hint_diff : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs) -
        Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs)) (serviceLaw F) := by
    intro k _
    have h1 : Integrable (fun ω => Real.exp (-F.γ * g.startTime ω k) * U (B ∪ (g.hist ω k).jobs))
        (serviceLaw F) := by
      simpa using integrable_step_start (F := F) B g k MeasurableSet.univ (fun D _ => U D)
    have h2eq : (fun ω => Real.exp (-F.γ * g.completionTime ω k) * U (B ∪ (g.hist ω (k + 1)).jobs)) =
        fun ω => if True then Real.exp (-F.γ * g.completionTime ω k) *
          U (insert (g.job ω k) (B ∪ (g.hist ω k).jobs)) else 0 := by
      ext ω; simp [hist_jobs_succ, Finset.union_insert]
    exact h1.sub (by rw [h2eq]; exact integrable_step_compl B g k MeasurableSet.univ (fun D j => U (insert j D)))
  change g.payoff F B ≤ U B
  rw [payoff_eq_aVal hg, htel, integral_finsetSum _ hint_diff]
  rw [integral_finsetSum _ fun k _ => by
    simpa using integrable_step_start (F := F) B g k MeasurableSet.univ (fun _ j => aVal F j)]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [hstep_int k hk]
  refine integral_mono
    (by simpa using integrable_step_start (F := F) B g k MeasurableSet.univ (fun _ j => aVal F j))
    (by
      simpa using integrable_step_start (F := F) B g k MeasurableSet.univ
        (fun D j => U D - phi F j * U (insert j D))) fun ω => ?_
  have hav := hg ω k (Finset.mem_range.mp hk)
  have hle := le_UVal F (aVal F) (phi F) hav
  have hdiff : aVal F (g.job ω k) ≤
      U (B ∪ (g.hist ω k).jobs) - phi F (g.job ω k) * U (insert (g.job ω k) (B ∪ (g.hist ω k).jobs)) := by
    dsimp [U]; linarith
  exact mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le

open Classical in
private lemma stage_telescope_eq {F : JobFamily n} {B : Finset (Fin n)} {p : Stage n}
    (hp : p.Feasible F B) (V : Finset (Fin n) → ℝ) :
    V B - ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        V (B ∪ p.jobsDone B ω) ∂serviceLaw F =
      ∑ k ∈ Finset.range (numRemaining B),
        ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (V (B ∪ (p.toPolicy.hist ω k).jobs) -
              phi F (p.toPolicy.job ω k) * V (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
        else 0) ∂serviceLaw F := by
  classical
  have hpt : ∀ ω : Fin n → ℝ,
      V B - Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) * V (B ∪ p.jobsDone B ω) =
      ∑ k ∈ Finset.range (numRemaining B),
        (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * V (B ∪ (p.toPolicy.hist ω k).jobs) -
            Real.exp (-F.γ * p.toPolicy.completionTime ω k) * V (B ∪ (p.toPolicy.hist ω (k + 1)).jobs)
        else 0) := by
    intro ω
    have h1 := sum_telescope_stage B p ω (fun k => Real.exp (-F.γ * p.toPolicy.startTime ω k) *
      V (B ∪ (p.toPolicy.hist ω k).jobs))
    simp only [startTime_zero, hist_jobs_zero, mul_zero, Real.exp_zero, one_mul, Finset.union_empty,
      ← jobsDone_eq_hist_jobs] at h1
    simpa [completionTime_eq_startTime_succ] using h1.symm
  have hLHS : V B - ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
      V (B ∪ p.jobsDone B ω) ∂serviceLaw F =
    ∫ ω, (V B - Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
      V (B ∪ p.jobsDone B ω)) ∂serviceLaw F := by
    rw [integral_sub (integrable_const _) (integrable_stageEnd_mul B p V),
      integral_const, probReal_univ, one_smul]
  rw [hLHS]
  simp_rw [hpt]
  have hint : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * V (B ∪ (p.toPolicy.hist ω k).jobs) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) * V (B ∪ (p.toPolicy.hist ω (k + 1)).jobs)
      else 0) (serviceLaw F) := by
    intro k _
    have heq : (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * V (B ∪ (p.toPolicy.hist ω k).jobs) -
          Real.exp (-F.γ * p.toPolicy.completionTime ω k) * V (B ∪ (p.toPolicy.hist ω (k + 1)).jobs)
      else 0) =
      fun ω => (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          V (B ∪ (p.toPolicy.hist ω k).jobs) else 0) -
        (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
          V (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)) else 0) := by
      ext ω; split_ifs <;> simp [hist_jobs_succ, Finset.union_insert]
    rw [heq]
    exact (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun D _ => V D)).sub
      (integrable_step_compl B p.toPolicy k (measurableSet_inStage p B k) (fun D j => V (insert j D)))
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun k hk => ?_
  have heq : (fun ω => if p.InStage B ω k then
      Real.exp (-F.γ * p.toPolicy.startTime ω k) * V (B ∪ (p.toPolicy.hist ω k).jobs) -
        Real.exp (-F.γ * p.toPolicy.completionTime ω k) * V (B ∪ (p.toPolicy.hist ω (k + 1)).jobs)
    else 0) =
    fun ω => (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.startTime ω k) *
        V (B ∪ (p.toPolicy.hist ω k).jobs) else 0) -
      (if p.InStage B ω k then Real.exp (-F.γ * p.toPolicy.completionTime ω k) *
        V (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)) else 0) := by
    ext ω; split_ifs <;> simp [hist_jobs_succ, Finset.union_insert]
  rw [heq, integral_sub
    (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun D _ => V D))
    (integrable_step_compl B p.toPolicy k (measurableSet_inStage p B k) (fun D j => V (insert j D)))]
  rw [integral_step_exp_mul hp (Finset.mem_range.mp hk) (measurableSet_inStage p B k)
    (fun _ _ h => inStage_congr_of_agree h) (fun D j => V (insert j D))]
  rw [← integral_sub
    (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun D _ => V D))
    (integrable_step_start B p.toPolicy k (measurableSet_inStage p B k)
      (fun D j => phi F j * V (insert j D)))]
  congr 1; ext ω; split_ifs <;> ring

/-! #### Greedy stage for `HVal`, `GVal_familyIndex_eq_zero`, and `UVal_sub_stage_le_index_mul_time` -/

private lemma exists_stage_sub_eq_HVal {F : JobFamily n} {B : Finset (Fin n)} (hB : B ≠ Finset.univ)
    (lam : ℝ) :
    ∃ p : Stage n, p.Feasible F B ∧
      p.reward F B - lam * p.time F B = HVal F (wVal F lam) (phi F) B hB := by
  classical
  obtain ⟨j₀, _⟩ := availFinset_nonempty F hB
  let optJob : Finset (Fin n) → Fin n := fun D =>
    if hD : D = Finset.univ then j₀
    else Classical.choose (exists_HVal_eq F (wVal F lam) (phi F) hD)
  have hopt : ∀ D, (hD : D ≠ Finset.univ) →
      IsAvailable F D (optJob D) ∧
        HVal F (wVal F lam) (phi F) D hD =
          wVal F lam (optJob D) + phi F (optJob D) * GVal F (wVal F lam) (phi F) (insert (optJob D) D) := by
    intro D hD
    simp only [optJob, dif_neg hD]
    exact Classical.choose_spec (exists_HVal_eq F (wVal F lam) (phi F) hD)
  have hjobs_meas : ∀ k : ℕ, Measurable (fun v : Fin k → Fin n × ℝ => History.jobs (List.ofFn v)) := by
    intro k
    have heq : (fun v : Fin k → Fin n × ℝ => History.jobs (List.ofFn v)) =
        (fun u : Fin k → Fin n => Finset.univ.image u) ∘ (fun v i => (v i).1) := by
      ext v x
      simp only [Function.comp_apply, Finset.mem_image, Finset.mem_univ, true_and,
        History.jobs, List.mem_toFinset, List.mem_map, List.mem_ofFn]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨i, hi⟩, rfl⟩; exact ⟨i, by rw [hi]⟩
      · rintro ⟨i, rfl⟩; exact ⟨v i, ⟨i, rfl⟩, rfl⟩
    rw [heq]
    refine (measurable_of_countable _).comp ?_
    rw [measurable_pi_iff]
    intro i
    exact measurable_fst.comp (measurable_pi_apply i)
  let p : Stage n := {
    next := fun h => optJob (B ∪ h.jobs)
    measurable_next := fun k =>
      (measurable_of_countable (fun S => optJob (B ∪ S))).comp (hjobs_meas k)
    stop := fun h => decide (GVal F (wVal F lam) (phi F) (B ∪ h.jobs) ≤ 0)
    measurable_stop := fun k =>
      (measurable_of_countable (fun S => decide (GVal F (wVal F lam) (phi F) (B ∪ S) ≤ 0))).comp
        (hjobs_meas k)
  }
  have hp_feas : p.Feasible F B := by
    intro ω k hk
    have hcard : (B ∪ (p.toPolicy.hist ω k).jobs).card = B.card + k := by
      induction k with
      | zero => simp [hist_jobs_zero]
      | succ k ih =>
        have hk' : k < numRemaining B := by omega
        have hprev := ih hk'
        have hne : B ∪ (p.toPolicy.hist ω k).jobs ≠ Finset.univ := by
          intro h
          have hle : B.card ≤ n := by simpa using B.card_le_univ
          rw [h, Finset.card_univ, Fintype.card_fin] at hprev
          unfold numRemaining at hk'; omega
        have hav := (hopt _ hne).1
        rw [hist_jobs_succ, Finset.union_insert]
        change (insert (optJob (B ∪ (p.toPolicy.hist ω k).jobs))
          (B ∪ (p.toPolicy.hist ω k).jobs)).card = B.card + (k + 1)
        rw [Finset.card_insert_of_notMem hav.1, hprev]; omega
    have hne : B ∪ (p.toPolicy.hist ω k).jobs ≠ Finset.univ := by
      intro h
      have hle : B.card ≤ n := by simpa using B.card_le_univ
      rw [h, Finset.card_univ, Fintype.card_fin] at hcard
      unfold numRemaining at hk; omega
    exact (hopt _ hne).1
  refine ⟨p, hp_feas, ?_⟩
  let G := GVal F (wVal F lam) (phi F)
  -- Key observation: for every ω, G (B ∪ p.jobsDone B ω) = 0
  have hGend : ∀ ω : Fin n → ℝ, G (B ∪ p.jobsDone B ω) = 0 := by
    intro ω
    set τ := stageSteps B p ω
    by_cases hτ : τ = numRemaining B
    · rw [jobsDone_eq_hist_jobs]
      change G (B ∪ (p.toPolicy.hist ω τ).jobs) = 0
      rw [hτ, feasible_jobs_univ hp_feas ω]
      exact GVal_univ F _ _
    · have hlt : τ < numRemaining B := lt_of_le_of_ne (stageSteps_le B p ω) hτ
      have hnotIn : ¬ p.InStage B ω τ := fun h => lt_irrefl τ ((inStage_iff_lt_stageSteps B p ω τ).mp h)
      have hτpos : 1 ≤ τ := stageSteps_pos hB p ω
      have hprevIn : p.InStage B ω (τ - 1) :=
        (inStage_iff_lt_stageSteps B p ω (τ - 1)).mpr (by omega)
      have hstop_true : p.stop (p.toPolicy.hist ω τ) = true := by
        by_contra hf
        have hfalse : p.stop (p.toPolicy.hist ω τ) = false := Bool.eq_false_iff.mpr hf
        apply hnotIn
        refine ⟨hlt, fun l hl => ?_⟩
        rw [Finset.mem_Icc] at hl
        by_cases hlτ : l = τ
        · exact hlτ ▸ hfalse
        · exact hprevIn.2 l (Finset.mem_Icc.mpr ⟨hl.1, by omega⟩)
      have hle0 : G (B ∪ (p.toPolicy.hist ω τ).jobs) ≤ 0 := by
        simpa [p, G] using hstop_true
      rw [jobsDone_eq_hist_jobs]
      exact le_antisymm hle0 (GVal_nonneg F _ _ _)
  -- Rewrite R - λ W as sum over k of ∫ if InStage k then e^{-γ S_k} w_{J_k}
  rw [stage_reward_eq_aVal hp_feas, stage_time_eq_cVal hp_feas]
  have hint_a : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) else 0)
        (serviceLaw F) := fun k _ =>
    integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => aVal F j)
  have hint_c : ∀ k ∈ Finset.range (numRemaining B),
      Integrable (fun ω => if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0)
        (serviceLaw F) := fun k _ =>
    integrable_step_start B p.toPolicy k (measurableSet_inStage p B k) (fun _ j => cVal F j)
  rw [integral_finsetSum _ hint_a, integral_finsetSum _ hint_c, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  -- Compare with stage_telescope_eq for G!
  have htel := stage_telescope_eq hp_feas G
  have htel_end : ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
      G (B ∪ p.jobsDone B ω) ∂serviceLaw F = 0 := by
    simp [hGend]
  rw [htel_end, sub_zero] at htel
  -- Split off k = 0 from the range sum!
  have hnum_pos : 0 < numRemaining B :=
    Nat.pos_of_ne_zero fun h => hB ((numRemaining_eq_zero_iff B).mp h)
  have hrange : numRemaining B = (numRemaining B - 1) + 1 := by omega
  -- For k ≥ 1, the integrand of R - λ W equals the integrand of htel!
  have hmatch_succ : ∀ k ∈ Finset.range (numRemaining B), k ≠ 0 →
      (∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) else 0) ∂serviceLaw F -
      lam * ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0) ∂serviceLaw F) =
      ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (G (B ∪ (p.toPolicy.hist ω k).jobs) -
            phi F (p.toPolicy.job ω k) * G (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0) ∂serviceLaw F := by
    intro k hk hk0
    rw [← integral_const_mul, ← integral_sub (hint_a k hk) ((hint_c k hk).const_mul lam)]
    congr 1; ext ω
    split_ifs with hIn
    · have hstop_false : p.stop (p.toPolicy.hist ω k) = false :=
        hIn.2 k (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      have hGpos : 0 < G (B ∪ (p.toPolicy.hist ω k).jobs) := by
        simpa [p, G] using hstop_false
      have hDne : B ∪ (p.toPolicy.hist ω k).jobs ≠ Finset.univ := by
        intro h; dsimp [G] at hGpos; rw [h, GVal_univ] at hGpos; exact lt_irrefl _ hGpos
      have hGeqH : G (B ∪ (p.toPolicy.hist ω k).jobs) =
          HVal F (wVal F lam) (phi F) (B ∪ (p.toPolicy.hist ω k).jobs) hDne := by
        dsimp [G] at hGpos ⊢
        rw [GVal_eq_max_HVal F _ _ hDne] at hGpos ⊢
        have hHpos : 0 < HVal F (wVal F lam) (phi F) (B ∪ (p.toPolicy.hist ω k).jobs) hDne := by
          by_contra hle; push Not at hle
          rw [max_eq_left hle] at hGpos; exact lt_irrefl _ hGpos
        exact max_eq_right hHpos.le
      have hjob_eq : p.toPolicy.job ω k = optJob (B ∪ (p.toPolicy.hist ω k).jobs) := rfl
      have hopt_k := (hopt _ hDne).2
      rw [← hGeqH, ← hjob_eq] at hopt_k
      dsimp [wVal] at hopt_k
      have : aVal F (p.toPolicy.job ω k) - lam * cVal F (p.toPolicy.job ω k) =
          G (B ∪ (p.toPolicy.hist ω k).jobs) -
            phi F (p.toPolicy.job ω k) * G (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)) := by
        linarith
      calc Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) -
            lam * (Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k))
          = Real.exp (-F.γ * p.toPolicy.startTime ω k) *
              (aVal F (p.toPolicy.job ω k) - lam * cVal F (p.toPolicy.job ω k)) := by ring
        _ = _ := by rw [this]
    · ring
  -- And compute the k = 0 terms on both sides!
  have hIn0 : ∀ ω, p.InStage B ω 0 := fun ω => ⟨hnum_pos, by simp⟩
  have hjob0 : ∀ ω, p.toPolicy.job ω 0 = optJob B := fun ω => by
    simp [Policy.job, Policy.hist, p, history_jobs_nil]
  have h0_L : (∫ ω, (if p.InStage B ω 0 then
        Real.exp (-F.γ * p.toPolicy.startTime ω 0) * aVal F (p.toPolicy.job ω 0) else 0) ∂serviceLaw F -
      lam * ∫ ω, (if p.InStage B ω 0 then
        Real.exp (-F.γ * p.toPolicy.startTime ω 0) * cVal F (p.toPolicy.job ω 0) else 0) ∂serviceLaw F) =
      wVal F lam (optJob B) := by
    simp only [hIn0, ↓reduceIte, startTime_zero, mul_zero, Real.exp_zero, one_mul, hjob0,
      integral_const, probReal_univ, one_smul, wVal]
  have h0_tel : ∫ ω, (if p.InStage B ω 0 then
      Real.exp (-F.γ * p.toPolicy.startTime ω 0) *
        (G (B ∪ (p.toPolicy.hist ω 0).jobs) -
          phi F (p.toPolicy.job ω 0) * G (insert (p.toPolicy.job ω 0) (B ∪ (p.toPolicy.hist ω 0).jobs)))
      else 0) ∂serviceLaw F =
      G B - phi F (optJob B) * G (insert (optJob B) B) := by
    simp only [hIn0, ↓reduceIte, startTime_zero, mul_zero, Real.exp_zero, one_mul,
      hist_jobs_zero, Finset.union_empty, hjob0, integral_const, probReal_univ, one_smul]
  have hsplit_sum : ∀ f : ℕ → ℝ, ∑ k ∈ Finset.range (numRemaining B), f k =
      f 0 + ∑ k ∈ (Finset.range (numRemaining B)).erase 0, f k := fun f =>
    (Finset.add_sum_erase _ _ (Finset.mem_range.mpr hnum_pos)).symm
  rw [hsplit_sum] at htel ⊢
  have hrest : ∑ k ∈ (Finset.range (numRemaining B)).erase 0,
      (∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * aVal F (p.toPolicy.job ω k) else 0) ∂serviceLaw F -
        lam * ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) * cVal F (p.toPolicy.job ω k) else 0) ∂serviceLaw F) =
      ∑ k ∈ (Finset.range (numRemaining B)).erase 0,
        ∫ ω, (if p.InStage B ω k then
          Real.exp (-F.γ * p.toPolicy.startTime ω k) *
            (G (B ∪ (p.toPolicy.hist ω k).jobs) -
              phi F (p.toPolicy.job ω k) * G (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
        else 0) ∂serviceLaw F := by
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hmatch_succ k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
  rw [h0_L, hrest]
  rw [h0_tel] at htel
  have hoptB := (hopt B hB).2
  linarith

private lemma GVal_familyIndex_eq_zero {F : JobFamily n} {B : Finset (Fin n)} (hB : B ≠ Finset.univ) :
    GVal F (wVal F (familyIndex F B)) (phi F) B = 0 := by
  obtain ⟨p, hp, hEq⟩ := exists_stage_sub_eq_HVal hB (familyIndex F B)
  have hmem : p.ratio F B ∈ {x : ℝ | ∃ q : Stage n, q.Feasible F B ∧ x = q.ratio F B} :=
    ⟨p, hp, rfl⟩
  have hle : p.ratio F B ≤ familyIndex F B :=
    le_csSup (stage_ratio_bddAbove hB) hmem
  have htime : 0 < p.time F B := stage_time_pos hB hp
  have hHle : HVal F (wVal F (familyIndex F B)) (phi F) B hB ≤ 0 := by
    rw [← hEq]
    have : p.reward F B ≤ familyIndex F B * p.time F B := (div_le_iff₀ htime).mp hle
    linarith
  rw [GVal_eq_max_HVal F _ _ hB]
  exact max_eq_left hHle

private lemma UVal_sub_stage_le_index_mul_time {F : JobFamily n} {B : Finset (Fin n)}
    (hB : B ≠ Finset.univ) {p : Stage n} (hp : p.Feasible F B) :
    UVal F (aVal F) (phi F) B -
      ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω) ∂serviceLaw F ≤
      familyIndex F B * p.time F B := by
  classical
  set lam := familyIndex F B
  have htel := stage_telescope_eq hp (deltaTilde F lam)
  have hrhs_nn : 0 ≤ ∑ k ∈ Finset.range (numRemaining B),
      ∫ ω, (if p.InStage B ω k then
        Real.exp (-F.γ * p.toPolicy.startTime ω k) *
          (deltaTilde F lam (B ∪ (p.toPolicy.hist ω k).jobs) -
            phi F (p.toPolicy.job ω k) *
              deltaTilde F lam (insert (p.toPolicy.job ω k) (B ∪ (p.toPolicy.hist ω k).jobs)))
      else 0) ∂serviceLaw F := by
    refine Finset.sum_nonneg fun k hk => ?_
    refine integral_nonneg fun ω => ?_
    split_ifs
    · refine mul_nonneg (Real.exp_pos _).le ?_
      have hav := hp ω k (Finset.mem_range.mp hk)
      linarith [deltaTilde_step F lam hav]
    · exact le_rfl
  have hdt_ge : 0 ≤ deltaTilde F lam B -
      ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        deltaTilde F lam (B ∪ p.jobsDone B ω) ∂serviceLaw F := by linarith
  have hdtB : deltaTilde F lam B = -UVal F (aVal F) (phi F) B + lam * F.γ⁻¹ := by
    unfold deltaTilde
    rw [GVal_familyIndex_eq_zero hB]
    ring
  have hdtEnd_le :
      ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        (-UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω) + lam * F.γ⁻¹) ∂serviceLaw F ≤
      ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        deltaTilde F lam (B ∪ p.jobsDone B ω) ∂serviceLaw F := by
    refine integral_mono
      (integrable_stageEnd_mul B p (fun D => -UVal F (aVal F) (phi F) D + lam * F.γ⁻¹))
      (integrable_stageEnd_mul B p (deltaTilde F lam)) fun ω => ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    unfold deltaTilde
    linarith [GVal_nonneg F (wVal F lam) (phi F) (B ∪ p.jobsDone B ω)]
  have hsplit_end :
      ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        (-UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω) + lam * F.γ⁻¹) ∂serviceLaw F =
      -(∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
          UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω) ∂serviceLaw F) +
      lam * F.γ⁻¹ * ∫ ω, Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) ∂serviceLaw F := by
    have heq : (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        (-UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω) + lam * F.γ⁻¹)) =
      fun ω => -(Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
          UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω)) +
        (lam * F.γ⁻¹) * Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) := by
      ext ω; ring
    have hint_neg : Integrable (fun ω => -(Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)) *
        UVal F (aVal F) (phi F) (B ∪ p.jobsDone B ω))) (serviceLaw F) :=
      (integrable_stageEnd_mul B p (UVal F (aVal F) (phi F))).neg
    have hint_exp : Integrable (fun ω => Real.exp (-F.γ * p.toPolicy.startTime ω (stageSteps B p ω)))
        (serviceLaw F) := by
      simpa using integrable_stageEnd_mul (F := F) B p (fun _ => 1)
    rw [heq, integral_add hint_neg (hint_exp.const_mul (lam * F.γ⁻¹)),
      integral_neg, integral_const_mul]
  rw [hdtB] at hdt_ge
  rw [stage_time_eq_one_sub_exp B p]
  linarith

end PolicyStage

/-! ### Section 5: First-stage splitting & induction for `IsEpsFIStarPolicy` -/

section StageInduction

variable {n : ℕ}

private lemma stagedState_first_stage (ρ : History n → Stage n) (B : Finset (Fin n))
    (ω : Fin n → ℝ) :
    ∀ k ≤ stageSteps B (ρ []) ω,
      (k < stageSteps B (ρ []) ω →
        stagedState ρ ω k = ([], (ρ []).toPolicy.hist ω k) ∧
        stagedJob ρ ω k = (ρ []).toPolicy.job ω k) ∧
      (k = stageSteps B (ρ []) ω → k < numRemaining B →
        stagedState ρ ω k = ((ρ []).toPolicy.hist ω k, [])) := by
  set p₀ := ρ []
  set τ := stageSteps B p₀ ω
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun h0 hlt => ?_⟩
    exfalso
    have hIn0 : p₀.InStage B ω 0 := ⟨hlt, by simp⟩
    have := (inStage_iff_lt_stageSteps B p₀ ω 0).mp hIn0
    omega
  | succ k ih =>
    intro hk_le
    have hprev := (ih (by omega)).1 (by omega)
    have hstep_eq : stagedState ρ ω (k + 1) =
        if p₀.stop (p₀.toPolicy.hist ω (k + 1)) then
          (p₀.toPolicy.hist ω (k + 1), [])
        else ([], p₀.toPolicy.hist ω (k + 1)) := by
      simp only [stagedState, hprev.1, List.nil_append]
      rfl
    refine ⟨fun hk_lt => ?_, fun hk_eq hk_rem => ?_⟩
    · have hIn : p₀.InStage B ω (k + 1) := (inStage_iff_lt_stageSteps B p₀ ω (k + 1)).mpr hk_lt
      have hstop_false : p₀.stop (p₀.toPolicy.hist ω (k + 1)) = false :=
        hIn.2 (k + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      have hst : stagedState ρ ω (k + 1) = ([], p₀.toPolicy.hist ω (k + 1)) := by
        rw [hstep_eq, hstop_false]; simp
      exact ⟨hst, by simp [stagedJob, hst, Policy.job, p₀]⟩
    · have hnotIn : ¬ p₀.InStage B ω (k + 1) := by
        intro h; have := (inStage_iff_lt_stageSteps B p₀ ω (k + 1)).mp h; omega
      have hprevIn : p₀.InStage B ω k := (inStage_iff_lt_stageSteps B p₀ ω k).mpr (by omega)
      have hstop_true : p₀.stop (p₀.toPolicy.hist ω (k + 1)) = true := by
        by_contra hf
        have hfalse := Bool.eq_false_iff.mpr hf
        apply hnotIn
        refine ⟨hk_rem, fun l hl => ?_⟩
        rw [Finset.mem_Icc] at hl
        by_cases hlk : l = k + 1
        · exact hlk ▸ hfalse
        · exact hprevIn.2 l (Finset.mem_Icc.mpr ⟨hl.1, by omega⟩)
      rw [hstep_eq, hstop_true]; simp

private lemma stagedState_shift (ρ : History n → Stage n) (ω : Fin n → ℝ) (τ : ℕ) (h₀ : History n)
    (hτ : stagedState ρ ω τ = (h₀, [])) :
    ∀ r : ℕ,
      stagedState ρ ω (τ + r) =
        (h₀ ++ (stagedState (fun l => ρ (h₀ ++ l)) ω r).1,
          (stagedState (fun l => ρ (h₀ ++ l)) ω r).2) ∧
      stagedJob ρ ω (τ + r) = stagedJob (fun l => ρ (h₀ ++ l)) ω r := by
  intro r
  induction r with
  | zero =>
    refine ⟨by simp [stagedState, hτ], ?_⟩
    simp [stagedJob, stagedState, hτ]
  | succ r ih =>
    have hst : stagedState ρ ω (τ + (r + 1)) =
        (h₀ ++ (stagedState (fun l => ρ (h₀ ++ l)) ω (r + 1)).1,
          (stagedState (fun l => ρ (h₀ ++ l)) ω (r + 1)).2) := by
      rw [← Nat.add_assoc]
      simp only [stagedState, ih.1]
      split_ifs <;> simp [List.append_assoc]
    refine ⟨hst, ?_⟩
    simp [stagedJob, hst]

private def shiftPolicy (h : Policy n) (h₀ : History n) : Policy n where
  next l := h.next (h₀ ++ l)
  measurable_next k := by
    let c : Fin h₀.length → Fin n × ℝ := fun i => h₀[i]
    have hc : List.ofFn c = h₀ := List.ofFn_getElem
    have heq : (fun v : Fin k → Fin n × ℝ => h.next (h₀ ++ List.ofFn v)) =
        (fun w : Fin (h₀.length + k) → Fin n × ℝ => h.next (List.ofFn w)) ∘
        (fun v : Fin k → Fin n × ℝ => Fin.append c v) := by
      ext v
      simp only [Function.comp_apply, ofFn_append, hc]
    rw [heq]
    refine (h.measurable_next (h₀.length + k)).comp ?_
    rw [measurable_pi_iff]
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i₁; simp only [Fin.append_left]; exact measurable_const
    · intro i₂; simp only [Fin.append_right]; exact measurable_pi_apply i₂

private lemma shiftPolicy_hist (h : Policy n) (h₀ : History n) (ω : Fin n → ℝ) (m₀ : ℕ)
    (hm₀ : h.hist ω m₀ = h₀) :
    ∀ r : ℕ, h.hist ω (m₀ + r) = h₀ ++ (shiftPolicy h h₀).hist ω r
  | 0 => by simp [Policy.hist, hm₀]
  | r + 1 => by
    rw [← Nat.add_assoc, Policy.hist, shiftPolicy_hist h h₀ ω m₀ hm₀ r, Policy.hist]
    simp [shiftPolicy, List.append_assoc]

private lemma shiftPolicy_job (h : Policy n) (h₀ : History n) (ω : Fin n → ℝ) (m₀ : ℕ)
    (hm₀ : h.hist ω m₀ = h₀) (r : ℕ) :
    h.job ω (m₀ + r) = (shiftPolicy h h₀).job ω r := by
  simp [Policy.job, shiftPolicy_hist h h₀ ω m₀ hm₀ r, shiftPolicy]

private lemma shiftPolicy_completionTime (h : Policy n) (h₀ : History n) (ω : Fin n → ℝ) (m₀ : ℕ)
    (hm₀ : h.hist ω m₀ = h₀) (r : ℕ) :
    h.completionTime ω (m₀ + r) = h₀.elapsed + (shiftPolicy h h₀).completionTime ω r := by
  simp only [Policy.completionTime]
  rw [Nat.add_assoc, shiftPolicy_hist h h₀ ω m₀ hm₀ (r + 1), history_elapsed_append]

private lemma UVal_sub_le_payoff_of_isEpsFIStar (F : JobFamily n) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ (m : ℕ) (A : Finset (Fin n)), numRemaining A = m →
      ∀ (h : Policy n), IsEpsFIStarPolicy F A ε h →
        UVal F (aVal F) (phi F) A - ε * F.γ⁻¹ ≤ h.payoff F A := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro A hAm h hh
    by_cases hm0 : m = 0
    · have hAuniv : A = Finset.univ := (numRemaining_eq_zero_iff A).mp (hAm.trans hm0)
      subst hAuniv
      simp only [UVal_univ, Policy.payoff, numRemaining, Finset.card_univ, Fintype.card_fin,
        Nat.sub_self, Finset.range_zero, Finset.sum_empty, integral_zero, zero_sub,
        neg_nonpos]
      exact mul_nonneg hε (inv_pos.mpr F.γ_pos).le
    · have hA : A ≠ Finset.univ := fun h => hm0 (hAm.symm.trans ((numRemaining_eq_zero_iff A).mpr h))
      rcases hh with ⟨hfeas, ρ, hρ, hae⟩
      set p₀ := ρ []
      have hp₀_spec : p₀.Feasible F A ∧ familyIndex F A - ε ≤ p₀.ratio F A := by
        simpa [p₀, history_jobs_nil] using hρ [] (by simpa [history_jobs_nil] using hA)
      have hp₀_feas : p₀.Feasible F A := hp₀_spec.1
      have hp₀_rew : (familyIndex F A - ε) * p₀.time F A ≤ p₀.reward F A :=
        (le_div_iff₀ (stage_time_pos hA hp₀_feas)).mp hp₀_spec.2
      -- Tail sum for each subset S
      let tailS : Finset (Fin n) → (Fin n → ℝ) → ℝ := fun S ω =>
        if p₀.jobsDone A ω = S then
          ∑ r ∈ Finset.range (numRemaining (A ∪ S)),
            F.reward (h.job ω (S.card + r)) * Real.exp (-F.γ * h.completionTime ω (S.card + r))
        else 0
      have hint_tailS : ∀ S : Finset (Fin n), Integrable (tailS S) (serviceLaw F) := by
        intro S
        have heq : tailS S = fun ω => ∑ r ∈ Finset.range (numRemaining (A ∪ S)),
            if p₀.jobsDone A ω = S then
              Real.exp (-F.γ * h.completionTime ω (S.card + r)) * F.reward (h.job ω (S.card + r))
            else 0 := by
          ext ω; dsimp [tailS]
          split_ifs
          · refine Finset.sum_congr rfl fun r _ => by ring
          · simp
        rw [heq]
        refine integrable_finsetSum _ fun r _ => ?_
        exact integrable_step_compl (P := fun ω => p₀.jobsDone A ω = S) A h (S.card + r)
          ((measurable_jobsDone A p₀) (measurableSet_singleton S)) (fun _ j => F.reward j)
      -- Split h.payoff F A = p₀.reward F A + ∑ S, ∫ tailS S
      have hpayoff_split : h.payoff F A = p₀.reward F A + ∑ S : Finset (Fin n), ∫ ω, tailS S ω ∂serviceLaw F := by
        unfold Policy.payoff Stage.reward
        have hint_rew : Integrable (fun ω => ∑ k ∈ Finset.range (numRemaining A),
            if p₀.InStage A ω k then
              F.reward (p₀.toPolicy.job ω k) * Real.exp (-F.γ * p₀.toPolicy.completionTime ω k)
            else 0) (serviceLaw F) := by
          refine integrable_finsetSum _ fun k _ => ?_
          have heq : (fun ω => if p₀.InStage A ω k then
              F.reward (p₀.toPolicy.job ω k) * Real.exp (-F.γ * p₀.toPolicy.completionTime ω k) else 0) =
            fun ω => if p₀.InStage A ω k then
              Real.exp (-F.γ * p₀.toPolicy.completionTime ω k) * F.reward (p₀.toPolicy.job ω k) else 0 := by
            ext ω; split_ifs <;> ring
          rw [heq]
          exact integrable_step_compl A p₀.toPolicy k (measurableSet_inStage p₀ A k) (fun _ j => F.reward j)
        rw [← integral_finsetSum _ fun S _ => hint_tailS S,
          ← integral_add hint_rew (integrable_finsetSum _ fun S _ => hint_tailS S)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with ω hω
        set S := p₀.jobsDone A ω
        set τ := stageSteps A p₀ ω
        have hτS : τ = S.card := stageSteps_eq_card_jobsDone hp₀_feas ω
        have hdisj : Disjoint S A := jobsDone_disjoint hp₀_feas ω
        have hcard_union : (A ∪ S).card = A.card + S.card :=
          Finset.card_union_of_disjoint hdisj.symm
        have hrem : numRemaining A = S.card + numRemaining (A ∪ S) := by
          unfold numRemaining
          have hle : (A ∪ S).card ≤ n := by simpa using (A ∪ S).card_le_univ
          omega
        -- Agreement of h and p₀ on first τ steps
        have hhist_eq : ∀ k ≤ τ, h.hist ω k = p₀.toPolicy.hist ω k := by
          intro k
          induction k with
          | zero => intro _; rfl
          | succ k ihk =>
            intro hk_le
            have hlt : k < τ := by omega
            have hlt_rem : k < numRemaining A := lt_of_lt_of_le hlt (stageSteps_le A p₀ ω)
            have hj1 : h.job ω k = stagedJob ρ ω k := hω k hlt_rem
            have hj2 : stagedJob ρ ω k = p₀.toPolicy.job ω k :=
              ((stagedState_first_stage ρ A ω k hlt.le).1 hlt).2
            have hprev := ihk hlt.le
            simp only [Policy.hist, hprev]
            have hnext : h.next (p₀.toPolicy.hist ω k) = p₀.toPolicy.next (p₀.toPolicy.hist ω k) := by
              calc h.next (p₀.toPolicy.hist ω k) = h.job ω k := by simp [Policy.job, hprev]
                _ = stagedJob ρ ω k := hj1
                _ = p₀.toPolicy.job ω k := hj2
            rw [hnext]
        have hjob_eq : ∀ k < τ, h.job ω k = p₀.toPolicy.job ω k := fun k hk => by
          have hlt_rem : k < numRemaining A := lt_of_lt_of_le hk (stageSteps_le A p₀ ω)
          exact (hω k hlt_rem).trans ((stagedState_first_stage ρ A ω k hk.le).1 hk).2
        have hcomp_eq : ∀ k < τ, h.completionTime ω k = p₀.toPolicy.completionTime ω k := fun k hk => by
          simp [Policy.completionTime, hhist_eq (k + 1) hk]
        -- Split range (numRemaining A) = range S.card + shifted range (numRemaining (A ∪ S))
        rw [Finset.sum_eq_single S (fun S' _ hne => by dsimp [tailS]; rw [if_neg (Ne.symm hne)])
          (fun h => absurd (Finset.mem_univ S) h)]
        dsimp [tailS]
        rw [if_pos rfl]
        have hhead : ∑ k ∈ Finset.range (numRemaining A),
            (if p₀.InStage A ω k then
              F.reward (p₀.toPolicy.job ω k) * Real.exp (-F.γ * p₀.toPolicy.completionTime ω k) else 0) =
            ∑ k ∈ Finset.range S.card,
              F.reward (h.job ω k) * Real.exp (-F.γ * h.completionTime ω k) := by
          rw [← Finset.sum_filter, filter_inStage_eq_range, ← hτS]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          rw [hjob_eq k hk', hcomp_eq k hk']
        rw [hhead, hrem, Finset.sum_range_add]
      -- Bound each ∫ tailS S via Fubini + IH!
      have hbound_S : ∀ S : Finset (Fin n),
          ∫ ω, (if p₀.jobsDone A ω = S then
              Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
                (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹)
            else 0) ∂serviceLaw F ≤
          ∫ ω, tailS S ω ∂serviceLaw F := by
        intro S
        by_cases hvalid : S.Nonempty ∧ Disjoint S A
        · rcases hvalid with ⟨hSne, hSdisj⟩
          have hm_lt : numRemaining (A ∪ S) < m := by
            rw [← hAm]
            unfold numRemaining
            rw [Finset.card_union_of_disjoint hSdisj.symm]
            have hScard : 0 < S.card := Finset.card_pos.mpr hSne
            have hle : (A ∪ S).card ≤ n := by simpa using (A ∪ S).card_le_univ
            rw [Finset.card_union_of_disjoint hSdisj.symm] at hle
            omega
          have hmp := measurePreserving_split F S
          have hmp_symm := hmp.symm
          let comb := (splitEquiv S).symm
          -- Define the measurable RHS integrand
          let rhsFn : (Fin n → ℝ) → ℝ := fun ω =>
            if p₀.jobsDone A ω = S then
              Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
                (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹)
            else 0
          have hint_rhs : Integrable rhsFn (serviceLaw F) := by
            have heq : rhsFn = fun ω =>
                Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
                  (if B_eq : p₀.jobsDone A ω = S then UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹ else 0) := by
              ext ω; dsimp [rhsFn]; split_ifs <;> ring
            -- Even simpler: bounded on pos + measurable!
            have hmeas : Measurable rhsFn := by
              refine Measurable.ite ((measurable_jobsDone A p₀) (measurableSet_singleton S)) ?_ measurable_const
              exact (Real.continuous_exp.measurable.comp
                (measurable_const.mul (measurable_stageEndTime A p₀))).mul measurable_const
            refine integrable_bounded_on_pos hmeas |UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹|
              fun ω hpos => ?_
            dsimp [rhsFn]
            split_ifs
            · simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
              have hexp : Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) ≤ 1 :=
                Real.exp_le_one_iff.mpr (by
                  nlinarith [F.γ_pos, startTime_nonneg p₀.toPolicy hpos (stageSteps A p₀ ω)])
              calc Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
                    |UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹|
                  ≤ 1 * |UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹| :=
                    mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
                _ = _ := one_mul _
            · simp [abs_nonneg]
          have hint_L_prod : Integrable (fun p => rhsFn (comb p)) ((subLaw F S).prod (complLaw F S)) :=
            (hmp_symm.integrable_comp_emb (splitEquiv S).symm.measurableEmbedding).mpr hint_rhs
          have hint_R_prod : Integrable (fun p => tailS S (comb p)) ((subLaw F S).prod (complLaw F S)) :=
            (hmp_symm.integrable_comp_emb (splitEquiv S).symm.measurableEmbedding).mpr (hint_tailS S)
          change ∫ ω, rhsFn ω ∂serviceLaw F ≤ ∫ ω, tailS S ω ∂serviceLaw F
          rw [← hmp_symm.integral_comp' rhsFn, ← hmp_symm.integral_comp' (tailS S)]
          rw [integral_prod _ hint_L_prod, integral_prod _ hint_R_prod]
          refine integral_mono_ae hint_L_prod.integral_prod_left hint_R_prod.integral_prod_left ?_
          -- Almost every u has a.e. v satisfying `Good (comb (u, v))`
          have hae_prod : ∀ᵐ p ∂((subLaw F S).prod (complLaw F S)),
              ∀ k < numRemaining A, h.job (comb p) k = stagedJob ρ (comb p) k :=
            hmp_symm.quasiMeasurePreserving.ae hae
          filter_upwards [Measure.ae_ae_of_ae_prod hae_prod] with u hu
          obtain ⟨v₀, hv₀⟩ := hu.exists
          have hagree_S : ∀ v : {i // i ∉ S} → ℝ, ∀ i ∈ S, comb (u, v₀) i = comb (u, v) i := by
            intro v i hi
            rw [splitEquiv_symm_mem u v₀ hi, splitEquiv_symm_mem u v hi]
          by_cases hdone : p₀.jobsDone A (comb (u, v₀)) = S
          · -- Stage 1 finishes exactly S for EVERY v!
            set h₀ := p₀.toPolicy.hist (comb (u, v₀)) S.card
            have hτ₀ : stageSteps A p₀ (comb (u, v₀)) = S.card := by
              rw [stageSteps_eq_card_jobsDone hp₀_feas, hdone]
            have hjobs₀ : h₀.jobs = S := by
              dsimp [h₀]; rw [← hτ₀, ← jobsDone_eq_hist_jobs, hdone]
            have hcongr_v : ∀ v : {i // i ∉ S} → ℝ,
                stageSteps A p₀ (comb (u, v)) = S.card ∧
                p₀.toPolicy.hist (comb (u, v)) S.card = h₀ ∧
                p₀.jobsDone A (comb (u, v)) = S := by
              intro v
              have hc := stageSteps_congr_of_jobsDone (B := A) (p := p₀)
                (ω := comb (u, v₀)) (ω' := comb (u, v))
                (fun i hi => hagree_S v i (hdone ▸ hi))
              refine ⟨by linarith [hc.1, hτ₀], ?_, ?_⟩
              · have := hc.2.1; rw [hτ₀] at this
                have h2 : stageSteps A p₀ (comb (u, v)) = S.card := by linarith [hc.1, hτ₀]
                rw [h2] at this; exact this.symm
              · rw [← hc.2.2, hdone]
            -- Also h.hist (comb (u, v)) S.card = h₀ for EVERY v!
            have hh_hist₀ : h.hist (comb (u, v₀)) S.card = h₀ := by
              have hrec : ∀ k ≤ S.card, h.hist (comb (u, v₀)) k = p₀.toPolicy.hist (comb (u, v₀)) k := by
                intro k
                induction k with
                | zero => intro _; rfl
                | succ k ihk =>
                  intro hk_le
                  have hlt : k < stageSteps A p₀ (comb (u, v₀)) := by omega
                  have hlt_rem : k < numRemaining A := lt_of_lt_of_le hlt (stageSteps_le A p₀ _)
                  have hprev := ihk (by omega)
                  have hj1 := hv₀ k hlt_rem
                  have hj2 := ((stagedState_first_stage ρ A (comb (u, v₀)) k hlt.le).1 hlt).2
                  simp only [Policy.hist, hprev]
                  have hnext : h.next (p₀.toPolicy.hist (comb (u, v₀)) k) =
                      p₀.toPolicy.next (p₀.toPolicy.hist (comb (u, v₀)) k) := by
                    calc h.next (p₀.toPolicy.hist (comb (u, v₀)) k)
                        = h.job (comb (u, v₀)) k := by simp [Policy.job, hprev]
                      _ = stagedJob ρ (comb (u, v₀)) k := hj1
                      _ = p₀.toPolicy.job (comb (u, v₀)) k := hj2
                  rw [hnext]
              exact hrec S.card le_rfl
            have hh_hist_v : ∀ v : {i // i ∉ S} → ℝ, h.hist (comb (u, v)) S.card = h₀ := by
              intro v
              rw [← hh_hist₀]
              exact (hist_congr_of_agree h fun i hi => hagree_S v i (hjobs₀ ▸ hh_hist₀ ▸ hi)).symm
            -- Build shifted policy h' and shifted rule ρ'
            let h' := shiftPolicy h h₀
            let ρ' : History n → Stage n := fun l => ρ (h₀ ++ l)
            have hrem_eq : numRemaining A = S.card + numRemaining (A ∪ S) := by
              unfold numRemaining
              rw [Finset.card_union_of_disjoint hSdisj.symm]
              have hle : (A ∪ S).card ≤ n := by simpa using (A ∪ S).card_le_univ
              rw [Finset.card_union_of_disjoint hSdisj.symm] at hle
              omega
            -- Core agreement for h' on any ω' vs comb (u, ω'|_{Sᶜ})
            have hh'_proj : ∀ (ω' : Fin n → ℝ) (r : ℕ), r ≤ numRemaining (A ∪ S) →
                let v' : {i // i ∉ S} → ℝ := fun i => ω' i.1
                h'.hist ω' r = h'.hist (comb (u, v')) r ∧
                (r < numRemaining (A ∪ S) →
                  IsAvailable F ((A ∪ S) ∪ (h'.hist ω' r).jobs) (h'.job ω' r) ∧
                  h'.job ω' r = h'.job (comb (u, v')) r) := by
              intro ω' r
              let v' : {i // i ∉ S} → ℝ := fun i => ω' i.1
              induction r with
              | zero =>
                intro _
                refine ⟨rfl, fun hlt => ?_⟩
                have hltA : S.card + 0 < numRemaining A := by omega
                have hav := hfeas (comb (u, v')) (S.card + 0) hltA
                rw [Nat.add_zero, hh_hist_v v', hjobs₀] at hav
                have hj_eq' : h'.job ω' 0 = h'.job (comb (u, v')) 0 := rfl
                have hj_eq : h'.job ω' 0 = h.job (comb (u, v')) S.card :=
                  hj_eq'.trans (by simpa [Nat.add_zero] using
                    (shiftPolicy_job h h₀ (comb (u, v')) S.card (hh_hist_v v') 0).symm)
                rw [← hj_eq] at hav
                exact ⟨by simpa [hist_jobs_zero] using hav, hj_eq'⟩
              | succ r ihr =>
                intro hr_le
                have hprev := ihr (by omega)
                have hlt_prev : r < numRemaining (A ∪ S) := by omega
                have ⟨hav_prev, hj_prev⟩ := hprev.2 hlt_prev
                have hj_not_S : h'.job ω' r ∉ S := fun hmem =>
                  hav_prev.1 (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
                have hω_eq : ω' (h'.job ω' r) = comb (u, v') (h'.job ω' r) := by
                  rw [splitEquiv_symm_not_mem u v' hj_not_S]
                have hhist_succ : h'.hist ω' (r + 1) = h'.hist (comb (u, v')) (r + 1) := by
                  simp only [Policy.hist]
                  rw [hprev.1]
                  have : h'.next (h'.hist (comb (u, v')) r) = h'.job ω' r := by
                    rw [← hprev.1]; rfl
                  rw [this, hω_eq]
                refine ⟨hhist_succ, fun hlt => ?_⟩
                have hltA : S.card + (r + 1) < numRemaining A := by omega
                have hav := hfeas (comb (u, v')) (S.card + (r + 1)) hltA
                rw [shiftPolicy_hist h h₀ (comb (u, v')) S.card (hh_hist_v v') (r + 1),
                  history_jobs_append, hjobs₀, ← Finset.union_assoc,
                  shiftPolicy_job h h₀ (comb (u, v')) S.card (hh_hist_v v') (r + 1)] at hav
                have hj_eq : h'.job ω' (r + 1) = h'.job (comb (u, v')) (r + 1) := by
                  simp [Policy.job, hhist_succ]
                rw [← hhist_succ, ← hj_eq] at hav
                exact ⟨hav, hj_eq⟩
            have hh'_feas : h'.Feasible F (A ∪ S) := fun ω' r hr =>
              ((hh'_proj ω' r hr.le).2 hr).1
            -- Show IsEpsFIStarPolicy F (A ∪ S) ε h'
            have hh'_eps : IsEpsFIStarPolicy F (A ∪ S) ε h' := by
              refine ⟨hh'_feas, ρ', ?_, ?_⟩
              · intro l hl
                have hl' : A ∪ (h₀ ++ l).jobs ≠ Finset.univ := by
                  rw [history_jobs_append, hjobs₀, ← Finset.union_assoc]; exact hl
                have hspec := hρ (h₀ ++ l) hl'
                rw [history_jobs_append, hjobs₀, ← Finset.union_assoc] at hspec
                exact hspec
              · have hae_snd : ∀ᵐ p : ({i // i ∈ S} → ℝ) × ({i // i ∉ S} → ℝ)
                    ∂((subLaw F S).prod (complLaw F S)),
                    ∀ k < numRemaining A, h.job (comb (u, p.2)) k = stagedJob ρ (comb (u, p.2)) k :=
                  Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hu
                have hae_ω' : ∀ᵐ ω' ∂serviceLaw F,
                    ∀ k < numRemaining A,
                      h.job (comb (u, (splitEquiv S ω').2)) k =
                        stagedJob ρ (comb (u, (splitEquiv S ω').2)) k :=
                  hmp.quasiMeasurePreserving.ae hae_snd
                filter_upwards [hae_ω'] with ω' hω' r hr
                let v' : {i // i ∉ S} → ℝ := (splitEquiv S ω').2
                have hv'_eq : v' = fun i => ω' i.1 := by
                  ext i; simp [v', splitEquiv, MeasurableEquiv.piEquivPiSubtypeProd]
                have hSlt : S.card < numRemaining A := by omega
                have hst_τ : stagedState ρ (comb (u, v')) S.card = (h₀, []) := by
                  have hcv := hcongr_v v'
                  have hst := (stagedState_first_stage ρ A (comb (u, v')) S.card
                    (by rw [hcv.1])).2 hcv.1.symm hSlt
                  rw [hcv.2.1] at hst
                  exact hst
                -- By induction on t ≤ r, stagedState ρ' ω' t = stagedState ρ' (comb (u, v')) t
                have hst_agree : ∀ t ≤ r, stagedState ρ' ω' t = stagedState ρ' (comb (u, v')) t := by
                  intro t
                  induction t with
                  | zero => intro _; rfl
                  | succ t iht =>
                    intro ht_le
                    have ht_lt : t < numRemaining (A ∪ S) := by omega
                    have hprev := iht (by omega)
                    have hj_st : stagedJob ρ' (comb (u, v')) t = h'.job (comb (u, v')) t := by
                      have h1 := (stagedState_shift ρ (comb (u, v')) S.card h₀ hst_τ t).2
                      have h2 := hω' (S.card + t) (by omega)
                      have h3 := shiftPolicy_job h h₀ (comb (u, v')) S.card (hh_hist_v v') t
                      rw [← h1, ← h2, h3]
                    have hj_not_S : stagedJob ρ' (comb (u, v')) t ∉ S := by
                      rw [hj_st]
                      have hav := hh'_feas (comb (u, v')) t ht_lt
                      exact fun hmem => hav.1 (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
                    have hω'_j : ω' (stagedJob ρ' (comb (u, v')) t) =
                        comb (u, v') (stagedJob ρ' (comb (u, v')) t) := by
                      rw [splitEquiv_symm_not_mem u v' hj_not_S]
                      exact (congrFun hv'_eq ⟨stagedJob ρ' (comb (u, v')) t, hj_not_S⟩).symm
                    simp only [stagedState, hprev]
                    change (let s := stagedState ρ' (comb (u, v')) t
                      let j := (ρ' s.1).next s.2
                      let l := s.2 ++ [(j, ω' j)]
                      if (ρ' s.1).stop l then (s.1 ++ l, []) else (s.1, l)) = _
                    have hj_def : (ρ' (stagedState ρ' (comb (u, v')) t).1).next
                        (stagedState ρ' (comb (u, v')) t).2 = stagedJob ρ' (comb (u, v')) t := rfl
                    simp only [hj_def, hω'_j]
                have hj_r1 : h'.job ω' r = h'.job (comb (u, v')) r := by
                  rw [hv'_eq]; exact ((hh'_proj ω' r hr.le).2 hr).2
                have hj_r2 : h'.job (comb (u, v')) r = stagedJob ρ' (comb (u, v')) r := by
                  have h1 := (stagedState_shift ρ (comb (u, v')) S.card h₀ hst_τ r).2
                  have h2 := hω' (S.card + r) (by omega)
                  have h3 := shiftPolicy_job h h₀ (comb (u, v')) S.card (hh_hist_v v') r
                  rw [← h1, ← h2, h3]
                have hj_r3 : stagedJob ρ' ω' r = stagedJob ρ' (comb (u, v')) r := by
                  simp [stagedJob, hst_agree r le_rfl]
                exact hj_r1.trans (hj_r2.trans hj_r3.symm)
            -- Apply IH to (A ∪ S) and h'!
            have hIH := ih (numRemaining (A ∪ S)) hm_lt (A ∪ S) rfl h' hh'_eps
            -- Compute both inner integrals over v!
            have hLHS_v : ∫ v, rhsFn (comb (u, v)) ∂complLaw F S =
                Real.exp (-F.γ * h₀.elapsed) * (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹) := by
              have hconst : ∀ v, rhsFn (comb (u, v)) =
                  Real.exp (-F.γ * h₀.elapsed) * (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹) := by
                intro v
                have hcv := hcongr_v v
                dsimp [rhsFn]
                rw [if_pos hcv.2.2, hcv.1]
                simp only [Policy.startTime, hcv.2.1]
              simp_rw [hconst]
              rw [integral_const, probReal_univ, one_smul]
            have hRHS_v : ∫ v, tailS S (comb (u, v)) ∂complLaw F S =
                Real.exp (-F.γ * h₀.elapsed) * h'.payoff F (A ∪ S) := by
              have hpt : ∀ v, tailS S (comb (u, v)) =
                  Real.exp (-F.γ * h₀.elapsed) *
                    ∑ r ∈ Finset.range (numRemaining (A ∪ S)),
                      F.reward (h'.job (comb (u, v)) r) *
                        Real.exp (-F.γ * h'.completionTime (comb (u, v)) r) := by
                intro v
                have hcv := hcongr_v v
                dsimp [tailS]
                rw [if_pos hcv.2.2, Finset.mul_sum]
                refine Finset.sum_congr rfl fun r _ => ?_
                rw [shiftPolicy_job h h₀ (comb (u, v)) S.card (hh_hist_v v) r,
                  shiftPolicy_completionTime h h₀ (comb (u, v)) S.card (hh_hist_v v) r,
                  mul_add, Real.exp_add]
                ring
              simp_rw [hpt]
              rw [integral_const_mul]
              congr 1
              -- Show ∫ v, sum(comb (u, v)) = h'.payoff F (A ∪ S)
              unfold Policy.payoff
              rw [← hmp_symm.integral_comp']
              have hprod_eq : ∀ p : ({i // i ∈ S} → ℝ) × ({i // i ∉ S} → ℝ),
                  (∑ r ∈ Finset.range (numRemaining (A ∪ S)),
                    F.reward (h'.job (comb p) r) * Real.exp (-F.γ * h'.completionTime (comb p) r)) =
                  (1 : ℝ) * (∑ r ∈ Finset.range (numRemaining (A ∪ S)),
                    F.reward (h'.job (comb (u, p.2)) r) *
                      Real.exp (-F.γ * h'.completionTime (comb (u, p.2)) r)) := by
                intro ⟨u', v⟩
                rw [one_mul]
                refine Finset.sum_congr rfl fun r hr => ?_
                have hr' := Finset.mem_range.mp hr
                have hv_eq : (fun i : {i // i ∉ S} => comb (u', v) i.1) = v := by
                  ext i; exact splitEquiv_symm_not_mem u' v i.2
                have h1 := hh'_proj (comb (u', v)) r hr'.le
                have h2 := hh'_proj (comb (u', v)) (r + 1) hr'
                rw [hv_eq] at h1 h2
                have hcomp : h'.completionTime (comb (u', v)) r = h'.completionTime (comb (u, v)) r := by
                  simp [Policy.completionTime, h2.1]
                rw [(h1.2 hr').2, hcomp]
              have hfun : (fun p : ({i // i ∈ S} → ℝ) × ({i // i ∉ S} → ℝ) =>
                    ∑ r ∈ Finset.range (numRemaining (A ∪ S)),
                      F.reward (h'.job (comb p) r) * Real.exp (-F.γ * h'.completionTime (comb p) r)) =
                  fun p => (1 : ℝ) * (∑ r ∈ Finset.range (numRemaining (A ∪ S)),
                    F.reward (h'.job (comb (u, p.2)) r) *
                      Real.exp (-F.γ * h'.completionTime (comb (u, p.2)) r)) :=
                funext hprod_eq
              rw [hfun]
              rw [integral_prod_mul (f := fun _ : {i : Fin n // i ∈ S} → ℝ => (1 : ℝ))
                  (g := fun v => ∑ r ∈ Finset.range (numRemaining (A ∪ S)),
                    F.reward (h'.job (comb (u, v)) r) *
                      Real.exp (-F.γ * h'.completionTime (comb (u, v)) r)),
                integral_const, probReal_univ, one_smul, one_mul]
            rw [hLHS_v, hRHS_v]
            exact mul_le_mul_of_nonneg_left hIH (Real.exp_pos _).le
          · -- Stage 1 does NOT finish S for ANY v!
            have hnot_v : ∀ v : {i // i ∉ S} → ℝ, p₀.jobsDone A (comb (u, v)) ≠ S := by
              intro v hEq
              have hc := stageSteps_congr_of_jobsDone (B := A) (p := p₀)
                (ω := comb (u, v)) (ω' := comb (u, v₀))
                (fun i hi => (hagree_S v i (hEq ▸ hi)).symm)
              exact hdone (hc.2.2.symm.trans hEq)
            have h0L : ∀ v, rhsFn (comb (u, v)) = 0 := fun v => by
              dsimp [rhsFn]; rw [if_neg (hnot_v v)]
            have h0R : ∀ v, tailS S (comb (u, v)) = 0 := fun v => by
              dsimp [tailS]; rw [if_neg (hnot_v v)]
            simp_rw [h0L, h0R]; simp
        · -- Invalid S (empty or not disjoint from A): never happens!
          have hnever : ∀ ω, p₀.jobsDone A ω ≠ S := fun ω hEq =>
            hvalid ⟨hEq ▸ jobsDone_nonempty hp₀_feas hA ω, hEq ▸ jobsDone_disjoint hp₀_feas ω⟩
          have h0L : ∀ ω, (if p₀.jobsDone A ω = S then
              Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
                (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹) else 0) = 0 :=
            fun ω => if_neg (hnever ω)
          have h0R : ∀ ω, tailS S ω = 0 := fun ω => by dsimp [tailS]; rw [if_neg (hnever ω)]
          simp_rw [h0L, h0R]; simp
      -- Sum hbound_S over all S : Finset (Fin n)!
      have hsum_bound := Finset.sum_le_sum (s := Finset.univ) fun S _ => hbound_S S
      have hint_rhsS : ∀ S : Finset (Fin n),
          Integrable (fun ω => if p₀.jobsDone A ω = S then
            Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
              (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹) else 0) (serviceLaw F) := by
        intro S
        have hmeas : Measurable (fun ω => if p₀.jobsDone A ω = S then
            Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
              (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹) else 0) :=
          Measurable.ite ((measurable_jobsDone A p₀) (measurableSet_singleton S))
            ((Real.continuous_exp.measurable.comp
              (measurable_const.mul (measurable_stageEndTime A p₀))).mul measurable_const)
            measurable_const
        refine integrable_bounded_on_pos hmeas |UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹|
          fun ω hpos => ?_
        split_ifs
        · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp : Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by
              nlinarith [F.γ_pos, startTime_nonneg p₀.toPolicy hpos (stageSteps A p₀ ω)])
          calc Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
                |UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹|
              ≤ 1 * |UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹| :=
                mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
            _ = _ := one_mul _
        · simp [abs_nonneg]
      rw [← integral_finsetSum _ fun S _ => hint_rhsS S] at hsum_bound
      have hcollapse : (fun ω => ∑ S : Finset (Fin n), if p₀.jobsDone A ω = S then
            Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
              (UVal F (aVal F) (phi F) (A ∪ S) - ε * F.γ⁻¹) else 0) =
          fun ω => Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) *
              UVal F (aVal F) (phi F) (A ∪ p₀.jobsDone A ω) -
            (ε * F.γ⁻¹) * Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)) := by
        ext ω
        rw [Finset.sum_ite_eq Finset.univ (p₀.jobsDone A ω)]
        simp only [Finset.mem_univ, ↓reduceIte]
        ring
      have hint_expA : Integrable (fun ω => Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω)))
          (serviceLaw F) := by
        simpa using integrable_stageEnd_mul (F := F) A p₀ (fun _ => 1)
      rw [hcollapse, integral_sub
        (integrable_stageEnd_mul A p₀ (UVal F (aVal F) (phi F)))
        (hint_expA.const_mul _),
        integral_const_mul] at hsum_bound
      -- Combine with hp₀_rew, UVal_sub_stage_le_index_mul_time, and stage_time_eq_one_sub_exp!
      have hstage_val := UVal_sub_stage_le_index_mul_time hA hp₀_feas
      have hstage_time := stage_time_eq_one_sub_exp (F := F) A p₀
      have hmul1 : (familyIndex F A - ε) * p₀.time F A =
          familyIndex F A * p₀.time F A - ε * p₀.time F A := by ring
      have hmul2 : ε * p₀.time F A =
          ε * F.γ⁻¹ - ε * F.γ⁻¹ * ∫ ω, Real.exp (-F.γ * p₀.toPolicy.startTime ω (stageSteps A p₀ ω))
            ∂serviceLaw F := by
        rw [hstage_time]; ring
      linarith

end StageInduction

end EpsFIStarProof

theorem solution {n : ℕ} (F : AllocationIndices.Precedence.JobFamily n) (A : Finset (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (h : AllocationIndices.Precedence.Policy n)
    (hh : AllocationIndices.Precedence.IsEpsFIStarPolicy F A ε h)
    (g : AllocationIndices.Precedence.Policy n)
    (hg : g.Feasible F A) :
    g.payoff F A - ε * F.γ⁻¹ ≤ h.payoff F A := by
  have h1 := EpsFIStarProof.payoff_le_UVal hg
  have h2 := EpsFIStarProof.UVal_sub_le_payoff_of_isEpsFIStar F ε hε (AllocationIndices.Precedence.numRemaining A) A rfl h hh
  linarith
