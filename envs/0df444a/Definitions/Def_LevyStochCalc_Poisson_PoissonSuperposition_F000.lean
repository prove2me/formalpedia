-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000
-- name    : LevyStochCalc_Poisson_PoissonSuperposition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:20:29.262211+00:00
-- url     : https://prove2.me/theorems/2c3903d7-774c-4ab2-b637-b7c78c3251bd
-- title:
--   Source declarations: LevyStochCalc.Poisson.PoissonSuperposition
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PoissonSuperposition. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F001
import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F002
import Definitions.Def_LevyStochCalc_Probability_IndepGrouping_F000
import Mathlib.Probability.Independence.CharacteristicFunction

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Superposition of independent Poisson pieces

Given weights `r p ≥ 0` and probability laws `ρ p` on a measurable space `𝓧`, indexed by a
countable type, the *superposition* is the random measure `N = ∑ₚ Nₚ` where the pieces
`Nₚ = ∑_{j < Kₚ} δ_{X_{p,j}}` are independent, `Kₚ` is Poisson with mean `r p`, and the marks
`X_{p,j}` are independent with law `ρ p`. Its intensity is `Λ = ∑ₚ r p • ρ p`.

The sample space is the product `ι → ULift ℕ × (ℕ → 𝓧)` with the product law, and the
distributional facts about a single piece reduce to Poisson splitting.
-/

open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

/-- The coordinates of one Poisson piece: a count and a sequence of marks. -/
abbrev PieceSpace (𝓧 : Type u) : Type u := ULift.{u} ℕ × (ℕ → 𝓧)
/-- The law of one piece: a Poisson count independent of a sequence of iid marks. -/
noncomputable def pieceLaw (r : ℝ≥0) (ρ : Measure 𝓧) : Measure (PieceSpace 𝓧) :=
  (Po(r).map ULift.up).prod (Measure.infinitePi fun _ : ℕ => ρ)
instance (r : ℝ≥0) (ρ : Measure 𝓧) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (pieceLaw r ρ) := by
  haveI : IsProbabilityMeasure (Po(r).map ULift.up) :=
    Measure.isProbabilityMeasure_map measurable_up.aemeasurable
  unfold pieceLaw
  infer_instance
/-- The count of a piece on a set: the number of its marks falling in `B`. -/
noncomputable def pieceCountOn (B : Set 𝓧) (θ : PieceSpace 𝓧) : ℕ :=
  markCount (fun θ : PieceSpace 𝓧 => θ.1.down) (fun j θ => θ.2 j) B θ
lemma measurable_pieceCountOn {B : Set 𝓧} (hB : MeasurableSet B) :
    Measurable (pieceCountOn B) :=
  markCount_measurable (measurable_down.comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp measurable_snd) hB
/-- The atomic measure of one piece, `∑_{j < K} δ_{Xⱼ}`. -/
noncomputable def pieceMeasure (θ : PieceSpace 𝓧) : Measure 𝓧 :=
  ∑ j ∈ Finset.range θ.1.down, Measure.dirac (θ.2 j)
lemma pieceMeasure_apply (θ : PieceSpace 𝓧) {B : Set 𝓧} (hB : MeasurableSet B) :
    pieceMeasure θ B = (pieceCountOn B θ : ℝ≥0∞) := by
  unfold pieceMeasure pieceCountOn markCount
  rw [Measure.finsetSum_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.dirac_apply' _ hB]
  by_cases h : θ.2 j ∈ B <;> simp [h]
variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

/-- The law of the superposition sample space: independent pieces. -/
noncomputable def superLaw : Measure (ι → PieceSpace 𝓧) :=
  Measure.infinitePi fun p => pieceLaw (r p) (ρ p)
instance : IsProbabilityMeasure (superLaw r ρ) := by
  unfold superLaw
  infer_instance
/-- The intensity of the superposition, `∑ₚ r p • ρ p`. -/
noncomputable def superIntensity : Measure 𝓧 :=
  Measure.sum fun p => (r p : ℝ≥0∞) • ρ p
omit [∀ p, IsProbabilityMeasure (ρ p)] in
lemma superIntensity_apply {B : Set 𝓧} (hB : MeasurableSet B) :
    superIntensity r ρ B = ∑' p, r p * ρ p B := by
  unfold superIntensity
  rw [Measure.sum_apply _ hB]
  simp [Measure.smul_apply]
variable {r ρ}

/-- The count of a piece. -/
def pieceCount (p : ι) (ω : ι → PieceSpace 𝓧) : ℕ := (ω p).1.down
/-- A mark of a piece. -/
def pieceMark (p : ι) (j : ℕ) (ω : ι → PieceSpace 𝓧) : 𝓧 := (ω p).2 j
lemma measurable_pieceCount (p : ι) : Measurable (pieceCount p : (ι → PieceSpace 𝓧) → ℕ) :=
  measurable_down.comp (measurable_fst.comp (measurable_pi_apply p))
lemma measurable_pieceMark (p : ι) (j : ℕ) :
    Measurable (pieceMark p j : (ι → PieceSpace 𝓧) → 𝓧) :=
  (measurable_pi_apply j).comp (measurable_snd.comp (measurable_pi_apply p))
omit [MeasurableSpace 𝓧] in
lemma markCount_pieceCount (p : ι) (B : Set 𝓧) (ω : ι → PieceSpace 𝓧) :
    markCount (pieceCount p) (pieceMark p) B ω = pieceCountOn B (ω p) := rfl
/-- The superposition of the pieces. -/
noncomputable def superposition (ω : ι → PieceSpace 𝓧) : Measure 𝓧 :=
  Measure.sum fun p => pieceMeasure (ω p)
lemma superposition_apply (ω : ι → PieceSpace 𝓧) {B : Set 𝓧} (hB : MeasurableSet B) :
    superposition ω B = ∑' p, (pieceCountOn B (ω p) : ℝ≥0∞) := by
  unfold superposition
  rw [Measure.sum_apply _ hB]
  simp_rw [pieceMeasure_apply _ hB]
variable (r ρ)

lemma iIndepFun_eval : iIndepFun (fun p (ω : ι → PieceSpace 𝓧) => ω p) (superLaw r ρ) :=
  iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
lemma map_eval_superLaw (p : ι) : (superLaw r ρ).map (Function.eval p) = pieceLaw (r p) (ρ p) :=
  (measurePreserving_eval_infinitePi _ p).map_eq
lemma map_pieceCount (p : ι) : (superLaw r ρ).map (pieceCount p) = Po(r p) := by
  change (superLaw r ρ).map (ULift.down ∘ Prod.fst ∘ Function.eval p) = _
  rw [← Measure.map_map measurable_down (measurable_fst.comp (measurable_pi_apply p)),
    ← Measure.map_map measurable_fst (measurable_pi_apply p), map_eval_superLaw, pieceLaw,
    Measure.map_fst_prod, measure_univ, one_smul, Measure.map_map measurable_down measurable_up]
  exact Measure.map_id
lemma hasLaw_pieceCount (p : ι) : HasLaw (pieceCount p) Po(r p) (superLaw r ρ) :=
  ⟨(measurable_pieceCount p).aemeasurable, map_pieceCount r ρ p⟩
lemma map_pieceMarks (p : ι) :
    (superLaw r ρ).map (fun ω j => pieceMark p j ω) = Measure.infinitePi fun _ : ℕ => ρ p := by
  change (superLaw r ρ).map (Prod.snd ∘ Function.eval p) = _
  rw [← Measure.map_map measurable_snd (measurable_pi_apply p), map_eval_superLaw, pieceLaw,
    Measure.map_snd_prod, measure_univ, one_smul]
lemma map_pieceMark (p : ι) (j : ℕ) : (superLaw r ρ).map (pieceMark p j) = ρ p := by
  change (superLaw r ρ).map (Function.eval j ∘ fun ω k => pieceMark p k ω) = _
  rw [← Measure.map_map (measurable_pi_apply j)
    (measurable_pi_lambda _ fun k => measurable_pieceMark p k), map_pieceMarks,
    (measurePreserving_eval_infinitePi _ j).map_eq]
lemma hasLaw_pieceMark (p : ι) (j : ℕ) : HasLaw (pieceMark p j) (ρ p) (superLaw r ρ) :=
  ⟨(measurable_pieceMark p j).aemeasurable, map_pieceMark r ρ p j⟩
lemma iIndepFun_pieceMark (p : ι) : iIndepFun (pieceMark p) (superLaw r ρ) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun j => measurable_pieceMark p j, map_pieceMarks]
  congr
  funext j
  exact (map_pieceMark r ρ p j).symm
lemma indepFun_pieceCount_pieceMark (p : ι) :
    IndepFun (pieceCount p) (fun ω j => pieceMark p j ω) (superLaw r ρ) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pieceCount p).aemeasurable
    (measurable_pi_lambda _ fun j => measurable_pieceMark p j).aemeasurable, map_pieceCount,
    map_pieceMarks]
  change (superLaw r ρ).map (Prod.map ULift.down id ∘ Function.eval p) = _
  rw [← Measure.map_map (measurable_down.prodMap measurable_id) (measurable_pi_apply p),
    map_eval_superLaw, pieceLaw, ← Measure.map_prod_map _ _ measurable_down measurable_id,
    Measure.map_map measurable_down measurable_up, Measure.map_id]
  exact congrArg (fun μ => Measure.prod μ _) Measure.map_id
/-- The count of a piece on a set has the Poisson law of mean `r p • ρ p B`, as an
`ℝ≥0∞`-valued random variable. -/
lemma map_pieceCountOn_ennreal (p : ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    (superLaw r ρ).map (fun ω => (pieceCountOn B (ω p) : ℝ≥0∞))
      = Po(r p * (ρ p B).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) :=
  map_markCount_ennreal (hasLaw_pieceCount r ρ p) (measurable_pieceCount p)
    (hasLaw_pieceMark r ρ p) (measurable_pieceMark p) (iIndepFun_pieceMark r ρ p)
    (indepFun_pieceCount_pieceMark r ρ p) (B := fun _ : Fin 1 => B) (fun _ => hB)
    (fun i j h => absurd (Subsingleton.elim i j) h) 0
/-- The count of a piece on a set has the Poisson law of mean `r p • ρ p B`, as a real random
variable. -/
lemma hasLaw_pieceCountOn_real (p : ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    HasLaw (fun ω => (pieceCountOn B (ω p) : ℝ)) Po(ℝ, r p * (ρ p B).toNNReal) (superLaw r ρ) :=
  hasLaw_markCount_real (hasLaw_pieceCount r ρ p) (measurable_pieceCount p)
    (hasLaw_pieceMark r ρ p) (measurable_pieceMark p) (iIndepFun_pieceMark r ρ p)
    (indepFun_pieceCount_pieceMark r ρ p) (B := fun _ : Fin 1 => B) (fun _ => hB)
    (fun i j h => absurd (Subsingleton.elim i j) h) 0
/-- The counts of a piece on pairwise disjoint sets are independent. -/
lemma iIndepFun_pieceCountOn_ennreal (p : ι) {ι' : Type*} {B : ι' → Set 𝓧}
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => (pieceCountOn (B i) (ω p) : ℝ≥0∞)) (superLaw r ρ) :=
  iIndepFun_markCount_ennreal' (hasLaw_pieceCount r ρ p) (measurable_pieceCount p)
    (hasLaw_pieceMark r ρ p) (measurable_pieceMark p) (iIndepFun_pieceMark r ρ p)
    (indepFun_pieceCount_pieceMark r ρ p) hB hdisj
variable {r ρ}

lemma measurable_pieceCountOn_eval (p : ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    Measurable fun ω : ι → PieceSpace 𝓧 => (pieceCountOn B (ω p) : ℝ≥0∞) :=
  (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ≥0∞))).comp
    ((measurable_pieceCountOn hB).comp (measurable_pi_apply p))
variable (r ρ)

/-- The mean of the Poisson law, as a Lebesgue integral. -/
lemma lintegral_natCast_poissonMeasure (r : ℝ≥0) : ∫⁻ n, (n : ℝ≥0∞) ∂Po(r) = r := by
  rw [lintegral_countable']
  simp_rw [poissonMeasure_singleton]
  have h : ∀ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / n.factorial)
      = ENNReal.ofReal (n * (Real.exp (-r) * r ^ n / n.factorial)) := fun n => by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [h]
  set f : ℕ → ℝ := fun n => (n : ℝ) * (Real.exp (-r) * r ^ n / n.factorial) with hf
  have key : ∀ n, f (n + 1) = (r : ℝ) * (Real.exp (-r) * r ^ n / n.factorial) := by
    intro n
    simp only [hf, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have hsum : HasSum f r := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton]
    have h0 : f 0 = 0 := by simp [hf]
    rw [h0, sub_zero]
    simp_rw [key]
    simpa using (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq,
    ENNReal.ofReal_coe_nnreal]
lemma lintegral_pieceCountOn (p : ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    ∫⁻ ω, (pieceCountOn B (ω p) : ℝ≥0∞) ∂(superLaw r ρ) = r p * ρ p B := by
  calc ∫⁻ ω, (pieceCountOn B (ω p) : ℝ≥0∞) ∂(superLaw r ρ)
      = ∫⁻ x, x ∂((superLaw r ρ).map fun ω => (pieceCountOn B (ω p) : ℝ≥0∞)) :=
        (lintegral_map measurable_id (measurable_pieceCountOn_eval p hB)).symm
    _ = ∫⁻ x, x ∂(Po(r p * (ρ p B).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) := by
        rw [map_pieceCountOn_ennreal r ρ p hB]
    _ = ∫⁻ n, (n : ℝ≥0∞) ∂Po(r p * (ρ p B).toNNReal) :=
        lintegral_map measurable_id Measurable.of_discrete
    _ = r p * ρ p B := by
        rw [lintegral_natCast_poissonMeasure, ENNReal.coe_mul,
          ENNReal.coe_toNNReal (measure_ne_top _ _)]
variable [Countable ι]

lemma measurable_superposition {B : Set 𝓧} (hB : MeasurableSet B) :
    Measurable fun ω : ι → PieceSpace 𝓧 => superposition ω B := by
  have : (fun ω : ι → PieceSpace 𝓧 => superposition ω B)
      = fun ω => ∑' p, (pieceCountOn B (ω p) : ℝ≥0∞) := funext fun ω => superposition_apply ω hB
  rw [this]
  exact Measurable.tsum fun p => measurable_pieceCountOn_eval p hB
/-- The mean of the superposition on a set is its intensity. -/
theorem lintegral_superposition {B : Set 𝓧} (hB : MeasurableSet B) :
    ∫⁻ ω, superposition ω B ∂(superLaw r ρ) = superIntensity r ρ B := by
  simp_rw [superposition_apply _ hB]
  rw [lintegral_tsum fun p => (measurable_pieceCountOn_eval p hB).aemeasurable,
    superIntensity_apply r ρ hB]
  exact tsum_congr fun p => lintegral_pieceCountOn r ρ p hB
theorem ae_lt_top_superposition {B : Set 𝓧} (hB : MeasurableSet B)
    (hfin : superIntensity r ρ B ≠ ⊤) : ∀ᵐ ω ∂(superLaw r ρ), superposition ω B < ⊤ :=
  ae_lt_top (measurable_superposition hB) (by rwa [lintegral_superposition r ρ hB])
end Piece

section Exhaustion

/-- A countable type is exhausted by an increasing sequence of finite sets. -/
lemma exists_finset_exhaustion (ι : Type*) [Countable ι] :
    ∃ F : ℕ → Finset ι, Monotone F ∧ ∀ s : Finset ι, ∃ m, s ⊆ F m := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨fun m => (Finset.range m).preimage e he.injOn, fun m _ hmm' x hx => ?_,
    fun s => ⟨s.sup e + 1, fun x hx => ?_⟩⟩
  · rw [Finset.mem_preimage, Finset.mem_range] at hx ⊢
    exact hx.trans_le hmm'
  · rw [Finset.mem_preimage, Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := e) hx
lemma tendsto_finset_exhaustion {ι : Type*} {F : ℕ → Finset ι} (hF : Monotone F)
    (hcof : ∀ s : Finset ι, ∃ m, s ⊆ F m) : Tendsto F atTop atTop :=
  Filter.tendsto_atTop_atTop.2 fun s =>
    let ⟨m, hm⟩ := hcof s
    ⟨m, fun _ hm' => hm.trans (hF hm')⟩
lemma tendsto_sum_exhaustion {ι : Type*} {F : ℕ → Finset ι} (hF : Tendsto F atTop atTop)
    (f : ι → ℝ≥0∞) : Tendsto (fun m => ∑ p ∈ F m, f p) atTop (𝓝 (∑' p, f p)) :=
  (ENNReal.summable (f := f)).hasSum.comp hF
end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

/-- The sum of the counts of finitely many pieces on a set, as a real random variable. -/
noncomputable def partialCount (F : Finset ι) (B : Set 𝓧) (ω : ι → PieceSpace 𝓧) : ℝ :=
  ∑ p ∈ F, (pieceCountOn B (ω p) : ℝ)
variable {r ρ}

lemma measurable_pieceCountOn_eval_real (p : ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    Measurable fun ω : ι → PieceSpace 𝓧 => (pieceCountOn B (ω p) : ℝ) :=
  (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp
    ((measurable_pieceCountOn hB).comp (measurable_pi_apply p))
lemma measurable_partialCount (F : Finset ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    Measurable (partialCount F B) :=
  Finset.measurable_sum _ fun p _ => measurable_pieceCountOn_eval_real p hB
omit [MeasurableSpace 𝓧] in
lemma partialCount_eq_toReal (F : Finset ι) (B : Set 𝓧) (ω : ι → PieceSpace 𝓧) :
    partialCount F B ω = (∑ p ∈ F, (pieceCountOn B (ω p) : ℝ≥0∞)).toReal := by
  unfold partialCount
  rw [ENNReal.toReal_sum fun p _ => ENNReal.natCast_ne_top _]
  simp [ENNReal.toReal_natCast]
variable (r ρ)

lemma iIndepFun_pieceCountOn_eval_real {B : Set 𝓧} (hB : MeasurableSet B) :
    iIndepFun (fun p ω => (pieceCountOn B (ω p) : ℝ)) (superLaw r ρ) :=
  (iIndepFun_eval r ρ).comp (fun _ θ => (pieceCountOn B θ : ℝ)) fun _ =>
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pieceCountOn hB)
/-- The sum of the counts of finitely many independent pieces is Poisson. -/
lemma map_partialCount (F : Finset ι) {B : Set 𝓧} (hB : MeasurableSet B) :
    (superLaw r ρ).map (partialCount F B) = Po(ℝ, ∑ p ∈ F, r p * (ρ p B).toNNReal) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have h := (iIndepFun_iff_finset.1 (iIndepFun_pieceCountOn_eval_real r ρ hB) F)
    |>.charFun_map_fun_finsetSum_eq_prod fun p _ =>
      (measurable_pieceCountOn_eval_real p hB).aemeasurable
  unfold partialCount
  rw [congrFun h t, Finset.prod_apply, charFun_map_cast_poissonMeasure]
  simp_rw [(hasLaw_pieceCountOn_real r ρ _ hB).map_eq, charFun_map_cast_poissonMeasure]
  rw [← Complex.exp_sum, ← Finset.sum_mul]
  push_cast
  rfl
variable [Countable ι]

end Law

end LevyStochCalc.Poisson


