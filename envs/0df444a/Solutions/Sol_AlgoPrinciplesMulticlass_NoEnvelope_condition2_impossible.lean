-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.condition2_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:10:11.082005+00:00
-- url     : https://prove2.me/submissions/f0b00b68-32b5-4873-8d60-eb3c740bafce

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Randomized
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction
universe u

section
namespace AlgoPrinciplesMulticlass
open NoEnvelope MeasureTheory


instance : Countable Pt := by
  have : Function.Injective (fun x : Pt => (⟨x.d, (x.v, x.j)⟩ : Σ d : ℕ, List (Fin d → Bool) × Fin d)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  exact this.countable

namespace Dev.Cond2

open scoped Classical in
/-- fiber counting -/
lemma card_le_of_exists_update {d ℓ : ℕ} (i : Fin ℓ) (E : (Fin ℓ → Fin d) → Prop)
    (hE : ∀ u : Fin ℓ → Fin d, ∃ j, E (Function.update u i j)) :
    d ^ ℓ ≤ d * (Finset.univ.filter E).card := by
  choose j hj using hE
  have h1 : (Finset.univ : Finset (Fin ℓ → Fin d)).card = d ^ ℓ := by simp
  rw [← h1]
  have h2 := Finset.card_le_mul_card_image (f := fun u => Function.update u i (j u))
    (Finset.univ : Finset (Fin ℓ → Fin d)) d ?_
  · refine h2.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro v hv
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hj u⟩
  · intro v hv
    have := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (fun u : Fin ℓ → Fin d => Function.update u i (j u) = v)) (t := (Finset.univ : Finset (Fin d)))
      (fun u => u i) (by intros; simp) ?_
    · simpa using this
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      funext k
      by_cases hk : k = i
      · subst hk; exact hxy
      · have e1 := congrFun hx k
        have e2 := congrFun hy k
        simp only [Function.update_of_ne hk] at e1 e2
        rw [e1, e2]

open scoped Classical in
/-- main counting -/
lemma bad_count {d m ℓ : ℕ} (hm : 1 ≤ m) (hl : ℓ = 4 * m) (T : Finset (Fin ℓ)) (hT : 3 * m ≤ T.card)
    (E : (Fin ℓ → Fin d) → Fin ℓ → Prop)
    (hE : ∀ i ∈ T, ∀ u : Fin ℓ → Fin d, ∃ j, E (Function.update u i j) i) :
    d ^ ℓ ≤ 2 * d * (Finset.univ.filter
      (fun u : Fin ℓ → Fin d => m < d * (Finset.univ.filter (fun i => E u i)).card)).card := by
  set Dn := d ^ ℓ with hDn
  set B := (Finset.univ.filter
      (fun u : Fin ℓ → Fin d => m < d * (Finset.univ.filter (fun i => E u i)).card)).card with hB
  set N : (Fin ℓ → Fin d) → ℕ := fun u => (Finset.univ.filter (fun i => E u i)).card with hN
  have hcard : (Finset.univ : Finset (Fin ℓ → Fin d)).card = Dn := by simp [hDn]
  -- sum of N
  have hsum : T.card * Dn ≤ d * ∑ u, N u := by
    have : ∑ u, N u = ∑ i, (Finset.univ.filter (fun u => E u i)).card := by
      simp only [hN, Finset.card_filter]
      exact Finset.sum_comm
    rw [this, Finset.mul_sum]
    calc T.card * Dn = ∑ i ∈ T, Dn := by simp
      _ ≤ ∑ i ∈ T, d * (Finset.univ.filter (fun u => E u i)).card :=
          Finset.sum_le_sum (fun i hi => card_le_of_exists_update i _ (hE i hi))
      _ ≤ ∑ i, d * (Finset.univ.filter (fun u => E u i)).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hNle : ∀ u, N u ≤ ℓ := fun u => by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin ℓ)) (fun i => E u i)
    simpa using this
  have hpt : ∀ u, d * N u ≤ (if m < d * N u then d * ℓ else m) := by
    intro u
    split_ifs with h
    · exact Nat.mul_le_mul_left _ (hNle u)
    · omega
  have h3 : d * ∑ u, N u ≤ B * (d * ℓ) + Dn * m := by
    rw [Finset.mul_sum]
    calc ∑ u, d * N u ≤ ∑ u : Fin ℓ → Fin d, (if m < d * N u then d * ℓ else m) :=
          Finset.sum_le_sum (fun u _ => hpt u)
      _ ≤ ∑ u : Fin ℓ → Fin d, ((if m < d * N u then d * ℓ else 0) + m) := by
          apply Finset.sum_le_sum; intro u _; split_ifs <;> omega
      _ = B * (d * ℓ) + Dn * m := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter]
          simp [hB, hN, hcard, Finset.sum_const]
  subst hl
  nlinarith

variable {d ℓ : ℕ}

/-- the parameter along the path `b` with choices `u` -/
def prm (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) : Param :=
  ⟨d, ℓ, hℓ, fun i => b i, u⟩

/-- the `i`-th public point -/
def pt (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) (i : Fin ℓ) : Pt :=
  (prm b hℓ u).publicPoint i

lemma pt_eq (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) (i : Fin ℓ) :
    pt b hℓ u i = ⟨d, List.ofFn (fun k : Fin i => b k), u i⟩ := by
  unfold pt Param.publicPoint prm
  congr 1
  refine List.ext_get (by simp [i.2.le]) (fun n h1 h2 => by simp)

lemma pt_inj (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) (i i' : Fin ℓ)
    (h : pt b hℓ u i = pt b hℓ u i') : i = i' := by
  rw [pt_eq, pt_eq] at h
  have := congrArg (fun x : Pt => x.v.length) h
  simp only [List.length_ofFn] at this
  exact Fin.ext this

lemma hyp_pt (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) (i : Fin ℓ) :
    hyp (prm b hℓ u) (pt b hℓ u i) = Label.pub (b i (u i)) := by
  have h : ∃ i' : Fin (prm b hℓ u).ℓ, pt b hℓ u i = (prm b hℓ u).publicPoint i' := ⟨i, rfl⟩
  unfold hyp
  rw [dif_pos h]
  have hc := h.choose_spec
  have : h.choose = i := (pt_inj b hℓ u i h.choose hc).symm
  rw [this]
  rfl

/-- labeled sample at the visited indices -/
noncomputable def smp (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) {m : ℕ} (a : Fin m → Fin ℓ) (u : Fin ℓ → Fin d) :
    Fin m → Pt × Label :=
  labelSample (hyp (prm b hℓ u)) (fun k => pt b hℓ u (a k))

lemma smp_update (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) {m : ℕ} (a : Fin m → Fin ℓ)
    (u : Fin ℓ → Fin d) (i : Fin ℓ) (hi : ∀ k, a k ≠ i) (j : Fin d) :
    smp b hℓ a (Function.update u i j) = smp b hℓ a u := by
  funext k
  simp only [smp, labelSample]
  rw [hyp_pt, hyp_pt]
  simp only [pt_eq, Function.update_of_ne (hi k)]


scoped instance msPt : MeasurableSpace Pt := ⊤
attribute [scoped instance] RandLearner.msΩ

/-- uniform measure on `Fin ℓ` -/
noncomputable def Unif (ℓ : ℕ) : Measure (Fin ℓ) := (ℓ : ENNReal)⁻¹ • Measure.count

/-- the distribution `D_u` -/
noncomputable def Dm (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) : Measure Pt :=
  (Unif ℓ).map (pt b hℓ u)

lemma unif_apply (s : Set (Fin ℓ)) [DecidablePred (· ∈ s)] :
    Unif ℓ s = (ℓ : ENNReal)⁻¹ * (Finset.univ.filter (· ∈ s)).card := by
  simp only [Unif, Measure.smul_apply, smul_eq_mul]
  rw [Measure.count_apply_finite' (Set.toFinite _) (MeasurableSet.of_discrete)]
  have : (Set.toFinite s).toFinset = Finset.univ.filter (· ∈ s) := by ext; simp
  rw [this]

lemma unif_prob (hℓ : 1 ≤ ℓ) : IsProbabilityMeasure (Unif ℓ) := by
  constructor
  classical
  rw [unif_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by simpa using Nat.pos_iff_ne_zero.1 hℓ) (by simp)

lemma Dm_prob (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) :
    IsProbabilityMeasure (Dm b hℓ u) := by
  have := unif_prob hℓ
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable

open scoped Classical in
lemma popLoss_Dm (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (u : Fin ℓ → Fin d) (g h : Pt → Label) :
    popLoss (Dm b hℓ u) g h = (ℓ : ENNReal)⁻¹ *
      ((Finset.univ.filter (fun i => g (pt b hℓ u i) ≠ h (pt b hℓ u i))).card : ENNReal) := by
  classical
  unfold popLoss Dm
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete, unif_apply]
  simp only [Set.mem_preimage, Set.mem_setOf_eq]

lemma lt_iff {m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (N : ℕ) :
    ENNReal.ofReal (1 / (4 * (d : ℝ))) < ((4 * m : ℕ) : ENNReal)⁻¹ * (N : ENNReal) ↔ m < d * N := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : ((4 * m : ℕ) : ENNReal)⁻¹ * (N : ENNReal) = ENNReal.ofReal ((N : ℝ) / (4 * m)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.div_eq_inv_mul]
  rw [this, ENNReal.ofReal_lt_ofReal_iff']
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  constructor
  · rintro ⟨h1, -⟩
    have : (m : ℝ) < d * N := by nlinarith
    exact_mod_cast this
  · intro h
    have h' : (m : ℝ) < d * N := by exact_mod_cast h
    have hN : (0 : ℝ) < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp at h
      · exact_mod_cast h0
    refine ⟨by nlinarith, by positivity⟩


open scoped Classical in
lemma sum_lower {α Ω ι : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure (α × Ω)) [IsProbabilityMeasure ν] (F : ι → Set (α × Ω))
    (hF : ∀ u, MeasurableSet (F u)) (c k : ℕ)
    (h : ∀ x, c ≤ k * (Finset.univ.filter (fun u => x ∈ F u)).card) :
    (c : ENNReal) ≤ k * ∑ u, ν (F u) := by
  classical
  calc (c : ENNReal) = ∫⁻ _, (c : ENNReal) ∂ν := by simp
    _ ≤ ∫⁻ x, (k : ENNReal) * ∑ u, (F u).indicator 1 x ∂ν := by
        apply lintegral_mono
        intro x
        show (c : ENNReal) ≤ (k : ENNReal) * ∑ u, (F u).indicator 1 x
        have : ∑ u, (F u).indicator (1 : α × Ω → ENNReal) x =
            ((Finset.univ.filter (fun u => x ∈ F u)).card : ENNReal) := by
          simp [Set.indicator_apply, Finset.sum_boole]
        rw [this]
        exact_mod_cast h x
    _ = k * ∑ u, ν (F u) := by
        rw [lintegral_const_mul' _ _ (by simp),
          lintegral_finsetSum _ (fun u _ => measurable_one.indicator (hF u))]
        simp [lintegral_indicator_one (hF _)]

/-- the bad set -/
def Fset (R : RandLearner.{u} Pt Label) (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (m : ℕ) (ε : ℝ)
    (u : Fin ℓ → Fin d) : Set ((Fin m → Fin ℓ) × R.Ω) :=
  {p | ENNReal.ofReal ε < popLoss (Dm b hℓ u) (R.A p.2 m (smp b hℓ p.1 u)) (hyp (prm b hℓ u))}

lemma Fset_le (R : RandLearner.{u} Pt Label) (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (m : ℕ) (ε : ℝ)
    (u : Fin ℓ → Fin d) :
    ((Measure.pi fun _ : Fin m => Unif ℓ).prod R.μ) (Fset R b hℓ m ε u) ≤
      R.failProb (hyp (prm b hℓ u)) (Dm b hℓ u) m ε := by
  have := unif_prob hℓ
  have := Dm_prob b hℓ u
  have := R.isProb
  have hpi : Measure.pi (fun _ : Fin m => Dm b hℓ u) =
      (Measure.pi fun _ : Fin m => Unif ℓ).map (fun a k => pt b hℓ u (a k)) := by
    exact (Measure.pi_map_pi (μ := fun _ : Fin m => Unif ℓ) (f := fun _ => pt b hℓ u)
      (fun _ => Measurable.of_discrete.aemeasurable)).symm
  have hφ : Measurable (fun (a : Fin m → Fin ℓ) k => pt b hℓ u (a k)) :=
    measurable_pi_lambda _ (fun k => Measurable.of_discrete.comp (measurable_pi_apply k))
  have key := Measure.map_prod_map (Measure.pi fun _ : Fin m => Unif ℓ) R.μ hφ
    (measurable_id : Measurable (id : R.Ω → R.Ω))
  rw [Measure.map_id] at key
  unfold RandLearner.failProb
  show _ ≤ (Measure.pi (fun _ : Fin m => Dm b hℓ u)).prod R.μ _
  rw [hpi, key]
  exact Measure.le_map_apply (hφ.prodMap measurable_id).aemeasurable _

lemma Fset_meas (R : RandLearner.{u} Pt Label) (b : ℕ → Fin d → Bool) (hℓ : 1 ≤ ℓ) (m : ℕ) (ε : ℝ)
    (u : Fin ℓ → Fin d) : MeasurableSet (Fset R b hℓ m ε u) := by
  classical
  have h1 : Fset R b hℓ m ε u = ⋃ a : Fin m → Fin ℓ, {a} ×ˢ
      {ω | ENNReal.ofReal ε < popLoss (Dm b hℓ u) (R.A ω m (smp b hℓ a u)) (hyp (prm b hℓ u))} := by
    ext ⟨a, ω⟩; simp [Fset]
  rw [h1]
  refine MeasurableSet.iUnion (fun a => (measurableSet_singleton a).prod ?_)
  have hg : Measurable (fun ω => popLoss (Dm b hℓ u) (R.A ω m (smp b hℓ a u)) (hyp (prm b hℓ u))) := by
    simp only [popLoss_Dm, Finset.card_filter]
    refine Measurable.const_mul ?_ _
    push_cast
    refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
    exact (R.meas m (smp b hℓ a u) (pt b hℓ u i)) (MeasurableSpace.measurableSet_top (s := {y | y ≠ _}))
  exact measurableSet_lt measurable_const hg


theorem main (R : RandLearner.{u} Pt Label) (hR : R.PACLearns H) (d : ℕ) (hd : 1 ≤ d) :
    ¬ Condition2 R.image d := by
  classical
  rintro ⟨b, hb⟩
  unfold RealizesOnBlock at hb
  push_neg at hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hε0 : (0 : ℝ) < 1 / (4 * (d : ℝ)) := by positivity
  have hε1 : 1 / (4 * (d : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨n, hn⟩ := hR _ _ hε0 hε1 hε0 hε1
  obtain ⟨m, hm⟩ : ∃ m, m = max n 1 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hnm : n ≤ m := by omega
  obtain ⟨ℓ, hl⟩ : ∃ ℓ, ℓ = 4 * m := ⟨_, rfl⟩
  have hℓ : 1 ≤ ℓ := by omega
  have hfail : ∀ u : Fin ℓ → Fin d, R.failProb (hyp (prm b hℓ u)) (Dm b hℓ u) m (1 / (4 * (d : ℝ)))
      ≤ ENNReal.ofReal (1 / (4 * (d : ℝ))) := fun u =>
    hn m hnm _ ⟨_, rfl⟩ (Dm b hℓ u) (Dm_prob b hℓ u)
  have := unif_prob hℓ
  have := R.isProb
  have hpt : ∀ x : (Fin m → Fin ℓ) × R.Ω, d ^ ℓ ≤ 2 * d *
      (Finset.univ.filter (fun u : Fin ℓ → Fin d =>
        x ∈ Fset R b hℓ m (1 / (4 * (d : ℝ))) u)).card := by
    rintro ⟨a, ω⟩
    have h := bad_count (d := d) (m := m) (ℓ := ℓ) hm1 hl
      (Finset.univ \ Finset.univ.image a)
      (by
        have h1 := Finset.le_card_sdiff (Finset.univ.image a) (Finset.univ : Finset (Fin ℓ))
        have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := a)
        simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
        omega)
      (fun u i => R.A ω m (smp b hℓ a u) (pt b hℓ u i) ≠ hyp (prm b hℓ u) (pt b hℓ u i))
      (by
        intro i hi u
        have hi' : ∀ k, a k ≠ i := by
          intro k hk
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and, not_exists] at hi
          exact hi k hk
        obtain ⟨j, hj⟩ := hb i _ ⟨ω, m, smp b hℓ a u, rfl⟩
        refine ⟨j, ?_⟩
        rw [smp_update b hℓ a u i hi', hyp_pt, pt_eq]
        simpa [block] using hj)
    refine h.trans (Nat.mul_le_mul_left _ (le_of_eq ?_))
    congr 1
    apply Finset.filter_congr
    intro u _
    simp only [Fset, Set.mem_setOf_eq, popLoss_Dm]
    have e : (ℓ : ENNReal) = ((4 * m : ℕ) : ENNReal) := by rw [hl]
    rw [e, lt_iff hd hm1]
    convert Iff.rfl
  have hsum := sum_lower ((Measure.pi fun _ : Fin m => Unif ℓ).prod R.μ)
    (Fset R b hℓ m (1 / (4 * (d : ℝ)))) (Fset_meas R b hℓ m _) (d ^ ℓ) (2 * d) hpt
  have hle : ∑ u : Fin ℓ → Fin d, ((Measure.pi fun _ : Fin m => Unif ℓ).prod R.μ)
      (Fset R b hℓ m (1 / (4 * (d : ℝ))) u) ≤ (d ^ ℓ : ℕ) * ENNReal.ofReal (1 / (4 * (d : ℝ))) := by
    calc _ ≤ ∑ u : Fin ℓ → Fin d, ENNReal.ofReal (1 / (4 * (d : ℝ))) :=
          Finset.sum_le_sum (fun u _ => (Fset_le R b hℓ m _ u).trans (hfail u))
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : ((d ^ ℓ : ℕ) : ENNReal) ≤ ((2 * d : ℕ) : ENNReal) *
      (((d ^ ℓ : ℕ) : ENNReal) * ENNReal.ofReal (1 / (4 * (d : ℝ)))) := by
    refine hsum.trans ?_
    push_cast at hle ⊢
    gcongr
  have h3 := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0.le] at h3
  simp only [ENNReal.toReal_natCast] at h3
  have hD : (0 : ℝ) < ((d ^ ℓ : ℕ) : ℝ) := by positivity
  have : ((2 * d : ℕ) : ℝ) * (1 / (4 * (d : ℝ))) = 1 / 2 := by
    push_cast; field_simp; ring
  nlinarith

end Dev.Cond2

open scoped Dev.Cond2 in
theorem chk_condition2_impossible (R : RandLearner.{u} Pt Label) (hR : R.PACLearns H) (d : ℕ)
    (hd : 1 ≤ d) :
    ¬ Condition2 R.image d := Dev.Cond2.main R hR d hd

end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_condition2_impossible := @AlgoPrinciplesMulticlass.chk_condition2_impossible
