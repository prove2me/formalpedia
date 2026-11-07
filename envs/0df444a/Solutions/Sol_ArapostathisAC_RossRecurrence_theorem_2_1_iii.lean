-- Prove2me | solution 1 for ArapostathisAC.RossRecurrence.theorem_2_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:37:14.213696+00:00
-- url     : https://prove2.me/submissions/27afad93-5d7c-47d6-88c4-717748f2e55c

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.RossRecurrence

namespace Ross53Aux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

instance initMeasure_isProb {M : CMP A} (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (initMeasure π i) := by
  unfold initMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance pathMeasure_isProb (M : CMP A) (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (pathMeasure M π i) := by
  unfold pathMeasure; infer_instance

lemma measurableSet_bad' (S : ℕ → Set A) (hS : ∀ j, MeasurableSet (S j)) :
    MeasurableSet {q : ℕ × A | q.2 ∉ S q.1} := by
  have : {q : ℕ × A | q.2 ∉ S q.1} = ⋃ j : ℕ, ({j} : Set ℕ) ×ˢ (S j)ᶜ := by
    ext ⟨j, a⟩; simp
  rw [this]
  exact MeasurableSet.iUnion fun j => (measurableSet_singleton j).prod (hS j).compl

lemma compProd_bad {X : Type*} [MeasurableSpace X] (S : ℕ → Set A) (hS : ∀ j, MeasurableSet (S j))
    (κ : Kernel X ℕ) [IsSFiniteKernel κ]
    (η : Kernel (X × ℕ) A) [IsSFiniteKernel η] (hη : ∀ x j, η (x, j) (S j)ᶜ = 0) (x : X) :
    (κ ⊗ₖ η) x {q : ℕ × A | q.2 ∉ S q.1} = 0 := by
  rw [Kernel.compProd_apply (measurableSet_bad' S hS)]
  have : ∀ j : ℕ, η (x, j) {a | a ∉ S j} = 0 := fun j => hη x j
  simp [this]

lemma compProd_fst_lintegral {X : Type*} [MeasurableSpace X]
    (κ : Kernel X ℕ) [IsSFiniteKernel κ]
    (η : Kernel (X × ℕ) A) [IsMarkovKernel η] (x : X) (g : ℕ → ℝ≥0∞) :
    ∫⁻ q, g q.1 ∂((κ ⊗ₖ η) x) = ∫⁻ j, g j ∂(κ x) := by
  rw [Kernel.lintegral_compProd κ η x (f := fun q : ℕ × A => g q.1)
    ((measurable_of_countable g).comp measurable_fst)]
  simp


lemma stepKernel_bad' (M : CMP A) (π : Policy M) (S : ℕ → Set A) (hS : ∀ j, MeasurableSet (S j))
    (hπ : ∀ t hist, π.rule t hist (S hist.2)ᶜ = 0) (t : ℕ) (h : Π _ : Finset.Iic t, ℕ × A) :
    stepKernel M π t h {q : ℕ × A | q.2 ∉ S q.1} = 0 := by
  have h1 : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t)
      (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap
      (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact compProd_bad S hS _ _ (fun x j => by rw [Kernel.comap_apply]; exact hπ (t + 1) _) h

lemma stepKernel_fst (M : CMP A) (π : Policy M) (t : ℕ) (h : Π _ : Finset.Iic t, ℕ × A)
    (g : ℕ → ℝ≥0∞) :
    ∫⁻ q, g q.1 ∂(stepKernel M π t h) = ∫⁻ j, g j ∂(M.P (h ⟨t, by simp⟩)) := by
  have h1 : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t)
      (measurable_pi_apply _)) := Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap
      (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact compProd_fst_lintegral _ _ h g

lemma map_zero (M : CMP A) (π : Policy M) (i : ℕ) :
    (pathMeasure M π i).map (fun ω => ω 0) = initMeasure π i := by
  have hg : Measurable (fun y : Π _ : Finset.Iic 0, ℕ × A => y ⟨0, by simp⟩) :=
    measurable_pi_apply _
  have hk : (Kernel.traj (X := fun _ => ℕ × A) (stepKernel M π) 0).map (fun ω => ω 0) =
      Kernel.deterministic _ hg := by
    rw [← Kernel.id_map hg, ← Kernel.partialTraj_self (X := fun _ => ℕ × A) (κ := stepKernel M π),
      ← Kernel.traj_map_frestrictLe, ← Kernel.map_comp_right _ (by fun_prop) hg]
    rfl
  unfold pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), hk, Measure.deterministic_comp_eq_map,
    Measure.map_map hg (by fun_prop)]
  convert Measure.map_id
  funext x; rfl

lemma law_succ (M : CMP A) (π : Policy M) (i : ℕ) (a : ℕ) :
    (pathMeasure M π i).map (Preorder.frestrictLe a) ⊗ₘ stepKernel M π a =
      (pathMeasure M π i).map (fun x ↦ (Preorder.frestrictLe a x, x (a + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => ℕ × A) (μ₀ := initMeasure π i) (κ := stepKernel M π) (a := a)

lemma ae_mem (M : CMP A) (π : Policy M) (S : ℕ → Set A) (hS : ∀ j, MeasurableSet (S j))
    (hπ : ∀ t hist, π.rule t hist (S hist.2)ᶜ = 0) (i : ℕ) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M π i), (ω t).2 ∈ S (ω t).1 := by
  rw [ae_iff]
  have hB := measurableSet_bad' S hS
  cases t with
  | zero =>
    have h0 : (pathMeasure M π i) {ω | ¬ (ω 0).2 ∈ S (ω 0).1} =
        ((pathMeasure M π i).map (fun ω => ω 0)) {q : ℕ × A | q.2 ∉ S q.1} := by
      rw [Measure.map_apply (by fun_prop) hB]; rfl
    rw [h0, map_zero]
    unfold initMeasure
    rw [Measure.map_apply (by fun_prop) hB]
    exact hπ 0 (fun j => j.elim0, i)
  | succ a =>
    have := congrArg (fun μ => μ (Set.univ ×ˢ {q : ℕ × A | q.2 ∉ S q.1})) (law_succ M π i a)
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod hB),
      Measure.compProd_apply_prod MeasurableSet.univ hB] at this
    simp only [stepKernel_bad' M π S hS hπ, MeasureTheory.lintegral_zero] at this
    rw [this]; congr 1; ext ω; simp

lemma adm_ae (M : CMP A) (π : Policy M) (i : ℕ) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M π i), (ω t).2 ∈ M.U (ω t).1 :=
  ae_mem M π M.U (fun j => (M.U_compact j).isClosed.measurableSet) π.adm i t

lemma stat_ae (M : CMP A) (f : StationaryPolicy M) (i : ℕ) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M f.toPolicy i), (ω t).2 = f.1 (ω t).1 := by
  have := ae_mem M f.toPolicy (fun j => {f.1 j}) (fun j => measurableSet_singleton _)
    (fun t hist => by
      simp only [StationaryPolicy.toPolicy]
      rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton _).compl]
      simp) i t
  simpa using this

lemma init_ae (M : CMP A) (π : Policy M) (i : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M π i), (ω 0).1 = i := by
  rw [ae_iff]
  have hB : MeasurableSet {q : ℕ × A | q.1 ≠ i} := measurable_fst (measurableSet_singleton i).compl
  have h0 : (pathMeasure M π i) {ω | ¬ (ω 0).1 = i} =
      ((pathMeasure M π i).map (fun ω => ω 0)) {q : ℕ × A | q.1 ≠ i} := by
    rw [Measure.map_apply (by fun_prop) hB]; rfl
  rw [h0, map_zero]
  unfold initMeasure
  rw [Measure.map_apply (by fun_prop) hB]
  simp

/-- One step of the Markov property, in `lintegral` form, with an `𝓕_t`-measurable weight. -/
lemma one_step (M : CMP A) (π : Policy M) (i t : ℕ)
    (F : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞) (hF : Measurable F) (g : ℕ → ℝ≥0∞) :
    ∫⁻ ω, F (Preorder.frestrictLe t ω) * g (ω (t + 1)).1 ∂(pathMeasure M π i) =
      ∫⁻ ω, F (Preorder.frestrictLe t ω) * ∫⁻ j, g j ∂(M.P (ω t)) ∂(pathMeasure M π i) := by
  have hg : Measurable g := measurable_of_countable g
  have hG : Measurable (fun x : ℕ × A => ∫⁻ j, g j ∂(M.P x)) := Measurable.lintegral_kernel hg
  have e1 : ∫⁻ ω, F (Preorder.frestrictLe t ω) * g (ω (t + 1)).1 ∂(pathMeasure M π i) =
      ∫⁻ p, F p.1 * g p.2.1 ∂((pathMeasure M π i).map
        (fun x ↦ (Preorder.frestrictLe t x, x (t + 1)))) := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
  rw [e1, ← law_succ, Measure.lintegral_compProd (by fun_prop)]
  have e2 : ∫⁻ ω, F (Preorder.frestrictLe t ω) * ∫⁻ j, g j ∂(M.P (ω t)) ∂(pathMeasure M π i) =
      ∫⁻ h, F h * ∫⁻ j, g j ∂(M.P (h ⟨t, by simp⟩))
        ∂((pathMeasure M π i).map (Preorder.frestrictLe t)) := by
    rw [lintegral_map (f := fun h : (Π _ : Finset.Iic t, ℕ × A) =>
      F h * ∫⁻ j, g j ∂(M.P (h ⟨t, by simp⟩)))
      (by exact hF.mul (hG.comp (measurable_pi_apply _))) (by fun_prop)]
    rfl
  rw [e2]
  refine lintegral_congr fun h => ?_
  dsimp only
  rw [lintegral_const_mul (F h) (f := fun q : ℕ × A => g q.1) (hg.comp measurable_fst),
    stepKernel_fst]

lemma M0_nonneg (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀) : 0 ≤ M₀ := by
  obtain ⟨a, ha⟩ := M.U_nonempty 0
  exact (M.c_nonneg 0 a ha).trans (hc 0 a ha)

/-- A stationary deterministic policy exists (choice from the nonempty `U i`). -/
noncomputable def someStat (M : CMP A) : StationaryPolicy M :=
  ⟨fun i => (M.U_nonempty i).some, fun i => (M.U_nonempty i).some_mem⟩

lemma discCost_le (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (π : Policy M) (i : ℕ) :
    discCost M π β i ≤ ENNReal.ofReal (M₀ / (1 - β)) := by
  have hM := M0_nonneg M M₀ hc
  have hae : ∀ᵐ ω ∂(pathMeasure M π i), ∀ t, (ω t).2 ∈ M.U (ω t).1 :=
    ae_all_iff.2 (adm_ae M π i)
  have hgeom : ∑' t : ℕ, ENNReal.ofReal (β ^ t * M₀) = ENNReal.ofReal (M₀ / (1 - β)) := by
    have hs : Summable (fun t : ℕ => β ^ t * M₀) :=
      (summable_geometric_of_lt_one hβ.1.le hβ.2).mul_right _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ.1.le t) hM) hs,
      tsum_mul_right, tsum_geometric_of_lt_one hβ.1.le hβ.2, div_eq_inv_mul]
  unfold discCost
  calc ∫⁻ ω, ∑' t, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) ∂(pathMeasure M π i)
      ≤ ∫⁻ _ω, ENNReal.ofReal (M₀ / (1 - β)) ∂(pathMeasure M π i) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with ω hω
        rw [← hgeom]
        exact ENNReal.tsum_le_tsum fun t => ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hc _ _ (hω t)) (pow_nonneg hβ.1.le t))
    _ = ENNReal.ofReal (M₀ / (1 - β)) := by simp

lemma discValue_le (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    discValue M β i ≤ ENNReal.ofReal (M₀ / (1 - β)) :=
  (iInf_le _ (someStat M).toPolicy).trans (discCost_le M M₀ hc β hβ _ i)

/-- Bernoulli: `1 - β^K ≤ K (1 - β)` for `K ≥ 1`, `β ∈ (0,1)`. -/
lemma one_sub_rpow_le (β K : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hK : 1 ≤ K) :
    1 - β ^ K ≤ K * (1 - β) := by
  have := one_add_mul_self_le_rpow_one_add (s := β - 1) (by linarith [hβ.1]) hK
  have e : (1 : ℝ) + (β - 1) = β := by ring
  rw [e] at this
  nlinarith

end Ross53Aux

namespace Ross53Aux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The Bellman expression `c(i,a) + β Σ_j P(j|i,a) v(j)` in `[0, ∞]`. -/
noncomputable def G (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) (a : A) : ℝ≥0∞ :=
  ENNReal.ofReal (M.c i a) + ENNReal.ofReal β * ∫⁻ j, v j ∂(M.P (i, a))

/-- The Bellman operator. -/
noncomputable def T (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  ⨅ a : M.U i, G M β v i a

lemma G_mono (M : CMP A) (β : ℝ) {v w : ℕ → ℝ≥0∞} (h : v ≤ w) (i : ℕ) (a : A) :
    G M β v i a ≤ G M β w i a := by
  unfold G
  gcongr
  exact h _

lemma T_mono (M : CMP A) (β : ℝ) {v w : ℕ → ℝ≥0∞} (h : v ≤ w) : T M β v ≤ T M β w :=
  fun i => iInf_mono fun a => G_mono M β h i a

lemma T_le_G (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) (a : A) (ha : a ∈ M.U i) :
    T M β v i ≤ G M β v i a :=
  iInf_le (fun a : M.U i => G M β v i a) ⟨a, ha⟩

lemma lsc_mul_cont (k : ℝ≥0∞) {s : Set A} {p : A → ℝ≥0∞} (hp : ContinuousOn p s) :
    LowerSemicontinuousOn (fun a => k * p a) s := by
  by_cases hk : k = ⊤
  · subst hk
    have : (fun a => ⊤ * p a) = fun a => ⨆ n : ℕ, (n : ℝ≥0∞) * p a := by
      funext a; rw [← ENNReal.iSup_mul, ENNReal.iSup_natCast]
    rw [this]
    exact lowerSemicontinuousOn_iSup fun n =>
      ((ENNReal.continuous_const_mul (ENNReal.natCast_ne_top n)).comp_continuousOn hp).lowerSemicontinuousOn
  · exact ((ENNReal.continuous_const_mul hk).comp_continuousOn hp).lowerSemicontinuousOn

lemma G_lsc (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) :
    LowerSemicontinuousOn (G M β v i) (M.U i) := by
  have e : G M β v i = fun a => ENNReal.ofReal (M.c i a) +
      ∑' j, (ENNReal.ofReal β * v j) * M.P (i, a) {j} := by
    funext a
    unfold G
    rw [lintegral_countable', ← ENNReal.tsum_mul_left]
    congr 1; congr 1; funext j; ring
  rw [e]
  refine LowerSemicontinuousOn.add ?_ ?_
  · exact (ENNReal.continuous_ofReal.comp_continuousOn (M.c_cont i)).lowerSemicontinuousOn
  · refine lowerSemicontinuousOn_tsum fun j => lsc_mul_cont _ ?_
    have : (fun a => M.P (i, a) {j}) = fun a => ENNReal.ofReal ((M.P (i, a) {j}).toReal) := by
      funext a; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.continuous_ofReal.comp_continuousOn (M.P_cont i j)

lemma exists_min (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (i : ℕ) :
    ∃ a ∈ M.U i, T M β v i = G M β v i a := by
  obtain ⟨a, ha, hmin⟩ := (G_lsc M β v i).exists_isMinOn (M.U_nonempty i) (M.U_compact i)
  refine ⟨a, ha, le_antisymm (T_le_G M β v i a ha) ?_⟩
  exact le_iInf fun b => hmin b.2

/-- Value iteration from `0`. -/
noncomputable def vi (M : CMP A) (β : ℝ) : ℕ → ℕ → ℝ≥0∞
  | 0 => 0
  | n + 1 => T M β (vi M β n)

lemma vi_mono (M : CMP A) (β : ℝ) : Monotone (vi M β) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact fun _ => zero_le
  | succ n ih => exact T_mono M β ih

noncomputable def Vstar (M : CMP A) (β : ℝ) : ℕ → ℝ≥0∞ := ⨆ n, vi M β n

lemma Vstar_apply (M : CMP A) (β : ℝ) (j : ℕ) : Vstar M β j = ⨆ n, vi M β n j := by
  simp [Vstar, iSup_apply]

lemma G_iSup (M : CMP A) (β : ℝ) (i : ℕ) (a : A) :
    G M β (Vstar M β) i a = ⨆ m, G M β (vi M β m) i a := by
  unfold G
  have : ∫⁻ j, Vstar M β j ∂(M.P (i, a)) = ⨆ m, ∫⁻ j, vi M β m j ∂(M.P (i, a)) := by
    simp_rw [Vstar_apply]
    exact lintegral_iSup (fun m => measurable_of_countable _) (fun m n h => vi_mono M β h)
  rw [this, ENNReal.mul_iSup, ENNReal.add_iSup]

lemma le_T_Vstar (M : CMP A) (β : ℝ) : Vstar M β ≤ T M β (Vstar M β) := by
  intro j
  rw [Vstar_apply]
  refine iSup_le fun n => ?_
  cases n with
  | zero => exact zero_le
  | succ n => exact T_mono M β (le_iSup (vi M β) n) j

lemma T_Vstar_le (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) : T M β (Vstar M β) ≤ Vstar M β := by
  intro i
  choose a ha hT using fun n => exists_min M β (vi M β n) i
  obtain ⟨a₀, ha₀, φ, hφ, hlim⟩ := (M.U_compact i).tendsto_subseq ha
  have hlim' : Tendsto (a ∘ φ) atTop (𝓝[M.U i] a₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => ha _⟩
  refine (T_le_G M β _ i a₀ ha₀).trans ?_
  rw [G_iSup]
  refine iSup_le fun m => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hev := (G_lsc M β (vi M β m) i a₀ ha₀) _ hcon
  have hev2 := hlim'.eventually hev
  obtain ⟨n, hn⟩ := (hev2.and (eventually_ge_atTop m)).exists
  have h1 : G M β (vi M β m) i (a (φ n)) ≤ Vstar M β i := by
    calc G M β (vi M β m) i (a (φ n)) ≤ G M β (vi M β (φ n)) i (a (φ n)) :=
          G_mono M β (vi_mono M β (hn.2.trans (hφ.id_le n))) i _
      _ = vi M β (φ n + 1) i := (hT (φ n)).symm
      _ ≤ Vstar M β i := by rw [Vstar_apply]; exact le_iSup (fun k => vi M β k i) _
  exact absurd hn.1 (not_lt.2 h1)

lemma T_Vstar (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) : T M β (Vstar M β) = Vstar M β :=
  le_antisymm (T_Vstar_le M β hβ) (le_T_Vstar M β)

/-- The discounted one-stage cost at time `s` along a path. -/
noncomputable def cterm (M : CMP A) (β : ℝ) (s : ℕ) (ω : ℕ → ℕ × A) : ℝ≥0∞ :=
  ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2)

lemma measurable_cterm (M : CMP A) (β : ℝ) (s : ℕ) : Measurable (cterm M β s) :=
  (((M.c_meas.comp (measurable_pi_apply s))).const_mul _).ennreal_ofReal

lemma measurable_wt {t : ℕ} {F : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun ω : ℕ → ℕ × A => F (Preorder.frestrictLe t ω)) :=
  hF.comp (Preorder.measurable_frestrictLe t)

/-- The basic step: integrate the Bellman expression at time `t` against an `𝓕_t` weight. -/
lemma step_eq (M : CMP A) (π : Policy M) (i : ℕ) (β : ℝ) (hβ : 0 ≤ β) (t : ℕ)
    (F : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞) (hF : Measurable F) (w : ℕ → ℝ≥0∞) :
    ∫⁻ ω, F (Preorder.frestrictLe t ω) * (ENNReal.ofReal (β ^ t) * G M β w (ω t).1 (ω t).2)
        ∂(pathMeasure M π i) =
      ∫⁻ ω, F (Preorder.frestrictLe t ω) * cterm M β t ω ∂(pathMeasure M π i) +
      ∫⁻ ω, F (Preorder.frestrictLe₂ (Nat.le_succ t) (Preorder.frestrictLe (t + 1) ω)) *
        (ENNReal.ofReal (β ^ (t + 1)) * w (ω (t + 1)).1) ∂(pathMeasure M π i) := by
  have hpt : 0 ≤ β ^ t := pow_nonneg hβ t
  have e : ∀ ω : ℕ → ℕ × A,
      F (Preorder.frestrictLe t ω) * (ENNReal.ofReal (β ^ t) * G M β w (ω t).1 (ω t).2) =
      F (Preorder.frestrictLe t ω) * cterm M β t ω +
      (F (Preorder.frestrictLe t ω) * ENNReal.ofReal (β ^ (t + 1))) *
        ∫⁻ j, w j ∂(M.P (ω t)) := by
    intro ω
    unfold G cterm
    rw [ENNReal.ofReal_mul hpt, pow_succ, ENNReal.ofReal_mul hpt]
    ring
  simp_rw [e]
  rw [lintegral_add_left (f := fun ω => F (Preorder.frestrictLe t ω) * cterm M β t ω)
    (by exact (measurable_wt hF).mul (measurable_cterm M β t))]
  congr 1
  rw [← one_step M π i t (fun h => F h * ENNReal.ofReal (β ^ (t + 1))) (hF.mul_const _) w]
  refine lintegral_congr fun ω => ?_
  rw [← Function.comp_apply (f := Preorder.frestrictLe₂ (Nat.le_succ t)),
    Preorder.frestrictLe₂_comp_frestrictLe]
  ring

lemma init_eq (M : CMP A) (π : Policy M) (i : ℕ) (w : ℕ → ℝ≥0∞) :
    ∫⁻ ω, w (ω 0).1 ∂(pathMeasure M π i) = w i := by
  rw [lintegral_congr_ae (by filter_upwards [init_ae M π i] with ω hω; rw [hω])]
  simp

/-- (A): the `k`-stage value-iteration bound, with an `𝓕_t` weight. -/
lemma vi_le (M : CMP A) (π : Policy M) (i : ℕ) (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) :
    ∀ t (F : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞), Measurable F →
    ∫⁻ ω, F (Preorder.frestrictLe t ω) * (ENNReal.ofReal (β ^ t) * vi M β k (ω t).1)
        ∂(pathMeasure M π i) ≤
      ∫⁻ ω, F (Preorder.frestrictLe t ω) * ∑ s ∈ Finset.range k, cterm M β (t + s) ω
        ∂(pathMeasure M π i) := by
  induction k with
  | zero => intro t F hF; simp [vi]
  | succ k ih =>
    intro t F hF
    have hle : ∀ᵐ ω ∂(pathMeasure M π i),
        F (Preorder.frestrictLe t ω) * (ENNReal.ofReal (β ^ t) * vi M β (k + 1) (ω t).1) ≤
        F (Preorder.frestrictLe t ω) * (ENNReal.ofReal (β ^ t) * G M β (vi M β k) (ω t).1 (ω t).2) := by
      filter_upwards [adm_ae M π i t] with ω hω
      gcongr
      exact T_le_G M β _ _ _ hω
    refine (lintegral_mono_ae hle).trans ?_
    rw [step_eq M π i β hβ t F hF]
    have ih' := ih (t + 1) (fun h : (Π _ : Finset.Iic (t + 1), ℕ × A) =>
      F (Preorder.frestrictLe₂ (π := fun _ => ℕ × A) (Nat.le_succ t) h))
      (by exact hF.comp (Preorder.measurable_frestrictLe₂ (X := fun _ => ℕ × A) (Nat.le_succ t)))
    refine (add_le_add le_rfl ih').trans ?_
    rw [← lintegral_add_left (f := fun ω => F (Preorder.frestrictLe t ω) * cterm M β t ω)
      (by exact (measurable_wt hF).mul (measurable_cterm M β t))]
    refine lintegral_mono fun ω => ?_
    rw [← Function.comp_apply (f := Preorder.frestrictLe₂ (Nat.le_succ t)),
      Preorder.frestrictLe₂_comp_frestrictLe, ← mul_add, Finset.sum_range_succ']
    apply le_of_eq
    congr 1
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1; omega

lemma Vstar_le_discCost (M : CMP A) (π : Policy M) (i : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    Vstar M β i ≤ discCost M π β i := by
  rw [Vstar_apply]
  refine iSup_le fun k => ?_
  have h := vi_le M π i β hβ k 0 (fun _ => 1) measurable_const
  simp only [one_mul, pow_zero, ENNReal.ofReal_one, zero_add] at h
  rw [init_eq] at h
  refine h.trans (lintegral_mono fun ω => ?_)
  exact ENNReal.sum_le_tsum _

lemma Vstar_le_discValue (M : CMP A) (i : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    Vstar M β i ≤ discValue M β i :=
  le_iInf fun π => Vstar_le_discCost M π i β hβ

/-- (B): along a stationary policy attaining the Bellman minimum for `Vstar`, the telescoped
identity holds. -/
lemma telescope_eq (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) (f : StationaryPolicy M)
    (hf : ∀ x, G M β (Vstar M β) x (f.1 x) = Vstar M β x) (i : ℕ) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∫⁻ ω, cterm M β t ω ∂(pathMeasure M f.toPolicy i) +
      ∫⁻ ω, ENNReal.ofReal (β ^ n) * Vstar M β (ω n).1 ∂(pathMeasure M f.toPolicy i) =
      Vstar M β i := by
  induction n with
  | zero => simp [init_eq]
  | succ n ih =>
    have hs := step_eq M f.toPolicy i β hβ n (fun _ => 1) measurable_const (Vstar M β)
    simp only [one_mul] at hs
    have hV : ∫⁻ ω, ENNReal.ofReal (β ^ n) * Vstar M β (ω n).1 ∂(pathMeasure M f.toPolicy i) =
        ∫⁻ ω, ENNReal.ofReal (β ^ n) * G M β (Vstar M β) (ω n).1 (ω n).2
          ∂(pathMeasure M f.toPolicy i) := by
      refine lintegral_congr_ae ?_
      filter_upwards [stat_ae M f i n] with ω hω
      rw [hω, hf]
    rw [hV, hs] at ih
    rw [Finset.sum_range_succ, add_assoc]
    exact ih

lemma discCost_le_Vstar (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) (f : StationaryPolicy M)
    (hf : ∀ x, G M β (Vstar M β) x (f.1 x) = Vstar M β x) (i : ℕ) :
    discCost M f.toPolicy β i ≤ Vstar M β i := by
  show ∫⁻ ω, ∑' t, cterm M β t ω ∂(pathMeasure M f.toPolicy i) ≤ _
  rw [lintegral_tsum (fun t => (measurable_cterm M β t).aemeasurable)]
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← telescope_eq M β hβ f hf i n]
  exact le_self_add

lemma exists_opt (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ f : StationaryPolicy M, (∀ x, G M β (Vstar M β) x (f.1 x) = Vstar M β x) ∧
      IsDiscOptimal M f β ∧ ∀ i, discValue M β i = Vstar M β i := by
  choose g hg hgT using fun x => exists_min M β (Vstar M β) x
  let f : StationaryPolicy M := ⟨g, hg⟩
  have hf : ∀ x, G M β (Vstar M β) x (f.1 x) = Vstar M β x := fun x => by
    rw [← hgT x, T_Vstar M β hβ]
  have key : ∀ i, discCost M f.toPolicy β i = discValue M β i ∧ discValue M β i = Vstar M β i := by
    intro i
    have h1 := discCost_le_Vstar M β hβ f hf i
    have h2 := Vstar_le_discValue M i β hβ
    have h3 : discValue M β i ≤ discCost M f.toPolicy β i := iInf_le _ _
    exact ⟨le_antisymm (h1.trans h2) h3, le_antisymm (h3.trans h1) h2⟩
  exact ⟨f, hf, fun i => (key i).1, fun i => (key i).2⟩

end Ross53Aux

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, IsDiscOptimal M f β := by
  obtain ⟨f, -, hf, -⟩ := Ross53Aux.exists_opt M β hβ.1.le
  exact ⟨f, hf⟩
