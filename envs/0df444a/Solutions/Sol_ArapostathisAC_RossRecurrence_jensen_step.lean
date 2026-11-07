-- Prove2me | solution 1 for ArapostathisAC.RossRecurrence.jensen_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:44:43.073201+00:00
-- url     : https://prove2.me/submissions/66729b65-3fe4-481a-955b-4e9a6dd4fc36

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
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

namespace Ross53Aux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

lemma one_le_returnTime (ω : ℕ → ℕ × A) : 1 ≤ returnTime ω := by
  unfold returnTime
  apply le_sInf
  rintro _ ⟨t, ht, rfl⟩
  show (1 : ℕ∞) ≤ (t : ℕ∞)
  exact_mod_cast ht.1

lemma one_le_meanReturnTime (M : CMP A) (f : StationaryPolicy M) (i : ℕ) :
    1 ≤ meanReturnTime M f i := by
  unfold meanReturnTime
  calc (1 : ℝ≥0∞) = ∫⁻ _ω, 1 ∂(pathMeasure M f.toPolicy i) := by simp
    _ ≤ _ := lintegral_mono fun ω => by
        have := one_le_returnTime ω
        rw [← ENat.toENNReal_one]; exact ENat.toENNReal_le.2 this

lemma one_lt_K (M : CMP A) (K : ℝ)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K) : 1 < K := by
  have h := (one_le_meanReturnTime M (someStat M) 0).trans_lt (h57 (someStat M) 0)
  rw [← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).1 h

lemma discAtReturn_le (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (ω : ℕ → ℕ × A) :
    discAtReturn β ω ≤ ENNReal.ofReal β := by
  unfold discAtReturn
  split_ifs with h
  · exact zero_le
  · apply ENNReal.ofReal_le_ofReal
    have h1 := one_le_returnTime ω
    have hn : 1 ≤ (returnTime ω).toNat := by
      lift returnTime ω to ℕ using h with n
      simpa using h1
    calc β ^ (returnTime ω).toNat ≤ β ^ 1 := pow_le_pow_of_le_one hβ.1.le hβ.2.le hn
      _ = β := pow_one β

lemma expDiscAtReturn_le (M : CMP A) (f : StationaryPolicy M) (β : ℝ)
    (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ) :
    expDiscAtReturn M f β i ≤ ENNReal.ofReal β := by
  unfold expDiscAtReturn
  calc ∫⁻ ω, discAtReturn β ω ∂(pathMeasure M f.toPolicy i)
      ≤ ∫⁻ _ω, ENNReal.ofReal β ∂(pathMeasure M f.toPolicy i) :=
        lintegral_mono fun ω => discAtReturn_le β hβ ω
    _ = ENNReal.ofReal β := by simp

end Ross53Aux

namespace Ross53Aux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

omit [MetricSpace A] [BorelSpace A] in
/-- A function of the path depending only on the states up to time `t` is a measurable function
of the history `h_t`. -/
lemma hist_fun (a₀ : A) (t : ℕ) (G : (ℕ → ℕ × A) → ℝ≥0∞)
    (hG : ∀ ω ω' : ℕ → ℕ × A, (∀ s ≤ t, (ω s).1 = (ω' s).1) → G ω = G ω') :
    ∃ Φ : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞, Measurable Φ ∧
      ∀ ω, Φ (Preorder.frestrictLe t ω) = G ω := by
  let ext : (Finset.Iic t → ℕ) → (ℕ → ℕ × A) := fun x s =>
    (if hs : s ≤ t then x ⟨s, Finset.mem_Iic.2 hs⟩ else 0, a₀)
  let Ψ : (Finset.Iic t → ℕ) → ℝ≥0∞ := fun x => G (ext x)
  refine ⟨fun h => Ψ (fun s => (h s).1), ?_, ?_⟩
  · exact (measurable_of_countable Ψ).comp
      (measurable_pi_lambda _ fun s => measurable_fst.comp (measurable_pi_apply s))
  · intro ω
    apply hG
    intro s hs
    simp [ext, hs]

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma lt_returnTime_iff (t : ℕ) (ω : ℕ → ℕ × A) :
    (t : ℕ∞) < returnTime ω ↔ ∀ s, 1 ≤ s → s ≤ t → (ω s).1 ≠ 0 := by
  unfold returnTime
  constructor
  · intro h s hs1 hst h0
    have : sInf ((fun t : ℕ => (t : ℕ∞)) '' {t : ℕ | 1 ≤ t ∧ (ω t).1 = 0}) ≤ (s : ℕ∞) :=
      sInf_le ⟨s, ⟨hs1, h0⟩, rfl⟩
    have := h.trans_le this
    exact absurd (by exact_mod_cast this) (not_lt.2 hst)
  · intro h
    have : ((t + 1 : ℕ) : ℕ∞) ≤ sInf ((fun t : ℕ => (t : ℕ∞)) '' {t : ℕ | 1 ≤ t ∧ (ω t).1 = 0}) := by
      apply le_sInf
      rintro _ ⟨s, ⟨hs1, h0⟩, rfl⟩
      by_contra hc
      have hc' : (s : ℕ∞) < ((t + 1 : ℕ) : ℕ∞) := not_le.1 hc
      have : s ≤ t := by have := (Nat.cast_lt (α := ℕ∞)).1 hc'; omega
      exact h s hs1 this h0
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) this

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma returnTime_eq_iff (t : ℕ) (ω : ℕ → ℕ × A) :
    returnTime ω = (t : ℕ∞) ↔ 1 ≤ t ∧ (ω t).1 = 0 ∧ ∀ s, 1 ≤ s → s < t → (ω s).1 ≠ 0 := by
  constructor
  · intro h
    have hne : ((fun t : ℕ => (t : ℕ∞)) '' {t : ℕ | 1 ≤ t ∧ (ω t).1 = 0}).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      unfold returnTime at h
      rw [hc, sInf_empty] at h
      exact ENat.top_ne_natCast t h
    have hmem := csInf_mem hne
    unfold returnTime at h
    rw [h] at hmem
    obtain ⟨t', ⟨h1, h0⟩, he⟩ := hmem
    have : t' = t := (Nat.cast_inj (R := ℕ∞)).1 he
    subst this
    refine ⟨h1, h0, fun s hs1 hst h0' => ?_⟩
    have : sInf ((fun t : ℕ => (t : ℕ∞)) '' {t : ℕ | 1 ≤ t ∧ (ω t).1 = 0}) ≤ (s : ℕ∞) :=
      sInf_le ⟨s, ⟨hs1, h0'⟩, rfl⟩
    rw [h] at this
    exact absurd ((Nat.cast_le (α := ℕ∞)).1 this) (not_le.2 hst)
  · rintro ⟨h1, h0, hs⟩
    unfold returnTime
    refine le_antisymm (sInf_le (Set.mem_image_of_mem (fun t : ℕ => (t : ℕ∞))
      (show t ∈ {t : ℕ | 1 ≤ t ∧ (ω t).1 = 0} from ⟨h1, h0⟩))) ?_
    apply le_sInf
    rintro _ ⟨s, ⟨hs1, h0'⟩, rfl⟩
    by_contra hc
    exact hs s hs1 ((Nat.cast_lt (α := ℕ∞)).1 (not_le.1 hc)) h0'

/-- `1{τ > t}`. -/
noncomputable def Nw (t : ℕ) (ω : ℕ → ℕ × A) : ℝ≥0∞ := if (t : ℕ∞) < returnTime ω then 1 else 0

/-- `1{τ = t}`. -/
noncomputable def Ew (t : ℕ) (ω : ℕ → ℕ × A) : ℝ≥0∞ := if returnTime ω = (t : ℕ∞) then 1 else 0

omit [MetricSpace A] [BorelSpace A] in
lemma Nw_hist (a₀ : A) (t : ℕ) : ∃ Φ : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞, Measurable Φ ∧
    ∀ ω, Φ (Preorder.frestrictLe t ω) = Nw t ω := by
  apply hist_fun a₀ t
  intro ω ω' h
  unfold Nw
  have : (t : ℕ∞) < returnTime ω ↔ (t : ℕ∞) < returnTime ω' := by
    rw [lt_returnTime_iff, lt_returnTime_iff]
    exact forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun hst => by
      rw [h s hst]
  simp only [this]

omit [MetricSpace A] [BorelSpace A] in
lemma Ew_hist (a₀ : A) (t : ℕ) : ∃ Φ : (Π _ : Finset.Iic t, ℕ × A) → ℝ≥0∞, Measurable Φ ∧
    ∀ ω, Φ (Preorder.frestrictLe t ω) = Ew t ω := by
  apply hist_fun a₀ t
  intro ω ω' h
  unfold Ew
  have : returnTime ω = (t : ℕ∞) ↔ returnTime ω' = (t : ℕ∞) := by
    rw [returnTime_eq_iff, returnTime_eq_iff, h t le_rfl]
    exact and_congr_right fun _ => and_congr_right fun _ =>
      forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun hst => by
        rw [h s hst.le]
  simp only [this]

lemma Nw_zero (ω : ℕ → ℕ × A) : Nw 0 ω = 1 := by
  unfold Nw
  rw [if_pos]
  exact lt_of_lt_of_le (by norm_num) (one_le_returnTime ω)

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma Nw_split (t : ℕ) (ω : ℕ → ℕ × A) (W : ℕ → ℝ≥0∞) :
    Nw t ω * W (ω (t + 1)).1 ≤ Nw (t + 1) ω * W (ω (t + 1)).1 + Ew (t + 1) ω * W 0 := by
  unfold Nw Ew
  by_cases ht : (t : ℕ∞) < returnTime ω
  · rw [if_pos ht, one_mul]
    by_cases h0 : (ω (t + 1)).1 = 0
    · have : returnTime ω = ((t + 1 : ℕ) : ℕ∞) := by
        rw [returnTime_eq_iff]
        refine ⟨by omega, h0, fun s hs1 hst => (lt_returnTime_iff t ω).1 ht s hs1 (by omega)⟩
      rw [if_pos this, h0, one_mul]
      exact le_add_self
    · have : ((t + 1 : ℕ) : ℕ∞) < returnTime ω := by
        rw [lt_returnTime_iff]
        intro s hs1 hst
        rcases Nat.lt_or_ge s (t + 1) with h | h
        · exact (lt_returnTime_iff t ω).1 ht s hs1 (by omega)
        · have : s = t + 1 := by omega
          subst this; exact h0
      rw [if_pos this, one_mul]
      exact le_self_add
  · rw [if_neg ht, zero_mul]
    exact zero_le

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma sum_Nw_le (n : ℕ) (ω : ℕ → ℕ × A) :
    ∑ t ∈ Finset.range n, Nw t ω ≤ (returnTime ω : ℝ≥0∞) := by
  unfold Nw
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_one]
  rcases eq_or_ne (returnTime ω) ⊤ with h | h
  · rw [h]; simp
  · lift returnTime ω to ℕ using h with m hm
    have : (Finset.filter (fun t : ℕ => (t : ℕ∞) < (m : ℕ∞)) (Finset.range n)) ⊆ Finset.range m := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simpa using (by exact_mod_cast hx.2 : x < m)
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    simp only [ENat.toENNReal_coe]
    exact_mod_cast this

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma tsum_Ew_eq (β : ℝ) (ω : ℕ → ℕ × A) :
    ∑' t, Ew t ω * ENNReal.ofReal (β ^ t) = discAtReturn β ω := by
  unfold Ew discAtReturn
  rcases eq_or_ne (returnTime ω) ⊤ with h | h
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]
    lift returnTime ω to ℕ using h with m hm
    have : (fun t : ℕ => (if (m : ℕ∞) = (t : ℕ∞) then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (β ^ t))
        = fun t => if t = m then ENNReal.ofReal (β ^ m) else 0 := by
      funext t
      by_cases htm : t = m
      · subst htm; simp
      · rw [if_neg (fun h => htm (by exact_mod_cast h.symm)), if_neg htm, zero_mul]
    rw [this, tsum_ite_eq]
    simp

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma sum_Ew_succ_le (β : ℝ) (n : ℕ) (ω : ℕ → ℕ × A) :
    ∑ t ∈ Finset.range n, Ew (t + 1) ω * ENNReal.ofReal (β ^ (t + 1)) ≤ discAtReturn β ω := by
  rw [← tsum_Ew_eq]
  calc ∑ t ∈ Finset.range n, Ew (t + 1) ω * ENNReal.ofReal (β ^ (t + 1))
      ≤ ∑ t ∈ Finset.range (n + 1), Ew t ω * ENNReal.ofReal (β ^ t) := by
        rw [Finset.sum_range_succ']; exact le_self_add
    _ ≤ _ := ENNReal.sum_le_tsum _

omit [MetricSpace A] [MeasurableSpace A] [BorelSpace A] in
lemma tsum_Ew_mul_le (k : ℕ) (g : ℕ → (ℕ → ℕ × A) → ℝ≥0∞) (ω : ℕ → ℕ × A) :
    ∑' t, Ew t ω * ∑ s ∈ Finset.range k, g (t + s) ω ≤ ∑' s, g s ω := by
  unfold Ew
  rcases eq_or_ne (returnTime ω) ⊤ with h | h
  · simp [h]
  · lift returnTime ω to ℕ using h with m hm
    have : (fun t : ℕ => (if (m : ℕ∞) = (t : ℕ∞) then (1 : ℝ≥0∞) else 0) *
        ∑ s ∈ Finset.range k, g (t + s) ω)
        = fun t => if t = m then ∑ s ∈ Finset.range k, g (m + s) ω else 0 := by
      funext t
      by_cases htm : t = m
      · subst htm; simp
      · rw [if_neg (fun h => htm (by exact_mod_cast h.symm)), if_neg htm, zero_mul]
    have hi := Finset.sum_image (s := Finset.range k) (f := fun u => g u ω)
      (g := fun s => m + s) (fun x _ y _ h => by simpa using h)
    rw [this, tsum_ite_eq, ← hi]
    exact ENNReal.sum_le_tsum _

end Ross53Aux

namespace Ross53Aux

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

lemma measurable_Nw (a₀ : A) (t : ℕ) : Measurable (Nw (A := A) t) := by
  obtain ⟨Φ, hΦ, he⟩ := Nw_hist a₀ t
  have : Nw (A := A) t = fun ω => Φ (Preorder.frestrictLe t ω) := funext fun ω => (he ω).symm
  rw [this]; exact measurable_wt hΦ

lemma measurable_Ew (a₀ : A) (t : ℕ) : Measurable (Ew (A := A) t) := by
  obtain ⟨Φ, hΦ, he⟩ := Ew_hist a₀ t
  have : Ew (A := A) t = fun ω => Φ (Preorder.frestrictLe t ω) := funext fun ω => (he ω).symm
  rw [this]; exact measurable_wt hΦ

lemma measurable_returnTime (a₀ : A) : Measurable (returnTime (A := A)) := by
  have hfin : ∀ m : ℕ, MeasurableSet {ω : ℕ → ℕ × A | returnTime ω = (m : ℕ∞)} := by
    intro m
    have : {ω : ℕ → ℕ × A | returnTime ω = (m : ℕ∞)} = (Ew m) ⁻¹' {1} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, Ew]
      split_ifs with h <;> simp [h]
    rw [this]; exact measurable_Ew a₀ m (measurableSet_singleton 1)
  apply measurable_to_countable'
  intro x
  induction x using ENat.recTopCoe with
  | top =>
    have : returnTime (A := A) ⁻¹' {⊤} = (⋃ m : ℕ, {ω | returnTime ω = (m : ℕ∞)})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists]
      constructor
      · intro h m hm; rw [h] at hm; exact ENat.top_ne_natCast m hm
      · intro h
        by_contra hc
        lift returnTime ω to ℕ using hc with m hm
        exact h m rfl
    rw [this]; exact (MeasurableSet.iUnion hfin).compl
  | coe m => exact hfin m

lemma measurable_discAtReturn (a₀ : A) (β : ℝ) : Measurable (discAtReturn (A := A) β) := by
  have : discAtReturn (A := A) β = (fun r : ℕ∞ => if r = ⊤ then (0 : ℝ≥0∞)
      else ENNReal.ofReal (β ^ r.toNat)) ∘ returnTime := rfl
  rw [this]
  exact (measurable_of_countable _).comp (measurable_returnTime a₀)

/-- Jensen's inequality step: `β^K ≤ E[β^τ]` when `E[τ] < K`. -/
lemma jensen_real (M : CMP A) (f : StationaryPolicy M) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (K : ℝ) (hK : 0 < K) (i : ℕ) (hτ : meanReturnTime M f i < ENNReal.ofReal K) :
    ENNReal.ofReal (β ^ K) ≤ expDiscAtReturn M f β i := by
  set L := -Real.log β with hL
  have hL0 : 0 < L := by rw [hL]; exact neg_pos.2 (Real.log_neg hβ.1 hβ.2)
  have hbK : 0 < β ^ K := Real.rpow_pos_of_pos hβ.1 K
  have hpt : ∀ ω : ℕ → ℕ × A, ENNReal.ofReal (β ^ K * (1 + L * K)) ≤
      discAtReturn β ω + ENNReal.ofReal (β ^ K * L) * (returnTime ω : ℝ≥0∞) := by
    intro ω
    rcases eq_or_ne (returnTime ω) ⊤ with h | h
    · rw [h, ENat.toENNReal_top, ENNReal.mul_top (by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact mul_pos hbK hL0)]
      simp
    · have hd : discAtReturn β ω = ENNReal.ofReal (β ^ (returnTime ω).toNat) := by
        unfold discAtReturn; rw [if_neg h]
      rw [hd]
      lift returnTime ω to ℕ using h with m hm
      simp only [ENat.toNat_natCast, ENat.toENNReal_coe]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (mul_pos hbK hL0).le,
        ← ENNReal.ofReal_add (pow_nonneg hβ.1.le _)
          (mul_nonneg (mul_pos hbK hL0).le (Nat.cast_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      -- real inequality: β^K (1 + L K) ≤ β^m + β^K L m
      have e1 : β ^ m = Real.exp (-L * m) := by
        rw [hL, neg_neg, ← Real.rpow_natCast, Real.rpow_def_of_pos hβ.1]
      have e2 : β ^ K = Real.exp (-L * K) := by
        rw [hL, neg_neg, Real.rpow_def_of_pos hβ.1]
      have hexp : Real.exp (-L * m) = Real.exp (-L * K) * Real.exp (-L * (m - K)) := by
        rw [← Real.exp_add]; ring_nf
      have := Real.add_one_le_exp (-L * (m - K))
      rw [e1, e2, hexp]
      have hpos := Real.exp_pos (-L * K)
      nlinarith
  have hint : ENNReal.ofReal (β ^ K * (1 + L * K)) ≤
      expDiscAtReturn M f β i + ENNReal.ofReal (β ^ K * L) * meanReturnTime M f i := by
    unfold expDiscAtReturn meanReturnTime
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left (measurable_discAtReturn (f.1 0) β)]
    calc ENNReal.ofReal (β ^ K * (1 + L * K))
        = ∫⁻ _ω, ENNReal.ofReal (β ^ K * (1 + L * K)) ∂(pathMeasure M f.toPolicy i) := by simp
      _ ≤ _ := lintegral_mono hpt
  have h2 : ENNReal.ofReal (β ^ K * L) * meanReturnTime M f i ≤ ENNReal.ofReal (β ^ K * L * K) := by
    rw [ENNReal.ofReal_mul (mul_pos hbK hL0).le (q := K)]
    exact mul_le_mul_right hτ.le _
  have h3 : ENNReal.ofReal (β ^ K * (1 + L * K)) =
      ENNReal.ofReal (β ^ K) + ENNReal.ofReal (β ^ K * L * K) := by
    rw [← ENNReal.ofReal_add hbK.le (mul_pos (mul_pos hbK hL0) hK).le]; congr 1; ring
  rw [h3] at hint
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (hint.trans (add_le_add le_rfl h2))

lemma discValue_eq_Vstar (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) (j : ℕ) :
    discValue M β j = Vstar M β j := by
  obtain ⟨_, _, _, h⟩ := exists_opt M β hβ
  exact h j

/-- The stopped telescoping inequality behind (5.8). -/
lemma stopped_le (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) (f : StationaryPolicy M) (i : ℕ) (n : ℕ) :
    Vstar M β i ≤
      ∑ t ∈ Finset.range n, ∫⁻ ω, Nw t ω * cterm M β t ω ∂(pathMeasure M f.toPolicy i) +
      Vstar M β 0 * ∑ t ∈ Finset.range n,
        ∫⁻ ω, Ew (t + 1) ω * ENNReal.ofReal (β ^ (t + 1)) ∂(pathMeasure M f.toPolicy i) +
      ∫⁻ ω, Nw n ω * (ENNReal.ofReal (β ^ n) * Vstar M β (ω n).1) ∂(pathMeasure M f.toPolicy i) := by
  set W := Vstar M β
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, Nw_zero, one_mul,
      pow_zero, ENNReal.ofReal_one]
    rw [init_eq]
  | succ n ih =>
    refine ih.trans ?_
    obtain ⟨Φ, hΦ, hΦe⟩ := Nw_hist (f.1 0) n
    have hle : ∫⁻ ω, Nw n ω * (ENNReal.ofReal (β ^ n) * W (ω n).1) ∂(pathMeasure M f.toPolicy i) ≤
        ∫⁻ ω, Φ (Preorder.frestrictLe n ω) * (ENNReal.ofReal (β ^ n) * G M β W (ω n).1 (ω n).2)
          ∂(pathMeasure M f.toPolicy i) := by
      refine lintegral_mono_ae ?_
      filter_upwards [adm_ae M f.toPolicy i n] with ω hω
      rw [hΦe]
      gcongr
      calc W (ω n).1 = T M β W (ω n).1 := by rw [T_Vstar M β hβ]
        _ ≤ _ := T_le_G M β W _ _ hω
    rw [step_eq M f.toPolicy i β hβ n Φ hΦ W] at hle
    have hcomp : ∀ ω : ℕ → ℕ × A,
        Φ (Preorder.frestrictLe₂ (Nat.le_succ n) (Preorder.frestrictLe (n + 1) ω)) = Nw n ω := by
      intro ω
      rw [← Function.comp_apply (f := Preorder.frestrictLe₂ (Nat.le_succ n)),
        Preorder.frestrictLe₂_comp_frestrictLe, hΦe]
    simp_rw [hcomp, hΦe] at hle
    have hsplit : ∫⁻ ω, Nw n ω * (ENNReal.ofReal (β ^ (n + 1)) * W (ω (n + 1)).1)
          ∂(pathMeasure M f.toPolicy i) ≤
        ∫⁻ ω, Nw (n + 1) ω * (ENNReal.ofReal (β ^ (n + 1)) * W (ω (n + 1)).1)
          ∂(pathMeasure M f.toPolicy i) +
        W 0 * ∫⁻ ω, Ew (n + 1) ω * ENNReal.ofReal (β ^ (n + 1)) ∂(pathMeasure M f.toPolicy i) := by
      rw [← lintegral_const_mul _ ((measurable_Ew (f.1 0) (n + 1)).mul_const _),
        ← lintegral_add_right _ (((measurable_Ew (f.1 0) (n + 1)).mul_const _).const_mul _)]
      refine lintegral_mono fun ω => ?_
      have := Nw_split n ω W
      calc Nw n ω * (ENNReal.ofReal (β ^ (n + 1)) * W (ω (n + 1)).1)
          = ENNReal.ofReal (β ^ (n + 1)) * (Nw n ω * W (ω (n + 1)).1) := by ring
        _ ≤ ENNReal.ofReal (β ^ (n + 1)) * (Nw (n + 1) ω * W (ω (n + 1)).1 + Ew (n + 1) ω * W 0) := by
          gcongr
        _ = _ := by ring
    calc _ ≤ ∑ t ∈ Finset.range n, ∫⁻ ω, Nw t ω * cterm M β t ω ∂(pathMeasure M f.toPolicy i) +
          W 0 * ∑ t ∈ Finset.range n,
            ∫⁻ ω, Ew (t + 1) ω * ENNReal.ofReal (β ^ (t + 1)) ∂(pathMeasure M f.toPolicy i) +
          (∫⁻ ω, Nw n ω * cterm M β n ω ∂(pathMeasure M f.toPolicy i) +
          (∫⁻ ω, Nw (n + 1) ω * (ENNReal.ofReal (β ^ (n + 1)) * W (ω (n + 1)).1)
            ∂(pathMeasure M f.toPolicy i) +
          W 0 * ∫⁻ ω, Ew (n + 1) ω * ENNReal.ofReal (β ^ (n + 1)) ∂(pathMeasure M f.toPolicy i))) :=
          add_le_add le_rfl (hle.trans (add_le_add le_rfl hsplit))
      _ = _ := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
          ring

lemma eq58 (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : StationaryPolicy M) (i : ℕ) :
    discValue M β i ≤
      ENNReal.ofReal M₀ * meanReturnTime M f i + discValue M β 0 * expDiscAtReturn M f β i := by
  have hβ0 := hβ.1.le
  have hM := M0_nonneg M M₀ hc
  set P := pathMeasure M f.toPolicy i
  set C := ENNReal.ofReal (M₀ / (1 - β))
  have hW : ∀ j, Vstar M β j ≤ C := fun j => by
    rw [← discValue_eq_Vstar M β hβ0]; exact discValue_le M M₀ hc β hβ j
  rw [discValue_eq_Vstar M β hβ0, discValue_eq_Vstar M β hβ0]
  have key : ∀ n : ℕ, Vstar M β i ≤
      (ENNReal.ofReal M₀ * meanReturnTime M f i + Vstar M β 0 * expDiscAtReturn M f β i) +
        ENNReal.ofReal (β ^ n) * C := by
    intro n
    refine (stopped_le M β hβ0 f i n).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · -- the running cost before return
      rw [← lintegral_finset_sum (f := fun t ω => Nw t ω * cterm M β t ω) _
        (fun t _ => by exact (measurable_Nw (f.1 0) t).mul (measurable_cterm M β t))]
      unfold meanReturnTime
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_all_iff.2 (adm_ae M f.toPolicy i)] with ω hω
      calc ∑ t ∈ Finset.range n, Nw t ω * cterm M β t ω
          ≤ ∑ t ∈ Finset.range n, Nw t ω * ENNReal.ofReal M₀ := by
            refine Finset.sum_le_sum fun t _ => mul_le_mul_right ?_ _
            unfold cterm
            apply ENNReal.ofReal_le_ofReal
            have h1 := hc _ _ (hω t)
            have h0 := M.c_nonneg _ _ (hω t)
            have hp : β ^ t ≤ 1 := pow_le_one₀ hβ0 hβ.2.le
            nlinarith [pow_nonneg hβ0 t]
        _ = ENNReal.ofReal M₀ * ∑ t ∈ Finset.range n, Nw t ω := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => mul_comm _ _
        _ ≤ _ := mul_le_mul_right (sum_Nw_le n ω) _
    · refine mul_le_mul_right ?_ _
      rw [← lintegral_finset_sum (f := fun t ω => Ew (t + 1) ω * ENNReal.ofReal (β ^ (t + 1))) _
        (fun t _ => by exact (measurable_Ew (f.1 0) (t + 1)).mul_const _)]
      exact lintegral_mono fun ω => sum_Ew_succ_le β n ω
    · calc ∫⁻ ω, Nw n ω * (ENNReal.ofReal (β ^ n) * Vstar M β (ω n).1) ∂P
          ≤ ∫⁻ _ω, ENNReal.ofReal (β ^ n) * C ∂P := by
            refine lintegral_mono fun ω => ?_
            have : Nw n ω ≤ 1 := by unfold Nw; split_ifs <;> simp
            calc Nw n ω * (ENNReal.ofReal (β ^ n) * Vstar M β (ω n).1)
                ≤ 1 * (ENNReal.ofReal (β ^ n) * C) := by gcongr; exact hW _
              _ = _ := one_mul _
        _ = _ := by simp
  have hlim : Tendsto (fun n : ℕ => (ENNReal.ofReal M₀ * meanReturnTime M f i +
      Vstar M β 0 * expDiscAtReturn M f β i) + ENNReal.ofReal (β ^ n) * C) atTop
      (𝓝 ((ENNReal.ofReal M₀ * meanReturnTime M f i + Vstar M β 0 * expDiscAtReturn M f β i) +
        0)) := by
    refine tendsto_const_nhds.add ?_
    have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (β ^ n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ.2)
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr ENNReal.ofReal_ne_top)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim key

lemma jensen_first (M : CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : StationaryPolicy M)
    (hf : IsDiscOptimal M f β) (i : ℕ) :
    discValue M β 0 * expDiscAtReturn M f β i ≤ discValue M β i := by
  have hβ0 := hβ.1.le
  set P := pathMeasure M f.toPolicy i
  rw [← hf i, discValue_eq_Vstar M β hβ0, Vstar_apply, ENNReal.iSup_mul]
  refine iSup_le fun k => ?_
  have hmeasE : ∀ t, Measurable (fun ω => Ew t ω * ∑ s ∈ Finset.range k, cterm M β (t + s) ω) :=
    fun t => (measurable_Ew (f.1 0) t).mul
      (Finset.measurable_sum _ fun s _ => measurable_cterm M β (t + s))
  have h1 : ∑' t, ∫⁻ ω, Ew t ω * ∑ s ∈ Finset.range k, cterm M β (t + s) ω ∂P ≤
      discCost M f.toPolicy β i := by
    rw [← lintegral_tsum fun t => (hmeasE t).aemeasurable]
    exact lintegral_mono fun ω => tsum_Ew_mul_le k (cterm M β) ω
  refine le_trans ?_ h1
  have h2 : ∀ t, vi M β k 0 * ∫⁻ ω, Ew t ω * ENNReal.ofReal (β ^ t) ∂P ≤
      ∫⁻ ω, Ew t ω * ∑ s ∈ Finset.range k, cterm M β (t + s) ω ∂P := by
    intro t
    obtain ⟨Φ, hΦ, hΦe⟩ := Ew_hist (f.1 0) t
    have := vi_le M f.toPolicy i β hβ0 k t Φ hΦ
    simp_rw [hΦe] at this
    refine le_trans (le_of_eq ?_) this
    rw [← lintegral_const_mul _ ((measurable_Ew (f.1 0) t).mul_const _)]
    refine lintegral_congr fun ω => ?_
    unfold Ew
    split_ifs with h
    · have h0 := ((returnTime_eq_iff t ω).1 h).2.1
      rw [h0]; ring
    · simp
  calc vi M β k 0 * expDiscAtReturn M f β i
      = ∑' t, vi M β k 0 * ∫⁻ ω, Ew t ω * ENNReal.ofReal (β ^ t) ∂P := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          fun t => ((measurable_Ew (f.1 0) t).mul_const _).aemeasurable]
        unfold expDiscAtReturn
        simp_rw [tsum_Ew_eq]
        rfl
    _ ≤ _ := ENNReal.tsum_le_tsum h2

end Ross53Aux

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (f : StationaryPolicy M) (hf : IsDiscOptimal M f β)
    (i : ℕ) :
    discValue M β 0 * expDiscAtReturn M f β i ≤ discValue M β i ∧
      discValue M β 0 * ENNReal.ofReal (β ^ K) ≤ discValue M β 0 * expDiscAtReturn M f β i :=
  ⟨Ross53Aux.jensen_first M β hβ f hf i,
    mul_le_mul_right (Ross53Aux.jensen_real M f β hβ K hK i (h57 f i)) _⟩
