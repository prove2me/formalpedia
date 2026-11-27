-- Prove2me | solution 1 for AuctionDuration.ClearingError.Supplement.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:20.896804+00:00
-- url     : https://prove2.me/submissions/6854aa72-3188-40d7-aa56-c5898bd1de59

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_Canonical

open MeasureTheory Set
open scoped NNReal

open AuctionDuration
open AuctionDuration.ClearingError
open AuctionDuration.ClearingError.Supplement

/-- Lemma C.1, p.27. One constant for both laws, uniform in s,x and controls,
for EVERY positive real moment order, including noninteger orders below one. -/
theorem solution (G : Game) (hG : G.Standing) (hh : 0 < G.h) :
    ∀ ρ : ℝ, 0 < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ s : ℝ≥0, (s : ℝ) ≤ G.h → ∀ x : Fin 2 → ℕ,
        (∀ ω : Sample, (momentRange G s x ρ ω).Nonempty ∧
          BddAbove (momentRange G s x ρ ω)) ∧
        Integrable (supremumMoment G s x ρ) G.P ∧
        (∫ ω, supremumMoment G s x ρ ω ∂G.P) ≤
          C * (1 + (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ) ∧
        ∀ a b : Process, G.Admissible a → G.Admissible b →
          IsProbabilityMeasure (G.law a b) ∧
          Integrable (supremumMoment G s x ρ) (G.law a b) ∧
          (∫ ω, supremumMoment G s x ρ ω ∂(G.law a b)) ≤
            C * (1 + (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ) := by
              have ar1 : ∀ A B E1 D E2 E3 S : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ E1 → 0 ≤ D → 0 ≤ E2 → 0 ≤ E3 → 0 ≤ S →
                  A * S + B * E1 ≤ ((A + B * E1) + D * (A * E2 + B * E3) + 1) * (1 + S) := by
                intro A B E1 D E2 E3 S hA hB h1 hD h2 h3 hS
                have : ((A + B * E1) + D * (A * E2 + B * E3) + 1) * (1 + S) - (A * S + B * E1) =
                  A + B * E1 * S + (D * (A * E2 + B * E3) + 1) * (1 + S) := by ring
                have h : 0 ≤ A + B * E1 * S + (D * (A * E2 + B * E3) + 1) * (1 + S) := by positivity
                linarith
              have ar2 : ∀ A B E1 D E2 E3 S : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ E1 → 0 ≤ D → 0 ≤ E2 → 0 ≤ E3 → 0 ≤ S →
                  D * (A * S * E2 + B * E3) ≤ ((A + B * E1) + D * (A * E2 + B * E3) + 1) * (1 + S) := by
                intro A B E1 D E2 E3 S hA hB h1 hD h2 h3 hS
                have : ((A + B * E1) + D * (A * E2 + B * E3) + 1) * (1 + S) - D * (A * S * E2 + B * E3) =
                  (A + B * E1 + 1) * (1 + S) + D * A * E2 + D * B * E3 * S := by ring
                have h : 0 ≤ (A + B * E1 + 1) * (1 + S) + D * A * E2 + D * B * E3 * S := by positivity
                linarith
              have L1 : ∀ (q : CountPath) (T : ℝ), 0 ≤ T →
                  {t : ℝ | 0 < t ∧ t ≤ T ∧ ((q.val t : ℕ) : ℝ) - Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) t = 1}.Finite ∧
                  Set.ncard {t : ℝ | 0 < t ∧ t ≤ T ∧ ((q.val t : ℕ) : ℝ) - Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) t = 1} = q.val T := by
                have htend : ∀ (q : CountPath) (m : ℝ), 0 < m →
                    Filter.Tendsto (fun s : ℝ => ((q.val s : ℕ) : ℝ)) (nhdsWithin m (Iio m))
                      (nhds (Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) m)) := by
                  intro q m hm
                  have hmo : MonotoneOn (fun t => q.val t) (Ici 0) := (q.property 0 le_rfl).monotone ()
                  set q' : ℝ → ℝ := fun t => ((q.val (max t 0) : ℕ) : ℝ) with hq'
                  have hq'm : Monotone q' := by
                    intro u v huv
                    simp only [hq']
                    exact_mod_cast hmo (le_max_right u 0) (le_max_right v 0) (max_le_max huv le_rfl)
                  have ht : Filter.Tendsto (fun s : ℝ => ((q.val s : ℕ) : ℝ)) (nhdsWithin m (Iio m))
                      (nhds (Function.leftLim q' m)) := by
                    have := hq'm.tendsto_leftLim m
                    apply this.congr'
                    have : Ioo 0 m ∈ nhdsWithin m (Iio m) := Ioo_mem_nhdsLT hm
                    filter_upwards [this] with s hs
                    simp [hq', max_eq_left hs.1.le]
                  rw [leftLim_eq_of_tendsto ht]
                  exact ht
                have hleft : ∀ (q : CountPath) (y m : ℝ), 0 ≤ y → y < m →
                    ((q.val y : ℕ) : ℝ) ≤ Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) m := by
                  intro q y m hy hym
                  have hmo : MonotoneOn (fun t => q.val t) (Ici 0) := (q.property 0 le_rfl).monotone ()
                  refine ge_of_tendsto (htend q m (hy.trans_lt hym)) ?_
                  filter_upwards [Ioo_mem_nhdsLT hym] with s hs
                  exact_mod_cast hmo hy (hy.trans hs.1.le) hs.1.le
                have hleft2 : ∀ (q : CountPath) (m B : ℝ), 0 < m → (∀ y, 0 ≤ y → y < m → ((q.val y : ℕ) : ℝ) ≤ B) →
                    Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) m ≤ B := by
                  intro q m B hm hB
                  refine le_of_tendsto (htend q m hm) ?_
                  filter_upwards [Ioo_mem_nhdsLT hm] with s hs
                  exact hB s hs.1.le hs.2
                have hcount : ∀ (q : CountPath) (S : Finset ℝ),
                    (∀ t ∈ S, 0 < t ∧ ((q.val t : ℕ) : ℝ) - Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) t = 1) →
                    ∀ T : ℝ, (∀ t ∈ S, t ≤ T) → 0 ≤ T → (S.card : ℝ) ≤ q.val T := by
                  intro q S
                  induction S using Finset.induction_on_max with
                  | empty => intro _ T _ _; simp
                  | insert a s hlt ih =>
                    intro hS T hT hT0
                    have hmo : MonotoneOn (fun t => q.val t) (Ici 0) := (q.property 0 le_rfl).monotone ()
                    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
                    rw [Finset.card_insert_of_notMem has]
                    have ha := hS a (Finset.mem_insert_self a s)
                    have haT : a ≤ T := hT a (Finset.mem_insert_self a s)
                    have hqa : ((q.val a : ℕ) : ℝ) ≤ q.val T := by
                      exact_mod_cast hmo (show (0:ℝ) ≤ a from ha.1.le) hT0 haT
                    have hcs : (s.card : ℝ) ≤ Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) a := by
                      rcases s.eq_empty_or_nonempty with hs | hs
                      · subst hs
                        have := hleft q 0 a le_rfl ha.1
                        have h0 : q.val 0 = 0 := (q.property 0 le_rfl).zero ()
                        simpa [h0] using this
                      · set y := s.max' hs
                        have hy : y ∈ s := s.max'_mem hs
                        have hyS := hS y (Finset.mem_insert_of_mem hy)
                        have := ih (fun t ht => hS t (Finset.mem_insert_of_mem ht)) y
                          (fun t ht => s.le_max' t ht) hyS.1.le
                        exact this.trans (hleft q y a hyS.1.le (hlt y hy))
                    push_cast
                    linarith [ha.2]
                intro q T hT
                have hmo : MonotoneOn (fun t => q.val t) (Ici 0) := (q.property 0 le_rfl).monotone ()
                set J : Set ℝ := {t : ℝ | 0 < t ∧ t ≤ T ∧ ((q.val t : ℕ) : ℝ) - Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) t = 1} with hJ
                have hfin : J.Finite := by
                  by_contra hinf
                  obtain ⟨S, hS, hcardS⟩ := Set.Infinite.exists_subset_card_eq hinf (q.val T + 1)
                  have := hcount q S (fun t ht => ⟨(hS ht).1, (hS ht).2.2⟩) T (fun t ht => (hS ht).2.1) hT
                  rw [hcardS] at this
                  push_cast at this
                  linarith
                refine ⟨hfin, ?_⟩
                rw [Set.ncard_eq_toFinset_card _ hfin]
                apply le_antisymm
                · have := hcount q hfin.toFinset (fun t ht => by
                    rw [Set.Finite.mem_toFinset] at ht
                    exact ⟨ht.1, ht.2.2⟩) T (fun t ht => by
                    rw [Set.Finite.mem_toFinset] at ht
                    exact ht.2.1) hT
                  exact_mod_cast this
                · have key : ∀ k ∈ Finset.Icc 1 (q.val T), ∃ t ∈ J, q.val t = k := by
                    intro k hk
                    rw [Finset.mem_Icc] at hk
                    set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ k ≤ q.val t} with hA
                    have hTA : T ∈ A := ⟨hT, hk.2⟩
                    have hbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
                    set m := sInf A with hm
                    have hm0 : 0 ≤ m := le_csInf ⟨T, hTA⟩ (fun t ht => ht.1)
                    have hmT : m ≤ T := csInf_le hbdd hTA
                    have hbelow : ∀ y, 0 ≤ y → y < m → q.val y ≤ k - 1 := by
                      intro y hy hym
                      by_contra hcon
                      have : y ∈ A := ⟨hy, by omega⟩
                      exact absurd (csInf_le hbdd this) (not_le.2 hym)
                    have hkm : k ≤ q.val m := by
                      have hrc := (q.property 0 le_rfl).right_continuous () m hm0
                      have hrc' : Filter.Tendsto (fun s : ℝ => ((q.val s : ℕ) : ℝ)) (nhdsWithin m (Ioi m)) (nhds ((q.val m : ℕ) : ℝ)) :=
                        hrc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
                      have : (k : ℝ) ≤ q.val m := by
                        refine ge_of_tendsto hrc' ?_
                        filter_upwards [self_mem_nhdsWithin] with s hs
                        obtain ⟨t, htA, hts⟩ := exists_lt_of_csInf_lt ⟨T, hTA⟩ hs
                        have := hmo htA.1 (htA.1.trans hts.le) hts.le
                        exact_mod_cast htA.2.trans this
                      exact_mod_cast this
                    have hmpos : 0 < m := by
                      rcases hm0.eq_or_lt with h | h
                      · rw [← h] at hkm
                        have h0 : q.val 0 = 0 := (q.property 0 le_rfl).zero ()
                        omega
                      · exact h
                    have hl : Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) m ≤ (k:ℝ) - 1 := by
                      apply hleft2 q m _ hmpos
                      intro y hy hym
                      have := hbelow y hy hym
                      have : q.val y + 1 ≤ k := by omega
                      have : ((q.val y : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast this
                      linarith
                    have hu : ((q.val m : ℕ) : ℝ) - Function.leftLim (fun s : ℝ => ((q.val s : ℕ) : ℝ)) m ≤ 1 :=
                      (q.property T hT).unit_jumps () m hmpos hmT
                    have hkm' : (k : ℝ) ≤ q.val m := by exact_mod_cast hkm
                    refine ⟨m, ⟨hmpos, hmT, by linarith⟩, ?_⟩
                    have : ((q.val m : ℕ) : ℝ) = k := by linarith
                    exact_mod_cast this
                  choose! f hf1 hf2 using key
                  have := Finset.card_le_card_of_injOn (s := Finset.Icc 1 (q.val T)) (t := hfin.toFinset) f
                    (fun k hk => by simpa using hf1 k hk)
                    (fun k hk l hl hkl => by
                      have h1 := hf2 k hk
                      have h2 := hf2 l hl
                      rw [hkl] at h1
                      exact h1.symm.trans h2)
                  simpa using this
              have L6 : ∀ (G : Game) (_ : G.Standing)
                  (_ : Integrable (fun ω => Real.exp (1 * ((X (Real.toNNReal G.h) ω 0 : ℝ) + X (Real.toNNReal G.h) ω 1))) G.P)
                  (bound : Sample → ℝ) (_ : Integrable bound G.P)
                  (_ : ∀ a b : Process, (∀ t ω, G.lower ≤ a t ω ∧ a t ω ≤ G.upper) → (∀ t ω, G.lower ≤ b t ω ∧ b t ω ≤ G.upper) →
                    ∀ ω, Real.exp (G.logLikelihood a b ω) ≤ bound ω)
                  (a b : Process) (_ : G.Admissible a) (_ : G.Admissible b),
                  ∫⁻ ω, ENNReal.ofReal (Real.exp (G.logLikelihood a b ω)) ∂G.P = 1 := by
                have L2 : ∀ (r : ℝ) (_ : 0 < r) (P : Measure Sample) (_ : IsPoissonPair r P) (u v : ℝ≥0) (_ : u ≤ v)
                    (Z : Sample → ENNReal) (α β : Sample → ℝ) (_ : Measurable[naturalFiltration u] Z)
                    (_ : Measurable[naturalFiltration u] α) (_ : Measurable[naturalFiltration u] β)
                    (_ : ∀ ω, 0 < α ω) (_ : ∀ ω, 0 < β ω),
                    ∫⁻ ω, Z ω * ENNReal.ofReal (Real.exp (((X v ω 0 - X u ω 0 : ℕ) : ℝ) * Real.log (α ω / r) +
                      ((X v ω 1 - X u ω 1 : ℕ) : ℝ) * Real.log (β ω / r) -
                      ((α ω - r) + (β ω - r)) * ((v : ℝ) - u))) ∂P = ∫⁻ ω, Z ω ∂P := by
                  have hmeasX : ∀ t : ℝ≥0, Measurable (X t) := by
                    intro t
                    exact Measurable.of_comap_le (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) t)
                  have hmono : ∀ (ω : Sample) (i : Fin 2) (u v : ℝ≥0), u ≤ v → X u ω i ≤ X v ω i := by
                    intro ω i u v huv
                    exact ((ω i).property 0 le_rfl).monotone () u.2 v.2 huv
                  have hX0 : ∀ (ω : Sample) (i : Fin 2), X 0 ω i = 0 := by
                    intro ω i
                    exact ((ω i).property 0 le_rfl).zero ()
                  intro r hr P hP u v huv Z α β hZ hα hβ hα0 hβ0
                  have : IsProbabilityMeasure P := hP.1
                  set Δ : Sample → Fin 2 → ℕ := fun ω i => X v ω i - X u ω i with hΔ
                  have hΔm : Measurable Δ := by
                    rw [measurable_pi_iff]
                    intro j
                    exact ((measurable_pi_apply j).comp (hmeasX _)).sub ((measurable_pi_apply j).comp (hmeasX _))
                  -- law
                  have hlaw : Measure.map Δ P = Measure.pi (fun _ : Fin 2 => ProbabilityTheory.poissonMeasure
                      (Real.toNNReal (r * ((v : ℝ) - u)))) := by
                    let tt : Fin 2 → ℝ≥0 := ![u, v]
                    have htt : Monotone tt := by
                      intro i j hij
                      fin_cases i <;> fin_cases j <;> simp [tt] at hij ⊢
                      exact huv
                    have hmap := hP.2 1 tt htt
                    have hp := MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin 2 => ProbabilityTheory.poissonMeasure
                      (Real.toNNReal (r * ((v : ℝ) - u)))) (Equiv.uniqueProd (Fin 2) (Fin 1))
                    have hp2 := hp.map_eq
                    have e : (Measure.pi (fun _ : Fin 1 × Fin 2 => ProbabilityTheory.poissonMeasure
                      (Real.toNNReal (r * ((v : ℝ) - u))))) = (Measure.pi fun j : Fin 1 × Fin 2 => ProbabilityTheory.poissonMeasure
                      (Real.toNNReal (r * ((tt j.1.succ : ℝ) - (tt j.1.castSucc : ℝ))))) := by
                      congr 1; funext j; obtain ⟨j1, j2⟩ := j; fin_cases j1; simp [tt]
                    rw [e, ← hmap, Measure.map_map (MeasurableEquiv.measurable _)] at hp2
                    · rw [← hp2]
                      congr 1
                    · rw [measurable_pi_iff]
                      intro j
                      exact ((measurable_pi_apply j.2).comp (hmeasX _)).sub ((measurable_pi_apply j.2).comp (hmeasX _))
                  have hE : ∀ c d : ℝ, ∫⁻ δ, ENNReal.ofReal (Real.exp ((δ 0 : ℝ) * c + (δ 1 : ℝ) * d)) ∂(Measure.map Δ P)
                      = ENNReal.ofReal (Real.exp (r * ((v : ℝ) - u) * (Real.exp c - 1) + r * ((v : ℝ) - u) * (Real.exp d - 1))) := by
                    intro c d
                    rw [hlaw]
                    set ν := Real.toNNReal (r * ((v : ℝ) - u)) with hν
                    have hνr : (ν : ℝ) = r * ((v : ℝ) - u) := by
                      apply Real.coe_toNNReal
                      have : (u : ℝ) ≤ v := huv
                      exact mul_nonneg hr.le (by linarith)
                    have hint1 : ∀ c : ℝ, Integrable (fun n : ℕ => Real.exp ((n : ℝ) * c)) (ProbabilityTheory.poissonMeasure ν) := by
                      intro c
                      rw [ProbabilityTheory.integrable_poissonMeasure_iff]
                      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                      have := (Real.summable_pow_div_factorial ((ν : ℝ) * Real.exp c)).mul_left (Real.exp (-(ν : ℝ)))
                      refine this.congr (fun n => ?_)
                      rw [mul_pow, ← Real.exp_nat_mul]
                      ring
                    have hval : ∀ c : ℝ, ∫ n : ℕ, Real.exp ((n : ℝ) * c) ∂(ProbabilityTheory.poissonMeasure ν) = Real.exp (ν * (Real.exp c - 1)) := by
                      intro c
                      rw [ProbabilityTheory.integral_poissonMeasure]
                      have h1 : HasSum (fun n : ℕ => ((ν : ℝ) * Real.exp c) ^ n / (n.factorial : ℝ)) (Real.exp (ν * Real.exp c)) := by
                        rw [Real.exp_eq_exp_ℝ]
                        exact NormedSpace.expSeries_div_hasSum_exp _
                      have h2 := h1.mul_left (Real.exp (-(ν : ℝ)))
                      rw [← Real.exp_add] at h2
                      rw [show (ν : ℝ) * (Real.exp c - 1) = -ν + ν * Real.exp c by ring, ← h2.tsum_eq]
                      congr 1
                      funext n
                      rw [mul_pow, ← Real.exp_nat_mul, smul_eq_mul]
                      ring
                    let f : Fin 2 → ℕ → ℝ := fun i n => Real.exp ((n : ℝ) * (![c, d] i))
                    have hf : ∀ δ : Fin 2 → ℕ, Real.exp ((δ 0 : ℝ) * c + (δ 1 : ℝ) * d) = ∏ i, f i (δ i) := by
                      intro δ
                      simp [f, Fin.prod_univ_two, Real.exp_add]
                    simp only [hf]
                    have hfi : Integrable (fun δ : Fin 2 → ℕ => ∏ i, f i (δ i)) (Measure.pi (fun _ : Fin 2 => ProbabilityTheory.poissonMeasure ν)) :=
                      Integrable.fintype_prod (fun i => hint1 _)
                    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun δ => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le),
                      integral_fintype_prod_eq_prod]
                    simp [f, Fin.prod_univ_two, hval, Real.exp_add, hνr]
                  -- independence
                  have hind : ProbabilityTheory.Indep (naturalFiltration u : MeasurableSpace Sample) (MeasurableSpace.comap Δ inferInstance) P := by
                    have hF : (naturalFiltration u : MeasurableSpace Sample) ≤
                        ⨆ S : Finset (Iic u), ⨆ s ∈ S, MeasurableSpace.comap (X s.1) inferInstance := by
                      refine iSup_le fun s => iSup_le fun hs => ?_
                      refine le_trans ?_ (le_iSup _ ({⟨s, hs⟩} : Finset (Iic u)))
                      exact le_iSup_of_le ⟨s, hs⟩ (le_iSup_of_le (Finset.mem_singleton_self _) le_rfl)
                    refine ProbabilityTheory.indep_of_indep_of_le_left ?_ hF
                    refine ProbabilityTheory.indep_iSup_of_directed_le ?_ ?_ ?_ ?_
                    · intro S
                      set T : Finset ℝ≥0 := insert 0 (insert u (S.image Subtype.val)) with hT
                      have hTu : ∀ t ∈ T, t ≤ u := by
                        intro t ht
                        simp only [hT, Finset.mem_insert, Finset.mem_image] at ht
                        rcases ht with rfl | rfl | ⟨w, _, rfl⟩
                        · exact bot_le
                        · exact le_rfl
                        · exact w.2
                      obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := Nat.exists_eq_succ_of_ne_zero
                        (Finset.card_pos.2 ⟨0, Finset.mem_insert_self _ _⟩).ne'
                      set e := T.orderEmbOfFin hn with he
                      have hrange : ∀ t ∈ T, ∃ k, e k = t := by
                        intro t ht
                        have : t ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact ht
                        exact this
                      have heT : ∀ k, e k ≤ u := fun k => hTu _ (Finset.orderEmbOfFin_mem T hn k)
                      have he0 : e 0 = 0 := by
                        obtain ⟨k, hk⟩ := hrange 0 (Finset.mem_insert_self _ _)
                        have : e 0 ≤ e k := e.monotone (Fin.zero_le _)
                        rw [hk] at this
                        exact le_antisymm this bot_le
                      have helast : e (Fin.last n) = u := by
                        obtain ⟨k, hk⟩ := hrange u (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                        have : e k ≤ e (Fin.last n) := e.monotone (Fin.le_last _)
                        rw [hk] at this
                        exact le_antisymm (heT _) this
                      set tt : Fin (n + 2) → ℝ≥0 := Fin.snoc (α := fun _ => ℝ≥0) e v with htt
                      have htc : ∀ k : Fin (n+1), tt k.castSucc = e k := fun k => by simp [htt]
                      have htl : tt (Fin.last (n+1)) = v := by simp [htt]
                      have hmo : Monotone tt := by
                        rw [Fin.monotone_iff_le_succ]
                        intro i
                        rw [htc]
                        refine Fin.lastCases ?_ (fun j => ?_) i
                        · rw [Fin.succ_last, htl]; exact (heT _).trans huv
                        · rw [← Fin.castSucc_succ, htc]
                          exact e.monotone (Fin.castSucc_lt_succ).le
                      have hmap := hP.2 (n+1) tt hmo
                      set ξ : Fin (n+1) × Fin 2 → Sample → ℕ := fun j ω => X (tt j.1.succ) ω j.2 - X (tt j.1.castSucc) ω j.2 with hξ
                      have hξm : ∀ j, Measurable (ξ j) := fun j =>
                        ((measurable_pi_apply j.2).comp (hmeasX _)).sub ((measurable_pi_apply j.2).comp (hmeasX _))
                      have hii : ProbabilityTheory.iIndepFun ξ P := by
                        rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (fun j => (hξm j).aemeasurable)]
                        have hj : ∀ j, Measure.map (ξ j) P = ProbabilityTheory.poissonMeasure
                            (Real.toNNReal (r * ((tt j.1.succ : ℝ) - (tt j.1.castSucc : ℝ)))) := by
                          intro j
                          have h1 := (measurePreserving_eval (fun j : Fin (n+1) × Fin 2 => ProbabilityTheory.poissonMeasure
                            (Real.toNNReal (r * ((tt j.1.succ : ℝ) - (tt j.1.castSucc : ℝ))))) j).map_eq
                          rw [← hmap, Measure.map_map (measurable_pi_apply j) (measurable_pi_iff.2 hξm)] at h1
                          exact h1
                        simp only [hj]
                        exact hmap
                      have hdis := hii.indepFun_finset (Finset.univ.filter (fun j => j.1 ≠ Fin.last n))
                        (Finset.univ.filter (fun j => j.1 = Fin.last n)) (by
                          rw [Finset.disjoint_left]; intro j h1 h2
                          simp at h1 h2; exact h1 h2) hξm
                      refine ProbabilityTheory.indep_of_indep_of_le hdis ?_ ?_
                      · set m' := MeasurableSpace.comap (fun a (i : (Finset.univ.filter (fun j : Fin (n+1) × Fin 2 => j.1 ≠ Fin.last n))) => ξ i a) inferInstance with hm'
                        have hξm' : ∀ j : Fin (n+1) × Fin 2, j.1 ≠ Fin.last n → Measurable[m'] (ξ j) := by
                          intro j hj
                          have h1 : Measurable[m'] (fun a (i : (Finset.univ.filter (fun j : Fin (n+1) × Fin 2 => j.1 ≠ Fin.last n))) => ξ i a) :=
                            comap_measurable _
                          exact (measurable_pi_apply (⟨j, by simpa using hj⟩ : (Finset.univ.filter (fun j : Fin (n+1) × Fin 2 => j.1 ≠ Fin.last n)))).comp h1
                        have hstep : ∀ k : ℕ, ∀ hk : k < n + 1, ∀ i, Measurable[m'] (fun ω => X (e ⟨k, hk⟩) ω i) := by
                          intro k
                          induction k with
                          | zero =>
                            intro hk i
                            have : (fun ω => X (e ⟨0, hk⟩) ω i) = fun _ => 0 := by
                              funext ω
                              rw [show (⟨0, hk⟩ : Fin (n+1)) = 0 from rfl, he0, hX0]
                            rw [this]
                            exact measurable_const
                          | succ k ih =>
                            intro hk i
                            have hk' : k < n + 1 := by omega
                            have h1 := ih hk' i
                            have h2 := hξm' (⟨k, hk'⟩, i) (by
                              intro h
                              have := congrArg Fin.val h
                              simp at this; omega)
                            have e1 : tt (⟨k, hk'⟩ : Fin (n+1)).castSucc = e ⟨k, hk'⟩ := htc _
                            have e2 : tt (⟨k, hk'⟩ : Fin (n+1)).succ = e ⟨k+1, hk⟩ := by
                              rw [← htc]; rfl
                            have : (fun ω => X (e ⟨k+1, hk⟩) ω i) = fun ω => X (e ⟨k, hk'⟩) ω i + ξ (⟨k, hk'⟩, i) ω := by
                              funext ω
                              simp only [hξ, e1, e2]
                              have := hmono ω i (e ⟨k, hk'⟩) (e ⟨k+1, hk⟩) (e.monotone (by simp [Fin.le_def]))
                              omega
                            rw [this]
                            exact h1.add h2
                        refine iSup_le fun s => iSup_le fun hs => ?_
                        obtain ⟨k, hk⟩ := hrange s.1 (by
                          simp only [hT, Finset.mem_insert, Finset.mem_image]
                          exact Or.inr (Or.inr ⟨s, hs, rfl⟩))
                        rw [← hk]
                        refine Measurable.comap_le ?_
                        rw [@measurable_pi_iff]
                        intro i
                        exact hstep k.1 k.2 i
                      · refine Measurable.comap_le ?_
                        rw [@measurable_pi_iff]
                        intro i
                        have h1 : Measurable[MeasurableSpace.comap (fun a (i : (Finset.univ.filter (fun j : Fin (n+1) × Fin 2 => j.1 = Fin.last n))) => ξ i a) inferInstance]
                          (fun a (i : (Finset.univ.filter (fun j : Fin (n+1) × Fin 2 => j.1 = Fin.last n))) => ξ i a) :=
                            comap_measurable _
                        have h2 := (measurable_pi_apply (⟨(Fin.last n, i), by simp⟩ : (Finset.univ.filter (fun j : Fin (n+1) × Fin 2 => j.1 = Fin.last n)))).comp h1
                        have e3 : (fun ω => Δ ω i) = ξ (Fin.last n, i) := by
                          funext ω
                          simp only [hΔ, hξ, htc, helast, Fin.succ_last, htl]
                        rw [e3]
                        exact h2
                    · intro S
                      exact iSup_le fun s => iSup_le fun _ => (hmeasX s.1).comap_le
                    · exact hΔm.comap_le
                    · intro S T
                      refine ⟨S ∪ T, ?_, ?_⟩
                      · exact iSup_le fun s => iSup_le fun hs => le_iSup_of_le s (le_iSup_of_le (Finset.mem_union_left _ hs) le_rfl)
                      · exact iSup_le fun s => iSup_le fun hs => le_iSup_of_le s (le_iSup_of_le (Finset.mem_union_right _ hs) le_rfl)
                  set Y : Sample → ENNReal × ℝ × ℝ := fun ω => (Z ω, α ω, β ω) with hY
                  have hYm : Measurable[naturalFiltration u] Y := hZ.prodMk (hα.prodMk hβ)
                  have hYm' : Measurable Y := hYm.mono (naturalFiltration.le u) le_rfl
                  have hYΔ : ProbabilityTheory.IndepFun Y Δ P :=
                    ProbabilityTheory.indep_of_indep_of_le_left hind hYm.comap_le
                  have hprod := hYΔ.map_prod_eq_prod_map_map hYm'.aemeasurable hΔm.aemeasurable
                  set f : (ENNReal × ℝ × ℝ) × (Fin 2 → ℕ) → ENNReal := fun p =>
                    p.1.1 * ENNReal.ofReal (Real.exp ((p.2 0 : ℝ) * Real.log (p.1.2.1 / r) +
                      (p.2 1 : ℝ) * Real.log (p.1.2.2 / r) - ((p.1.2.1 - r) + (p.1.2.2 - r)) * ((v : ℝ) - u))) with hf
                  have hc0 : Measurable (fun p : (ENNReal × ℝ × ℝ) × (Fin 2 → ℕ) => ((p.2 0 : ℕ) : ℝ)) :=
                    (measurable_of_countable (fun δ : Fin 2 → ℕ => ((δ 0 : ℕ) : ℝ))).comp measurable_snd
                  have hc1 : Measurable (fun p : (ENNReal × ℝ × ℝ) × (Fin 2 → ℕ) => ((p.2 1 : ℕ) : ℝ)) :=
                    (measurable_of_countable (fun δ : Fin 2 → ℕ => ((δ 1 : ℕ) : ℝ))).comp measurable_snd
                  have hfm : Measurable f := by
                    have ha : Measurable (fun p : (ENNReal × ℝ × ℝ) × (Fin 2 → ℕ) => p.1.2.1) := by fun_prop
                    have hb : Measurable (fun p : (ENNReal × ℝ × ℝ) × (Fin 2 → ℕ) => p.1.2.2) := by fun_prop
                    have hz : Measurable (fun p : (ENNReal × ℝ × ℝ) × (Fin 2 → ℕ) => p.1.1) := by fun_prop
                    exact hz.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
                      (((hc0.mul (Real.measurable_log.comp (ha.div_const r))).add
                        (hc1.mul (Real.measurable_log.comp (hb.div_const r)))).sub
                        (((ha.sub_const r).add (hb.sub_const r)).mul_const _))))
                  have hLHS : ∫⁻ ω, f (Y ω, Δ ω) ∂P = ∫⁻ ω, Z ω ∂P := by
                    rw [← lintegral_map (f := f) (g := fun ω => (Y ω, Δ ω)) hfm (hYm'.prodMk hΔm), hprod,
                      lintegral_prod _ hfm.aemeasurable, lintegral_map (f := fun y => ∫⁻ δ, f (y, δ) ∂(Measure.map Δ P)) hfm.lintegral_prod_right' hYm']
                    apply lintegral_congr
                    intro ω
                    simp only [hf, hY]
                    rw [lintegral_const_mul _ (measurable_of_countable _)]
                    have hs : ∀ δ : Fin 2 → ℕ, ENNReal.ofReal (Real.exp ((δ 0 : ℝ) * Real.log (α ω / r) +
                        (δ 1 : ℝ) * Real.log (β ω / r) - ((α ω - r) + (β ω - r)) * ((v : ℝ) - u))) =
                        ENNReal.ofReal (Real.exp (- (((α ω - r) + (β ω - r)) * ((v : ℝ) - u)))) *
                        ENNReal.ofReal (Real.exp ((δ 0 : ℝ) * Real.log (α ω / r) + (δ 1 : ℝ) * Real.log (β ω / r))) := by
                      intro δ
                      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
                      congr 2
                      ring
                    simp only [hs]
                    rw [lintegral_const_mul _ (measurable_of_countable _), hE, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
                      Real.exp_log (div_pos (hα0 ω) hr), Real.exp_log (div_pos (hβ0 ω) hr)]
                    have : -((α ω - r + (β ω - r)) * ((v : ℝ) - u)) + (r * ((v : ℝ) - u) * (α ω / r - 1) + r * ((v : ℝ) - u) * (β ω / r - 1)) = 0 := by
                      field_simp
                      ring
                    rw [this]
                    simp
                  exact hLHS
                have L3 : ∀ (E : Type) (mE : MeasurableSpace E) (𝒜 : Set (Set E)) (_ : IsSetAlgebra 𝒜)
                    (_ : mE = MeasurableSpace.generateFrom 𝒜) (μ : Measure E) (_ : IsFiniteMeasure μ)
                    (Pr : (E → ℝ) → Prop) (lo up : ℝ)
                    (_ : ∀ c : ℝ, ∀ s ∈ 𝒜, Pr (s.indicator fun _ => c)) (_ : ∀ f g, Pr f → Pr g → Pr (f + g))
                    (_ : ∀ f, Pr f → Measurable f) (_ : ∀ f, Pr f → Pr (fun e => max lo (min up (f e))))
                    (a : E → ℝ) (_ : StronglyMeasurable a) (_ : ∀ e, lo ≤ a e ∧ a e ≤ up),
                    ∃ g : ℕ → E → ℝ, (∀ n, Pr (g n)) ∧ (∀ n e, lo ≤ g n e ∧ g n e ≤ up) ∧
                      ∀ᵐ e ∂μ, Filter.Tendsto (fun n => g n e) Filter.atTop (nhds (a e)) := by
                  intro E mE 𝒜 hA hgen μ hμ Pr lo up h1 h2 h3 h4 a ha hab
                  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ hA hgen
                  have haL : MemLp a 1 μ := by
                    refine MemLp.of_bound ha.aestronglyMeasurable (max |lo| |up|) (Filter.Eventually.of_forall fun e => ?_)
                    rw [Real.norm_eq_abs]
                    exact abs_le_max_abs_abs (hab e).1 (hab e).2
                  have hex : ∀ n : ℕ, ∃ g : E → ℝ, eLpNorm (a - g) 1 μ ≤ ((n : ENNReal) + 1)⁻¹ ∧ Pr g := by
                    intro n
                    refine haL.induction_dense ENNReal.one_ne_top Pr ?_ h2 (fun f hf => (h3 f hf).aestronglyMeasurable) (by simp)
                    intro c s hs hsμ ε hε
                    by_cases hc : c = 0
                    · refine ⟨_, ?_, h1 0 ∅ hA.empty_mem⟩
                      subst hc
                      simp
                    have hcpos : 0 < ‖c‖ₑ := by simpa using hc
                    obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ‖c‖ₑ * ENNReal.ofReal ε' ≤ ε := by
                      by_cases hεt : ε = ⊤
                      · exact ⟨1, one_pos, by simp [hεt]⟩
                      refine ⟨(ε / ‖c‖ₑ).toReal, ENNReal.toReal_pos ?_ ?_, ?_⟩
                      · exact (ENNReal.div_pos hε (by simp)).ne'
                      · exact ENNReal.div_ne_top hεt hcpos.ne'
                      · rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hεt hcpos.ne'), ENNReal.mul_div_cancel hcpos.ne' (by simp)]
                    obtain ⟨t, htA, ht⟩ := hd.approx s hs hsμ.ne ε' hε'0
                    refine ⟨_, ?_, h1 c t htA⟩
                    have htm := hd.measurable t htA
                    rw [eLpNorm_one_eq_lintegral_enorm]
                    calc ∫⁻ x, ‖(t.indicator (fun _ => c) - s.indicator fun _ => c) x‖ₑ ∂μ
                        ≤ ∫⁻ x, (symmDiff s t).indicator (fun _ => ‖c‖ₑ) x ∂μ := by
                          apply lintegral_mono
                          intro x
                          by_cases hx : x ∈ s <;> by_cases hx' : x ∈ t <;> simp [Set.indicator, hx, hx', Set.mem_symmDiff]
                      _ = ‖c‖ₑ * μ (symmDiff s t) := lintegral_indicator_const (hs.symmDiff htm) _
                      _ ≤ _ := (mul_le_mul_right ht.le _).trans hε'
                  choose g0 hg0 hg0P using hex
                  have ht0 : Filter.Tendsto (fun n => eLpNorm (g0 n - a) 1 μ) Filter.atTop (nhds 0) := by
                    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ENNReal) + 1)⁻¹) Filter.atTop (nhds 0) := by
                      have := (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => ((n : ENNReal))⁻¹) 1).2 ENNReal.tendsto_inv_nat_nhds_zero
                      simpa using this
                    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) (fun n => ?_)
                    simp only
                    rw [eLpNorm_sub_comm]
                    exact hg0 n
                  have htm := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
                    (fun n => (h3 _ (hg0P n)).aestronglyMeasurable) ha.aestronglyMeasurable ht0
                  obtain ⟨ns, _, hns⟩ := htm.exists_seq_tendsto_ae
                  refine ⟨fun n e => max lo (min up (g0 (ns n) e)), fun n => h4 _ (hg0P _), fun n e => ⟨le_max_left _ _, ?_⟩, ?_⟩
                  · exact max_le ((hab e).1.trans (hab e).2) (min_le_left _ _)
                  · filter_upwards [hns] with e he
                    have hc : Continuous fun y : ℝ => max lo (min up y) := by fun_prop
                    have := (hc.tendsto (a e)).comp he
                    have e1 : max lo (min up (a e)) = a e := by rw [min_eq_right (hab e).2, max_eq_right (hab e).1]
                    rw [e1] at this
                    exact this
                have L4a : ∀ (E : Type) (mE : MeasurableSpace E) (j : ℝ≥0 → Sample → E) (S : Set (Set E))
                    (_ : mE = MeasurableSpace.generateFrom S) (_ : IsPiSystem S) (_ : ∀ ω, Measurable fun t => j t ω)
                    (ν : Sample → Measure ℝ≥0) (_ : ∀ ω, IsFiniteMeasure (ν ω))
                    (_ : ∀ s ∈ S, Measurable fun ω => ν ω ((fun t => j t ω) ⁻¹' s)) (_ : Measurable fun ω => ν ω univ)
                    (P : Measure Sample) (_ : ∫⁻ ω, ν ω univ ∂P ≠ ⊤),
                    ∃ μ : Measure E, IsFiniteMeasure μ ∧ ∀ p : E → Prop, (∀ᵐ e ∂μ, p e) → ∀ᵐ ω ∂P, ∀ᵐ t ∂(ν ω), p (j t ω) := by
                  intro E mE j S hgen hpi hj ν hν h1 h2 P hP
                  have hgm : ∀ s ∈ S, MeasurableSet s := fun s hs => by
                    rw [hgen]; exact MeasurableSpace.measurableSet_generateFrom hs
                  set κ : Sample → Measure E := fun ω => (ν ω).map (fun t => j t ω) with hκ
                  have hκf : ∀ ω, IsFiniteMeasure (κ ω) := fun ω => by
                    simp only [hκ]; infer_instance
                  have hκm : Measurable κ := by
                    refine Measurable.measure_of_isPiSystem hgen hpi ?_ ?_
                    · intro s hs
                      have : (fun ω => κ ω s) = fun ω => ν ω ((fun t => j t ω) ⁻¹' s) := by
                        funext ω
                        simp only [hκ]
                        rw [Measure.map_apply (hj ω) (hgm s hs)]
                      rw [this]; exact h1 s hs
                    · have : (fun ω => κ ω univ) = fun ω => ν ω univ := by
                        funext ω
                        simp only [hκ]
                        rw [Measure.map_apply (hj ω) MeasurableSet.univ, preimage_univ]
                      rw [this]; exact h2
                  refine ⟨P.bind κ, ⟨?_⟩, ?_⟩
                  · rw [Measure.bind_apply MeasurableSet.univ hκm.aemeasurable]
                    have : (fun ω => κ ω univ) = fun ω => ν ω univ := by
                        funext ω
                        simp only [hκ]
                        rw [Measure.map_apply (hj ω) MeasurableSet.univ, preimage_univ]
                    rw [this]
                    exact lt_top_iff_ne_top.2 hP
                  · intro p hp
                    have := Measure.ae_ae_of_ae_bind hκm.aemeasurable hp
                    filter_upwards [this] with ω hω
                    exact ae_of_ae_map (hj ω).aemeasurable hω
                have L4 : ∀ (h : ℝ) (_ : 0 ≤ h) (P : Measure Sample) (_ : IsProbabilityMeasure P)
                    (_ : Integrable (fun ω => Real.exp (1 * ((X (Real.toNNReal h) ω 0 : ℝ) + X (Real.toNNReal h) ω 1))) P),
                    ∃ μ : @Measure (ℝ≥0 × Sample) naturalFiltration.predictable, IsFiniteMeasure μ ∧
                      ∀ p : ℝ≥0 × Sample → Prop, (∀ᵐ e ∂μ, p e) → ∀ᵐ ω ∂P,
                        (∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) h)), p (Real.toNNReal t, ω)) ∧
                        ∀ i, ∀ t ∈ jumps h ω i, p (Real.toNNReal t, ω) := by
                  intro h hh P hP hint
                  have hmeasX : ∀ t : ℝ≥0, Measurable (X t) := by
                    intro t
                    exact Measurable.of_comap_le (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) t)
                  have hJfin : ∀ T : ℝ, 0 ≤ T → ∀ ω i, (jumps T ω i).Finite := fun T hT ω i => (L1 (ω i) T hT).1
                  have hJcard : ∀ T : ℝ, 0 ≤ T → ∀ ω i, (jumps T ω i).ncard = (ω i).val T := fun T hT ω i => (L1 (ω i) T hT).2
                  set H : ℝ≥0 := Real.toNNReal h with hH
                  have hHh : (H : ℝ) = h := Real.coe_toNNReal h hh
                  set m0 : Measure ℝ≥0 := (volume.restrict (Icc (0:ℝ) h)).map Real.toNNReal with hm0
                  have hm0f : IsFiniteMeasure m0 := by rw [hm0]; infer_instance
                  set ν : Sample → Measure ℝ≥0 := fun ω => m0 + ∑ i : Fin 2, ∑ t ∈ (hJfin h hh ω i).toFinset, Measure.dirac (Real.toNNReal t) with hν
                  have hνf : ∀ ω, IsFiniteMeasure (ν ω) := fun ω => by simp only [hν]; infer_instance
                  have hνapp : ∀ ω (B : Set ℝ≥0), MeasurableSet B → ν ω B = m0 B + ∑ i : Fin 2, (({t ∈ jumps h ω i | Real.toNNReal t ∈ B}).ncard : ENNReal) := by
                    intro ω B hB
                    classical
                    simp only [hν, Measure.add_apply, Measure.finsetSum_apply]
                    congr 1
                    refine Finset.sum_congr rfl fun i _ => ?_
                    simp only [Measure.dirac_apply' _ hB, Set.indicator_apply, Pi.one_apply]
                    rw [Finset.sum_boole]
                    congr 1
                    rw [← Set.ncard_coe_finset]
                    congr 1
                    ext t
                    simp
                  have hcount : ∀ s : ℝ≥0, ∀ ω i, {t ∈ jumps h ω i | Real.toNNReal t ∈ Ioi s}.ncard = X H ω i - X (min s H) ω i := by
                    intro s ω i
                    have hsub : jumps (min s H : ℝ≥0) ω i ⊆ jumps h ω i := by
                      intro t ht
                      refine ⟨ht.1, ht.2.1.trans ?_, ht.2.2⟩
                      rw [← hHh]
                      exact_mod_cast min_le_right s H
                    have he : {t ∈ jumps h ω i | Real.toNNReal t ∈ Ioi s} = jumps h ω i \ jumps (min s H : ℝ≥0) ω i := by
                      ext t
                      constructor
                      · rintro ⟨ht, hts⟩
                        refine ⟨ht, fun hc => ?_⟩
                        have h1 : t ≤ s := hc.2.1.trans (by exact_mod_cast min_le_left s H)
                        have h2 : s < Real.toNNReal t := hts
                        rw [Real.lt_toNNReal_iff_coe_lt] at h2
                        linarith
                      · rintro ⟨ht, hts⟩
                        refine ⟨ht, ?_⟩
                        show s < Real.toNNReal t
                        rw [Real.lt_toNNReal_iff_coe_lt]
                        by_contra hc
                        apply hts
                        refine ⟨ht.1, ?_, ht.2.2⟩
                        have h3 : t ≤ h := ht.2.1
                        rw [← hHh] at h3
                        push_cast
                        exact le_min (not_lt.1 hc) h3
                    rw [he, Set.ncard_sdiff hsub (hJfin _ (NNReal.coe_nonneg _) ω i), hJcard h hh, hJcard _ (NNReal.coe_nonneg _)]
                    unfold X
                    rw [hHh]
                  have hall : ∀ ω i, {t ∈ jumps h ω i | Real.toNNReal t ∈ univ}.ncard = X H ω i := by
                    intro ω i
                    have : {t ∈ jumps h ω i | Real.toNNReal t ∈ univ} = jumps h ω i := by simp
                    rw [this, hJcard h hh]
                    unfold X
                    rw [hHh]
                  have hcm : ∀ u : ℝ≥0, ∀ i, Measurable fun ω => X u ω i := fun u i => (measurable_pi_apply i).comp (hmeasX u)
                  have hνu : (fun ω => ν ω univ) = fun ω => m0 univ + ∑ i : Fin 2, ((X H ω i : ℕ) : ENNReal) := by
                    funext ω
                    rw [hνapp ω univ MeasurableSet.univ]
                    simp only [hall]
                  obtain ⟨μ, hμ, hμp⟩ := L4a (ℝ≥0 × Sample) naturalFiltration.predictable (fun t ω => (t, ω))
                    _ rfl (by
                      rintro _ (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩) _ (⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩) hne
                      · left
                        exact ⟨A ∩ B, hA.inter hB, by rw [Set.prod_inter_prod, inter_self]⟩
                      · exfalso
                        obtain ⟨⟨t, ω⟩, h1, h2⟩ := hne
                        have h3 : t = ⊥ := h1.1
                        have h4 : j < t := h2.1
                        rw [h3] at h4
                        exact not_lt_bot h4
                      · exfalso
                        obtain ⟨⟨t, ω⟩, h1, h2⟩ := hne
                        have h3 : t = ⊥ := h2.1
                        have h4 : i < t := h1.1
                        rw [h3] at h4
                        exact not_lt_bot h4
                      · right
                        refine ⟨max i j, A ∩ B, ?_, by rw [Set.prod_inter_prod, Ioi_inter_Ioi]⟩
                        exact (naturalFiltration.mono (le_max_left i j) _ hA).inter (naturalFiltration.mono (le_max_right i j) _ hB))
                    (by
                      intro ω
                      refine measurable_generateFrom ?_
                      rintro _ (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
                      · by_cases hω : ω ∈ A
                        · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = {⊥} := by ext t; simp [hω]
                          rw [this]; exact measurableSet_singleton _
                        · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = ∅ := by ext t; simp [hω]
                          rw [this]; exact MeasurableSet.empty
                      · by_cases hω : ω ∈ A
                        · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A) = Ioi i := by ext t; simp [hω]
                          rw [this]; exact measurableSet_Ioi
                        · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A) = ∅ := by ext t; simp [hω]
                          rw [this]; exact MeasurableSet.empty)
                    ν hνf (by
                      rintro _ (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
                      · have hA' : MeasurableSet A := naturalFiltration.le _ _ hA
                        have : (fun ω => ν ω ((fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A))) = A.indicator (fun ω => m0 {⊥} + ∑ i : Fin 2, (({t ∈ jumps h ω i | Real.toNNReal t ∈ ({⊥} : Set ℝ≥0)}).ncard : ENNReal)) := by
                          funext ω
                          by_cases hω : ω ∈ A
                          · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = {⊥} := by ext t; simp [hω]
                            rw [this, hνapp ω _ (measurableSet_singleton _), Set.indicator_of_mem hω]
                          · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = ∅ := by ext t; simp [hω]
                            rw [this, measure_empty, Set.indicator_of_notMem hω]
                        rw [this]
                        refine Measurable.indicator ?_ hA'
                        have h0 : ∀ ω i, {t ∈ jumps h ω i | Real.toNNReal t ∈ ({⊥} : Set ℝ≥0)} = ∅ := by
                          intro ω i
                          ext t
                          simp only [mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
                          intro ht h0
                          have h1 : 0 < Real.toNNReal t := Real.toNNReal_pos.2 ht.1
                          exact h1.ne' h0
                        simp only [h0, ncard_empty]
                        exact measurable_const
                      · have hA' : MeasurableSet A := naturalFiltration.le _ _ hA
                        have : (fun ω => ν ω ((fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A))) = A.indicator (fun ω => m0 (Ioi i) + ∑ k : Fin 2, ((X H ω k - X (min i H) ω k : ℕ) : ENNReal)) := by
                          funext ω
                          by_cases hω : ω ∈ A
                          · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A) = Ioi i := by ext t; simp [hω]
                            rw [this, hνapp ω _ measurableSet_Ioi, Set.indicator_of_mem hω]
                            simp only [hcount]
                          · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A) = ∅ := by ext t; simp [hω]
                            rw [this, measure_empty, Set.indicator_of_notMem hω]
                        rw [this]
                        refine Measurable.indicator ?_ hA'
                        refine measurable_const.add (Finset.measurable_sum _ fun k _ => ?_)
                        exact (measurable_of_countable (fun n : ℕ => (n : ENNReal))).comp ((hcm H k).sub (hcm _ k)))
                    (by
                      rw [hνu]
                      refine measurable_const.add (Finset.measurable_sum _ fun k _ => ?_)
                      exact (measurable_of_countable (fun n : ℕ => (n : ENNReal))).comp (hcm H k))
                    P (by
                      rw [hνu]
                      have hb : ∫⁻ ω, (m0 univ + ∑ i : Fin 2, ((X H ω i : ℕ) : ENNReal)) ∂P ≤
                          ∫⁻ ω, (m0 univ + ENNReal.ofReal (Real.exp (1 * ((X H ω 0 : ℝ) + X H ω 1)))) ∂P := by
                        refine lintegral_mono fun ω => ?_
                        refine add_le_add le_rfl ?_
                        rw [Fin.sum_univ_two, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                        apply ENNReal.ofReal_le_ofReal
                        have := Real.add_one_le_exp (1 * ((X H ω 0 : ℝ) + X H ω 1))
                        linarith
                      refine ne_top_of_le_ne_top ?_ hb
                      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ (μ := P), mul_one]
                      refine ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ?_⟩
                      have := hint.lintegral_lt_top
                      exact this.ne)
                  refine ⟨μ, hμ, fun p hp => ?_⟩
                  filter_upwards [hμp p hp] with ω hω
                  simp only [hν] at hω
                  rw [ae_add_measure_iff] at hω
                  refine ⟨ae_of_ae_map measurable_real_toNNReal.aemeasurable hω.1, ?_⟩
                  intro i t ht
                  have h1 : ∀ B : Set ℝ≥0, (∑ i : Fin 2, ∑ t ∈ (hJfin h hh ω i).toFinset, Measure.dirac (Real.toNNReal t)) B = 0 → Real.toNNReal t ∉ B := by
                    intro B hB hmem
                    simp only [Measure.finsetSum_apply, Finset.sum_eq_zero_iff] at hB
                    have := hB i (Finset.mem_univ _) t ((hJfin h hh ω i).mem_toFinset.2 ht)
                    rw [Measure.dirac_apply_of_mem hmem] at this
                    exact one_ne_zero this
                  by_contra hc
                  exact h1 _ (ae_iff.1 hω.2) hc
                have L5 : ∀ (G : Game) (_ : G.Standing) (a b : Process)
                    (_ : ∀ t ω, G.lower ≤ a t ω ∧ a t ω ≤ G.upper) (_ : ∀ t ω, G.lower ≤ b t ω ∧ b t ω ≤ G.upper)
                    (_ : ∃ T : Finset ℝ≥0, ∀ u v : ℝ≥0, u < v → (∀ τ ∈ T, τ ≤ u ∨ v ≤ τ) →
                      (∀ t, u < t → t ≤ v → ∀ ω, a t ω = a v ω) ∧ Measurable[naturalFiltration u] (fun ω => a v ω))
                    (_ : ∃ T : Finset ℝ≥0, ∀ u v : ℝ≥0, u < v → (∀ τ ∈ T, τ ≤ u ∨ v ≤ τ) →
                      (∀ t, u < t → t ≤ v → ∀ ω, b t ω = b v ω) ∧ Measurable[naturalFiltration u] (fun ω => b v ω)),
                    Measurable (G.logLikelihood a b) ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp (G.logLikelihood a b ω)) ∂G.P = 1 := by
                  intro G hG a b hab hbb hTa hTb
                  obtain ⟨Ta, hTa⟩ := hTa
                  obtain ⟨Tb, hTb⟩ := hTb
                  obtain ⟨hh, hl, hlu, hr, hru, hP⟩ := hG
                  have hprob : IsProbabilityMeasure G.P := hP.1
                  have hJfin : ∀ T : ℝ, 0 ≤ T → ∀ ω i, (jumps T ω i).Finite := fun T hT ω i => (L1 (ω i) T hT).1
                  have hJcard : ∀ T : ℝ, 0 ≤ T → ∀ ω i, (jumps T ω i).ncard = (ω i).val T := fun T hT ω i => (L1 (ω i) T hT).2
                  set T : Finset ℝ≥0 := insert 0 (Ta ∪ Tb) with hT
                  set fI : Sample → ℝ → ℝ := fun ω t => (a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate) with hfI
                  set Lk : ℝ≥0 → Sample → ℝ := fun v ω => (∑ᶠ t ∈ jumps v ω 0, Real.log (a (Real.toNNReal t) ω / G.rate)) +
                    (∑ᶠ t ∈ jumps v ω 1, Real.log (b (Real.toNNReal t) ω / G.rate)) - ∫ t in Icc (0 : ℝ) v, fI ω t with hLk
                  -- sum step
                  have hsum : ∀ (c : Process) (u v : ℝ≥0), u < v → (∀ t, u < t → t ≤ v → ∀ ω, c t ω = c v ω) → ∀ ω i,
                      (∑ᶠ t ∈ jumps v ω i, Real.log (c (Real.toNNReal t) ω / G.rate)) =
                      (∑ᶠ t ∈ jumps u ω i, Real.log (c (Real.toNNReal t) ω / G.rate)) +
                        ((X v ω i - X u ω i : ℕ) : ℝ) * Real.log (c v ω / G.rate) := by
                    intro c u v huv hc ω i
                    have huv' : (u : ℝ) < v := by exact_mod_cast huv
                    have hsub : jumps u ω i ⊆ jumps v ω i := fun t ht => ⟨ht.1, ht.2.1.trans huv'.le, ht.2.2⟩
                    have hfu := hJfin u (NNReal.coe_nonneg _) ω i
                    have hfv := hJfin v (NNReal.coe_nonneg _) ω i
                    have hfd : (jumps v ω i \ jumps u ω i).Finite := hfv.sdiff
                    have e1 : jumps v ω i = jumps u ω i ∪ (jumps v ω i \ jumps u ω i) := (Set.union_diff_cancel hsub).symm
                    conv_lhs => rw [e1]
                    rw [finsum_mem_union disjoint_sdiff_right hfu hfd]
                    congr 1
                    have e2 : (∑ᶠ t ∈ jumps v ω i \ jumps u ω i, Real.log (c (Real.toNNReal t) ω / G.rate)) =
                        ∑ᶠ t ∈ jumps v ω i \ jumps u ω i, Real.log (c v ω / G.rate) := by
                      refine finsum_mem_congr rfl fun t ht => ?_
                      have h1 : t ≤ v := ht.1.2.1
                      have h2 : (u : ℝ) < t := by
                        by_contra hcon
                        exact ht.2 ⟨ht.1.1, not_lt.1 hcon, ht.1.2.2⟩
                      rw [hc (Real.toNNReal t) (by rw [Real.lt_toNNReal_iff_coe_lt]; exact h2) (by rw [Real.toNNReal_le_iff_le_coe]; exact h1) ω]
                    rw [e2, finsum_mem_eq_finite_toFinset_sum _ hfd, Finset.sum_const, nsmul_eq_mul]
                    congr 2
                    rw [← Set.ncard_eq_toFinset_card _ hfd, Set.ncard_sdiff hsub hfu, hJcard _ (NNReal.coe_nonneg _), hJcard _ (NNReal.coe_nonneg _)]
                    rfl
                  have hXm : ∀ (u v : ℝ≥0) (i : Fin 2), u ≤ v → Measurable[naturalFiltration v] (fun ω => X u ω i) := by
                    intro u v i huv
                    have : Measurable[naturalFiltration v] (X u) := by
                      refine Measurable.of_comap_le ?_
                      exact le_iSup_of_le u (le_iSup_of_le huv le_rfl)
                    exact (measurable_pi_apply i).comp this
                  have claim : ∀ n : ℕ, ∀ v : ℝ≥0, (T.filter (· < v)).card = n →
                      (∀ ω, IntegrableOn (fI ω) (Icc (0:ℝ) v)) ∧ Measurable[naturalFiltration v] (Lk v) ∧
                      ∫⁻ ω, ENNReal.ofReal (Real.exp (Lk v ω)) ∂G.P = 1 := by
                    intro n
                    induction n using Nat.strong_induction_on with
                    | _ n ih =>
                    intro v hv
                    rcases eq_or_ne v 0 with rfl | hv0
                    · have hL0 : Lk 0 = fun _ => 0 := by
                        funext ω
                        have hj0 : ∀ i, jumps ((0:ℝ≥0):ℝ) ω i = ∅ := by
                          intro i
                          ext t
                          simp only [jumps, NNReal.coe_zero, mem_setOf_eq, mem_empty_iff_false, iff_false]
                          rintro ⟨h1, h2, _⟩
                          linarith
                        simp only [hLk]
                        rw [hj0, hj0]
                        simp
                      refine ⟨fun ω => ?_, ?_, ?_⟩
                      · simp
                      · rw [hL0]; exact measurable_const
                      · rw [hL0]; simp
                    have hvpos : 0 < v := pos_iff_ne_zero.2 hv0
                    have hne : (T.filter (· < v)).Nonempty := ⟨0, by simp [hT, hvpos]⟩
                    set u := (T.filter (· < v)).max' hne with hu
                    have huT := (T.filter (· < v)).max'_mem hne
                    rw [← hu, Finset.mem_filter] at huT
                    have huv : u < v := huT.2
                    have huv' : (u : ℝ) < v := by exact_mod_cast huv
                    have hgap : ∀ τ ∈ T, τ ≤ u ∨ v ≤ τ := by
                      intro τ hτ
                      rcases lt_or_ge τ v with h | h
                      · left
                        exact Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hτ, h⟩)
                      · exact Or.inr h
                    obtain ⟨ha1, ha2⟩ := hTa u v huv (fun τ hτ => hgap τ (by simp [hT, hτ]))
                    obtain ⟨hb1, hb2⟩ := hTb u v huv (fun τ hτ => hgap τ (by simp [hT, hτ]))
                    have hlt : (T.filter (· < u)).card < n := by
                      rw [← hv]
                      apply Finset.card_lt_card
                      rw [Finset.ssubset_iff_of_subset (fun t ht => by
                        rw [Finset.mem_filter] at ht ⊢
                        exact ⟨ht.1, ht.2.trans huv⟩)]
                      exact ⟨u, Finset.mem_filter.2 huT, by simp⟩
                    obtain ⟨i1, i2, i3⟩ := ih _ hlt u rfl
                    have hEq : ∀ ω, EqOn (fI ω) (fun _ => (a v ω - G.rate) + (b v ω - G.rate)) (Ioc (u:ℝ) v) := by
                      intro ω t ht
                      simp only [hfI]
                      rw [ha1 (Real.toNNReal t) (by rw [Real.lt_toNNReal_iff_coe_lt]; exact ht.1) (by rw [Real.toNNReal_le_iff_le_coe]; exact ht.2) ω,
                        hb1 (Real.toNNReal t) (by rw [Real.lt_toNNReal_iff_coe_lt]; exact ht.1) (by rw [Real.toNNReal_le_iff_le_coe]; exact ht.2) ω]
                    have hIoc : ∀ ω, IntegrableOn (fI ω) (Ioc (u:ℝ) v) := by
                      intro ω
                      rw [integrableOn_congr_fun (hEq ω) measurableSet_Ioc]
                      exact integrableOn_const measure_Ioc_lt_top.ne enorm_ne_top
                    have hun : Icc (0:ℝ) v = Icc (0:ℝ) u ∪ Ioc (u:ℝ) v := (Icc_union_Ioc_eq_Icc (NNReal.coe_nonneg _) huv'.le).symm
                    have hstep : ∀ ω, Lk v ω = Lk u ω + (((X v ω 0 - X u ω 0 : ℕ) : ℝ) * Real.log (a v ω / G.rate) +
                        ((X v ω 1 - X u ω 1 : ℕ) : ℝ) * Real.log (b v ω / G.rate) -
                        ((a v ω - G.rate) + (b v ω - G.rate)) * ((v : ℝ) - u)) := by
                      intro ω
                      have hint : ∫ t in Icc (0:ℝ) v, fI ω t = (∫ t in Icc (0:ℝ) u, fI ω t) + ((a v ω - G.rate) + (b v ω - G.rate)) * ((v : ℝ) - u) := by
                        rw [hun, setIntegral_union (by
                          rw [Set.disjoint_left]; intro t h1 h2; exact absurd h1.2 (not_le.2 h2.1)) measurableSet_Ioc (i1 ω) (hIoc ω),
                          setIntegral_congr_fun measurableSet_Ioc (hEq ω), setIntegral_const]
                        simp [Real.volume_real_Ioc, huv'.le, mul_comm]
                      simp only [hLk]
                      rw [hsum a u v huv ha1 ω 0, hsum b u v huv hb1 ω 1, hint]
                      ring
                    have hFuv : (naturalFiltration u : MeasurableSpace Sample) ≤ naturalFiltration v := naturalFiltration.mono huv.le
                    refine ⟨fun ω => ?_, ?_, ?_⟩
                    · rw [hun]; exact (i1 ω).union (hIoc ω)
                    · rw [show Lk v = _ from funext hstep]
                      have ha3 : Measurable[naturalFiltration v] (fun ω => a v ω) := ha2.mono hFuv le_rfl
                      have hb3 : Measurable[naturalFiltration v] (fun ω => b v ω) := hb2.mono hFuv le_rfl
                      have hc : ∀ i, Measurable[naturalFiltration v] (fun ω => ((X v ω i - X u ω i : ℕ) : ℝ)) := fun i =>
                        (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp ((hXm v v i le_rfl).sub (hXm u v i huv.le))
                      refine (i2.mono hFuv le_rfl).add ?_
                      exact (((hc 0).mul (Real.measurable_log.comp (ha3.div_const _))).add
                        ((hc 1).mul (Real.measurable_log.comp (hb3.div_const _)))).sub
                        (((ha3.sub_const _).add (hb3.sub_const _)).mul_const _)
                    · rw [← i3]
                      have := L2 G.rate hr G.P hP u v huv.le (fun ω => ENNReal.ofReal (Real.exp (Lk u ω))) (fun ω => a v ω) (fun ω => b v ω)
                        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp i2)) ha2 hb2
                        (fun ω => hl.trans_le (hab v ω).1) (fun ω => hl.trans_le (hbb v ω).1)
                      rw [← this]
                      refine lintegral_congr fun ω => ?_
                      rw [hstep ω, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
                  obtain ⟨_, c2, c3⟩ := claim _ ⟨G.h, hh⟩ rfl
                  have hfin : G.logLikelihood a b = Lk ⟨G.h, hh⟩ := by
                    funext ω
                    rfl
                  rw [hfin]
                  exact ⟨c2.mono (naturalFiltration.le _) le_rfl, c3⟩
                have L7 : ∀ ω : Sample, @Measurable ℝ≥0 (ℝ≥0 × Sample) _ naturalFiltration.predictable (fun t => (t, ω)) := by
                  intro ω
                  refine measurable_generateFrom ?_
                  rintro _ (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
                  · by_cases hω : ω ∈ A
                    · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = {⊥} := by ext t; simp [hω]
                      rw [this]; exact measurableSet_singleton _
                    · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (({⊥} : Set ℝ≥0) ×ˢ A) = ∅ := by ext t; simp [hω]
                      rw [this]; exact MeasurableSet.empty
                  · by_cases hω : ω ∈ A
                    · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A) = Ioi i := by ext t; simp [hω]
                      rw [this]; exact measurableSet_Ioi
                    · have : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ((Ioi i : Set ℝ≥0) ×ˢ A) = ∅ := by ext t; simp [hω]
                      rw [this]; exact MeasurableSet.empty
                intro G hG hint bound hbound hLL a b ha hb
                obtain ⟨hh, hl, hlu, hr, hru, hP⟩ := id hG
                have hprob : IsProbabilityMeasure G.P := hP.1
                have hJfin : ∀ T : ℝ, 0 ≤ T → ∀ ω i, (jumps T ω i).Finite := fun T hT ω i => (L1 (ω i) T hT).1
                obtain ⟨μ, hμ, hμp⟩ := L4 G.h hh G.P hprob hint
                set El : (ℝ≥0 × Sample → ℝ) → Prop := fun f => ∃ T : Finset ℝ≥0, ∀ u v : ℝ≥0, u < v → (∀ τ ∈ T, τ ≤ u ∨ v ≤ τ) →
                    (∀ t, u < t → t ≤ v → ∀ ω, f (t, ω) = f (v, ω)) ∧ Measurable[naturalFiltration u] (fun ω => f (v, ω)) with hEl
                set 𝒜 : Set (Set (ℝ≥0 × Sample)) := {E | MeasurableSet[naturalFiltration.predictable] E ∧
                  ∃ T : Finset ℝ≥0, ∀ u v : ℝ≥0, u < v → (∀ τ ∈ T, τ ≤ u ∨ v ≤ τ) →
                    (∀ t, u < t → t ≤ v → ∀ ω, (t, ω) ∈ E ↔ (v, ω) ∈ E) ∧ MeasurableSet[naturalFiltration u] {ω | (v, ω) ∈ E}} with h𝒜
                have hA : IsSetAlgebra 𝒜 := by
                  refine ⟨⟨@MeasurableSet.empty _ naturalFiltration.predictable, ∅, ?_⟩, ?_, ?_⟩
                  · intro u v _ _
                    refine ⟨fun t _ _ ω => Iff.rfl, ?_⟩
                    simp
                  · rintro s ⟨hs, T, hT⟩
                    refine ⟨hs.compl, T, fun u v huv hτ => ?_⟩
                    obtain ⟨h1, h2⟩ := hT u v huv hτ
                    exact ⟨fun t ht ht' ω => not_congr (h1 t ht ht' ω), h2.compl⟩
                  · rintro s s' ⟨hs, T, hT⟩ ⟨hs', T', hT'⟩
                    refine ⟨hs.union hs', T ∪ T', fun u v huv hτ => ?_⟩
                    obtain ⟨h1, h2⟩ := hT u v huv (fun τ h => hτ τ (Finset.mem_union_left _ h))
                    obtain ⟨h1', h2'⟩ := hT' u v huv (fun τ h => hτ τ (Finset.mem_union_right _ h))
                    exact ⟨fun t ht ht' ω => or_congr (h1 t ht ht' ω) (h1' t ht ht' ω), h2.union h2'⟩
                have hgen : (naturalFiltration.predictable : MeasurableSpace (ℝ≥0 × Sample)) = MeasurableSpace.generateFrom 𝒜 := by
                  apply le_antisymm
                  · refine MeasurableSpace.generateFrom_mono ?_
                    rintro _ (⟨A, hA', rfl⟩ | ⟨i, A, hA', rfl⟩)
                    · refine ⟨measurableSet_predictable_singleton_bot_prod hA', ∅, fun u v huv _ => ?_⟩
                      have h0 : ∀ t, u < t → ∀ ω, (t, ω) ∉ (({⊥} : Set ℝ≥0) ×ˢ A) := by
                        intro t ht ω hmem
                        have h3 : t = ⊥ := hmem.1
                        rw [h3] at ht
                        exact not_lt_bot ht
                      refine ⟨fun t ht ht' ω => iff_of_false (h0 t ht ω) (h0 v huv ω), ?_⟩
                      have : {ω | (v, ω) ∈ (({⊥} : Set ℝ≥0) ×ˢ A)} = ∅ := by
                        ext ω
                        exact iff_of_false (h0 v huv ω) (fun h => h)
                      rw [this]
                      exact @MeasurableSet.empty _ (naturalFiltration u)
                    · refine ⟨measurableSet_predictable_Ioi_prod hA', {i}, fun u v huv hτ => ?_⟩
                      rcases hτ i (Finset.mem_singleton_self i) with h | h
                      · refine ⟨fun t ht ht' ω => ?_, ?_⟩
                        · exact and_congr_left fun _ => iff_of_true (h.trans_lt ht) (h.trans_lt huv)
                        · have : {ω | (v, ω) ∈ ((Ioi i : Set ℝ≥0) ×ˢ A)} = A := by
                            ext ω
                            exact ⟨fun hm => hm.2, fun hm => ⟨h.trans_lt huv, hm⟩⟩
                          rw [this]
                          exact naturalFiltration.mono h _ hA'
                      · have h0 : ∀ t, t ≤ v → ∀ ω, (t, ω) ∉ ((Ioi i : Set ℝ≥0) ×ˢ A) := by
                          intro t ht ω hmem
                          have h3 : i < t := hmem.1
                          exact absurd (ht.trans h) (not_le.2 h3)
                        refine ⟨fun t ht ht' ω => iff_of_false (h0 t ht' ω) (h0 v le_rfl ω), ?_⟩
                        have : {ω | (v, ω) ∈ ((Ioi i : Set ℝ≥0) ×ˢ A)} = ∅ := by
                          ext ω
                          exact iff_of_false (h0 v le_rfl ω) (fun h => h)
                        rw [this]
                        exact @MeasurableSet.empty _ (naturalFiltration u)
                  · refine MeasurableSpace.generateFrom_le ?_
                    rintro s ⟨hs, _⟩
                    exact hs
                have happ : ∀ c : Process, G.Admissible c → ∃ g : ℕ → ℝ≥0 × Sample → ℝ,
                    (∀ n, Measurable[naturalFiltration.predictable] (g n) ∧ El (g n)) ∧ (∀ n e, G.lower ≤ g n e ∧ g n e ≤ G.upper) ∧
                    ∀ᵐ e ∂μ, Filter.Tendsto (fun n => g n e) Filter.atTop (nhds (Function.uncurry c e)) := by
                  intro c hc
                  refine L3 (ℝ≥0 × Sample) naturalFiltration.predictable 𝒜 hA hgen μ hμ
                    (fun f => Measurable[naturalFiltration.predictable] f ∧ El f) G.lower G.upper ?_ ?_ ?_ ?_ (Function.uncurry c) hc.1
                    (fun e => hc.2 e.1 e.2)
                  · rintro k s ⟨hs, T, hT⟩
                    refine ⟨measurable_const.indicator hs, T, fun u v huv hτ => ?_⟩
                    obtain ⟨h1, h2⟩ := hT u v huv hτ
                    refine ⟨fun t ht ht' ω => ?_, ?_⟩
                    · by_cases hm : (v, ω) ∈ s
                      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((h1 t ht ht' ω).2 hm)]
                      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm ((h1 t ht ht' ω).1 h))]
                    · exact (measurable_const (a := k)).indicator h2
                  · rintro f g ⟨hf, T, hT⟩ ⟨hg, T', hT'⟩
                    refine ⟨hf.add hg, T ∪ T', fun u v huv hτ => ?_⟩
                    obtain ⟨h1, h2⟩ := hT u v huv (fun τ h => hτ τ (Finset.mem_union_left _ h))
                    obtain ⟨h1', h2'⟩ := hT' u v huv (fun τ h => hτ τ (Finset.mem_union_right _ h))
                    refine ⟨fun t ht ht' ω => ?_, h2.add h2'⟩
                    simp only [Pi.add_apply]
                    rw [h1 t ht ht' ω, h1' t ht ht' ω]
                  · exact fun f hf => hf.1
                  · rintro f ⟨hf, T, hT⟩
                    refine ⟨measurable_const.max (measurable_const.min hf), T, fun u v huv hτ => ?_⟩
                    obtain ⟨h1, h2⟩ := hT u v huv hτ
                    refine ⟨fun t ht ht' ω => ?_, measurable_const.max (measurable_const.min h2)⟩
                    simp only
                    rw [h1 t ht ht' ω]
                obtain ⟨ga, ga1, ga2, ga3⟩ := happ a ha
                obtain ⟨gb, gb1, gb2, gb3⟩ := happ b hb
                have hlik : ∀ n, Measurable (G.logLikelihood (fun t ω => ga n (t, ω)) (fun t ω => gb n (t, ω))) ∧
                    ∫⁻ ω, ENNReal.ofReal (Real.exp (G.logLikelihood (fun t ω => ga n (t, ω)) (fun t ω => gb n (t, ω)) ω)) ∂G.P = 1 := fun n =>
                  L5 G hG _ _ (fun t ω => ga2 n (t, ω)) (fun t ω => gb2 n (t, ω)) (ga1 n).2 (gb1 n).2
                have hconv : ∀ᵐ ω ∂G.P, Filter.Tendsto (fun n => G.logLikelihood (fun t ω => ga n (t, ω)) (fun t ω => gb n (t, ω)) ω)
                    Filter.atTop (nhds (G.logLikelihood a b ω)) := by
                  filter_upwards [hμp _ ga3, hμp _ gb3] with ω hωa hωb
                  have hsumc : ∀ (c : Process) (g : ℕ → ℝ≥0 × Sample → ℝ) (i : Fin 2), G.Admissible c →
                      (∀ t ∈ jumps G.h ω i, Filter.Tendsto (fun n => g n (Real.toNNReal t, ω)) Filter.atTop (nhds (c (Real.toNNReal t) ω))) →
                      Filter.Tendsto (fun n => ∑ᶠ t ∈ jumps G.h ω i, Real.log (g n (Real.toNNReal t, ω) / G.rate)) Filter.atTop
                        (nhds (∑ᶠ t ∈ jumps G.h ω i, Real.log (c (Real.toNNReal t) ω / G.rate))) := by
                    intro c g i hc hg
                    simp only [finsum_mem_eq_finite_toFinset_sum _ (hJfin G.h hh ω i)]
                    refine tendsto_finsetSum _ fun t ht => ?_
                    have ht' := (hJfin G.h hh ω i).mem_toFinset.1 ht
                    refine ((hg t ht').div_const _).log ?_
                    exact (div_pos (hl.trans_le (hc.2 _ _).1) hr).ne'
                  have hsec : ∀ g : ℝ≥0 × Sample → ℝ, Measurable[naturalFiltration.predictable] g →
                      Measurable (fun t : ℝ => g (Real.toNNReal t, ω)) := fun g hg =>
                    (hg.comp (L7 ω)).comp measurable_real_toNNReal
                  have hintc : Filter.Tendsto (fun n => ∫ t in Icc (0:ℝ) G.h, ((ga n (Real.toNNReal t, ω) - G.rate) + (gb n (Real.toNNReal t, ω) - G.rate)))
                      Filter.atTop (nhds (∫ t in Icc (0:ℝ) G.h, ((a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate)))) := by
                    refine tendsto_integral_of_dominated_convergence (fun _ => 2 * G.upper) ?_ ?_ ?_ ?_
                    · intro n
                      exact (((hsec _ (ga1 n).1).sub_const _).add ((hsec _ (gb1 n).1).sub_const _)).aestronglyMeasurable
                    · exact integrable_const _
                    · intro n
                      refine Filter.Eventually.of_forall fun t => ?_
                      have h1 := ga2 n (Real.toNNReal t, ω)
                      have h2 := gb2 n (Real.toNNReal t, ω)
                      rw [Real.norm_eq_abs, abs_le]
                      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
                    · filter_upwards [hωa.1, hωb.1] with t h1 h2
                      exact (h1.sub_const _).add (h2.sub_const _)
                  unfold Game.logLikelihood
                  exact ((hsumc a ga 0 ha (fun t ht => hωa.2 0 t ht)).add (hsumc b gb 1 hb (fun t ht => hωb.2 1 t ht))).sub hintc
                have hlim := tendsto_lintegral_of_dominated_convergence (μ := G.P)
                  (F := fun n ω => ENNReal.ofReal (Real.exp (G.logLikelihood (fun t ω => ga n (t, ω)) (fun t ω => gb n (t, ω)) ω)))
                  (f := fun ω => ENNReal.ofReal (Real.exp (G.logLikelihood a b ω)))
                  (fun ω => ENNReal.ofReal (bound ω))
                  (fun n => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hlik n).1))
                  (fun n => Filter.Eventually.of_forall fun ω => ENNReal.ofReal_le_ofReal
                    (hLL _ _ (fun t ω => ga2 n (t, ω)) (fun t ω => gb2 n (t, ω)) ω))
                  hbound.lintegral_lt_top.ne
                  (by
                    filter_upwards [hconv] with ω hω
                    exact (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp hω))
                simp only [(hlik _).2] at hlim
                exact tendsto_nhds_unique hlim tendsto_const_nhds
              have hmono : ∀ (ω : Sample) (i : Fin 2) (u v : ℝ≥0), u ≤ v → X u ω i ≤ X v ω i := by
                intro ω i u v huv
                exact ((ω i).property 0 le_rfl).monotone () u.2 v.2 huv
              have hX0 : ∀ (ω : Sample) (i : Fin 2), X 0 ω i = 0 := by
                intro ω i
                exact ((ω i).property 0 le_rfl).zero ()
              have hmeasX : ∀ t : ℝ≥0, Measurable (X t) := by
                intro t
                exact Measurable.of_comap_le (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) t)
              have hcn_mono : ∀ y z : Fin 2 → ℕ, (∀ i, y i ≤ z i) → countNorm y ≤ countNorm z := by
                intro y z hyz
                unfold countNorm
                apply Real.sqrt_le_sqrt
                have h0 : (y 0 : ℝ) ≤ z 0 := by exact_mod_cast hyz 0
                have h1 : (y 1 : ℝ) ≤ z 1 := by exact_mod_cast hyz 1
                have := Nat.cast_nonneg (α := ℝ) (y 0)
                have := Nat.cast_nonneg (α := ℝ) (y 1)
                nlinarith
              have hcn_le : ∀ y : Fin 2 → ℕ, countNorm y ≤ (y 0 : ℝ) + y 1 := by
                intro y
                unfold countNorm
                rw [Real.sqrt_le_left]
                · have := Nat.cast_nonneg (α := ℝ) (y 0)
                  have := Nat.cast_nonneg (α := ℝ) (y 1)
                  nlinarith
                · positivity
              have hcn_nn : ∀ y, 0 ≤ countNorm y := fun y => Real.sqrt_nonneg _
              have hP := hG.2.2.2.2.2
              have : IsProbabilityMeasure G.P := hP.1
              set H : ℝ≥0 := ⟨G.h, hG.1⟩ with hH
              have hpois : ∀ c : ℝ, Integrable (fun ω => Real.exp (c * ((X H ω 0 : ℝ) + X H ω 1))) G.P := by
                intro c
                let tt : Fin 2 → ℝ≥0 := ![0, H]
                have htt : Monotone tt := by
                  intro i j hij
                  fin_cases i <;> fin_cases j <;> simp [tt] at hij ⊢ <;> exact zero_le _
                have hmap := hP.2 1 tt htt
                set Φ : Sample → (Fin 1 × Fin 2 → ℕ) := fun ω j =>
                  X (tt j.1.succ) ω j.2 - X (tt j.1.castSucc) ω j.2 with hΦ
                have hΦm : Measurable Φ := by
                  rw [measurable_pi_iff]
                  intro j
                  exact ((measurable_pi_apply j.2).comp (hmeasX _)).sub ((measurable_pi_apply j.2).comp (hmeasX _))
                let g : (Fin 1 × Fin 2 → ℕ) → ℝ := fun v => ∏ j, Real.exp (c * (v j : ℝ))
                have hg : Integrable g (Measure.map Φ G.P) := by
                  rw [hmap]
                  refine Integrable.fintype_prod (f := fun (_ : Fin 1 × Fin 2) (n : ℕ) => Real.exp (c * (n:ℝ))) (fun j => ?_)
                  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
                  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
                  have := (Real.summable_pow_div_factorial
                    ((Real.toNNReal (G.rate * ((tt j.1.succ : ℝ) - (tt j.1.castSucc : ℝ))) : ℝ) * Real.exp c)).mul_left
                    (Real.exp (-(Real.toNNReal (G.rate * ((tt j.1.succ : ℝ) - (tt j.1.castSucc : ℝ))) : ℝ)))
                  refine this.congr (fun n => ?_)
                  rw [mul_pow, ← Real.exp_nat_mul, mul_comm (n:ℝ) c]
                  ring
                have := hg.comp_measurable hΦm
                convert this using 1
                funext ω
                simp only [g, Function.comp, hΦ, tt]
                rw [Fintype.prod_prod_type]
                simp [Fin.prod_univ_two, hX0, ← Real.exp_add, mul_add]
              have hG' := hG
              obtain ⟨_, hL, hLU, hr, hrU, _⟩ := hG
              intro ρ hρ
              have hthree : ∀ p q r' : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r' →
                  (p + q + r') ^ ρ ≤ (3:ℝ) ^ ρ * (p ^ ρ + q ^ ρ + r' ^ ρ) := by
                intro p q r' hp hq hr'
                set M := max p (max q r') with hM
                have hM0 : 0 ≤ M := le_trans hp (le_max_left _ _)
                have h1 : p + q + r' ≤ 3 * M := by
                  have := le_max_left p (max q r')
                  have := le_max_left q r'
                  have := le_max_right q r'
                  have := le_max_right p (max q r')
                  linarith
                have h2 : (p + q + r') ^ ρ ≤ (3 * M) ^ ρ :=
                  Real.rpow_le_rpow (by positivity) h1 hρ.le
                rw [Real.mul_rpow (by norm_num) hM0] at h2
                have h3 : M ^ ρ ≤ p ^ ρ + q ^ ρ + r' ^ ρ := by
                  have := Real.rpow_nonneg hp ρ
                  have := Real.rpow_nonneg hq ρ
                  have := Real.rpow_nonneg hr' ρ
                  rcases max_choice p (max q r') with h | h <;> rw [hM, h]
                  · linarith
                  · rcases max_choice q r' with h' | h' <;> rw [h'] <;> linarith
                exact h2.trans (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (show (0:ℝ) ≤ 3 by norm_num) ρ))
              have hexpb : ∀ t : ℝ, 0 ≤ t → t ^ ρ ≤ ρ ^ ρ * Real.exp t := by
                intro t ht
                have e1 : t = ρ * (t / ρ) := by field_simp
                have e2 : t ^ ρ = ρ ^ ρ * (t / ρ) ^ ρ := by
                  conv_lhs => rw [e1]
                  exact Real.mul_rpow hρ.le (div_nonneg ht hρ.le)
                rw [e2]
                have e3 : (t / ρ) ^ ρ ≤ (Real.exp (t / ρ)) ^ ρ :=
                  Real.rpow_le_rpow (div_nonneg ht hρ.le) (by linarith [Real.add_one_le_exp (t / ρ)]) hρ.le
                rw [← Real.exp_mul, div_mul_cancel₀ t hρ.ne'] at e3
                exact mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg hρ.le _)
              set Nf : Sample → ℝ := fun ω => (X H ω 0 : ℝ) + X H ω 1 with hNf
              have hNf0 : ∀ ω, 0 ≤ Nf ω := fun ω => by simp only [hNf]; positivity
              set K : ℝ := G.upper / G.rate with hK
              set lK : ℝ := Real.log K with hlK
              have hK1 : 1 ≤ K := by rw [hK, le_div_iff₀ hr]; linarith
              have hlK0 : 0 ≤ lK := Real.log_nonneg hK1
              set E1 : ℝ := ∫ ω, Real.exp (1 * Nf ω) ∂G.P with hE1
              set E2 : ℝ := ∫ ω, Real.exp (lK * Nf ω) ∂G.P with hE2
              set E3 : ℝ := ∫ ω, Real.exp ((lK + 1) * Nf ω) ∂G.P with hE3
              have hE1n : 0 ≤ E1 := integral_nonneg (fun _ => (Real.exp_pos _).le)
              have hE2n : 0 ≤ E2 := integral_nonneg (fun _ => (Real.exp_pos _).le)
              have hE3n : 0 ≤ E3 := integral_nonneg (fun _ => (Real.exp_pos _).le)
              set A : ℝ := (3:ℝ) ^ ρ with hA
              set B : ℝ := (3:ℝ) ^ ρ * ρ ^ ρ with hB
              have hA0 : 0 ≤ A := Real.rpow_nonneg (by norm_num) _
              have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hρ.le _)
              set D : ℝ := Real.exp (2 * G.rate * G.h) with hD
              have hD0 : 0 < D := Real.exp_pos _
              refine ⟨(A + B * E1) + D * (A * E2 + B * E3) + 1, by positivity, ?_⟩
              intro s hs x
              set Sx : ℝ := (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ with hSx
              have hSx0 : 0 ≤ Sx := by positivity
              set F : Sample → ℝ := fun ω => countNorm (shifted s H x ω) ^ ρ with hF
              have hsH : s ≤ H := by
                show (s : ℝ) ≤ (H : ℝ)
                exact hs
              have hgreat : ∀ ω, IsGreatest (momentRange G s x ρ ω) (F ω) := by
                intro ω
                refine ⟨⟨H, hsH, le_rfl, rfl⟩, ?_⟩
                rintro r ⟨u, hsu, huh, rfl⟩
                have huH : u ≤ H := by
                  show (u : ℝ) ≤ (H : ℝ)
                  exact huh
                apply Real.rpow_le_rpow (hcn_nn _) (hcn_mono _ _ (fun i => ?_)) hρ.le
                unfold shifted
                exact Nat.add_le_add_left (Nat.sub_le_sub_right (hmono ω i u H huH) _) _
              have hsupF : ∀ ω, supremumMoment G s x ρ ω = F ω := fun ω => (hgreat ω).csSup_eq
              have hsupF' : supremumMoment G s x ρ = F := funext hsupF
              have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Real.rpow_nonneg (hcn_nn _) _
              have hFb : ∀ ω, F ω ≤ A * Sx + B * Real.exp (Nf ω) := by
                intro ω
                have hy : ∀ i, (shifted s H x ω i : ℝ) ≤ (x i : ℝ) + X H ω i := by
                  intro i
                  unfold shifted
                  push_cast
                  exact_mod_cast Nat.add_le_add_left (Nat.sub_le _ _) _
                have h1 : countNorm (shifted s H x ω) ≤ (x 0 : ℝ) + x 1 + Nf ω := by
                  have := hcn_le (shifted s H x ω)
                  have := hy 0
                  have := hy 1
                  simp only [hNf]
                  linarith
                have h2 : F ω ≤ ((x 0 : ℝ) + x 1 + Nf ω) ^ ρ :=
                  Real.rpow_le_rpow (hcn_nn _) h1 hρ.le
                have h3 := hthree (x 0 : ℝ) (x 1) (Nf ω) (by positivity) (by positivity) (hNf0 ω)
                have h4 := hexpb (Nf ω) (hNf0 ω)
                have : A * ((x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ + Nf ω ^ ρ) ≤ A * Sx + B * Real.exp (Nf ω) := by
                  rw [hB, mul_assoc, ← mul_add]
                  apply mul_le_mul_of_nonneg_left _ hA0
                  linarith
                linarith
              have hFm : Measurable F := by
                have hm2 : Measurable (fun ω => (X H ω, X s ω)) := (hmeasX H).prodMk (hmeasX s)
                have : F = (fun p : (Fin 2 → ℕ) × (Fin 2 → ℕ) =>
                    countNorm (fun i => x i + (p.1 i - p.2 i)) ^ ρ) ∘ (fun ω => (X H ω, X s ω)) := by
                  funext ω; rfl
                rw [this]
                exact (measurable_of_countable _).comp hm2
              have hP1 : Integrable (fun ω => A * Sx + B * Real.exp (1 * Nf ω)) G.P :=
                (integrable_const _).add ((hpois 1).const_mul B)
              have hFP : Integrable F G.P := by
                refine Integrable.mono' hP1 hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
                rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω), one_mul]
                exact hFb ω
              refine ⟨fun ω => ⟨⟨_, (hgreat ω).1⟩, ⟨_, (hgreat ω).2⟩⟩, ?_, ?_, ?_⟩
              · rw [hsupF']; exact hFP
              · rw [hsupF']
                calc ∫ ω, F ω ∂G.P ≤ ∫ ω, (A * Sx + B * Real.exp (1 * Nf ω)) ∂G.P :=
                      integral_mono hFP hP1 (fun ω => by simpa using hFb ω)
                  _ = A * Sx + B * E1 := by
                      rw [integral_add (integrable_const _) ((hpois 1).const_mul B), integral_const,
                        integral_const_mul]
                      have hu : G.P.real univ = 1 := by simp
                      rw [hu, one_smul]
                  _ ≤ _ := by
                      have hS' : 1 + (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ = 1 + Sx := by rw [hSx]; ring
                      rw [hS']
                      exact ar1 A B E1 D E2 E3 Sx hA0 hB0 hE1n hD0.le hE2n hE3n hSx0
              intro a b ha hb
              -- jump-sum bound
              have hJ : ∀ c : Process, (∀ t ω, G.lower ≤ c t ω ∧ c t ω ≤ G.upper) → ∀ ω i,
                  (∑ᶠ t ∈ jumps G.h ω i, Real.log (c (Real.toNNReal t) ω / G.rate)) ≤ (X H ω i : ℝ) * lK := by
                intro c hc ω i
                have hfin : (jumps G.h ω i).Finite := (L1 (ω i) G.h hh.le).1
                rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
                have hterm : ∀ t ∈ hfin.toFinset, Real.log (c (Real.toNNReal t) ω / G.rate) ≤ lK := by
                  intro t _
                  have hc1 := hc (Real.toNNReal t) ω
                  apply Real.log_le_log (div_pos (by linarith) hr)
                  exact div_le_div_of_nonneg_right hc1.2 hr.le
                have h1 := Finset.sum_le_card_nsmul _ _ _ hterm
                rw [nsmul_eq_mul] at h1
                have hcard : (hfin.toFinset.card : ℝ) ≤ X H ω i := by
                  have := (L1 (ω i) G.h hh.le).2
                  rw [← Set.ncard_eq_toFinset_card _ hfin]
                  exact_mod_cast this.le
                exact h1.trans (mul_le_mul_of_nonneg_right hcard hlK0)
              have hI : ∀ a b : Process, (∀ t ω, G.lower ≤ a t ω ∧ a t ω ≤ G.upper) → (∀ t ω, G.lower ≤ b t ω ∧ b t ω ≤ G.upper) →
                  ∀ ω, -(∫ t in Icc (0 : ℝ) G.h,
                  (a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate)) ≤ 2 * G.rate * G.h := by
                intro a b ha hb ω
                by_cases hi : IntegrableOn (fun t : ℝ =>
                    (a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate)) (Icc (0 : ℝ) G.h)
                · have hmono' : ∫ t in Icc (0 : ℝ) G.h, (-(2 * G.rate)) ≤ ∫ t in Icc (0 : ℝ) G.h,
                      (a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate) := by
                    have hcst : IntegrableOn (fun _ : ℝ => -(2 * G.rate)) (Icc (0:ℝ) G.h) :=
                      integrableOn_const measure_Icc_lt_top.ne enorm_ne_top
                    apply integral_mono hcst hi
                    intro t
                    have := ha (Real.toNNReal t) ω
                    have := hb (Real.toNNReal t) ω
                    simp only
                    linarith
                  rw [setIntegral_const] at hmono'
                  simp [Real.volume_real_Icc, hh.le] at hmono'
                  nlinarith
                · rw [integral_undef hi, neg_zero]
                  positivity
              have hLL : ∀ a b : Process, (∀ t ω, G.lower ≤ a t ω ∧ a t ω ≤ G.upper) → (∀ t ω, G.lower ≤ b t ω ∧ b t ω ≤ G.upper) →
                  ∀ ω, G.logLikelihood a b ω ≤ lK * Nf ω + 2 * G.rate * G.h := by
                intro a b ha hb ω
                unfold Game.logLikelihood
                have h0 := hJ a ha ω 0
                have h1 := hJ b hb ω 1
                have h2 := hI a b ha hb ω
                simp only [hNf]
                linarith
              set w : Sample → ℝ≥0 := fun ω => Real.toNNReal (Real.exp (lK * Nf ω + 2 * G.rate * G.h)) with hw
              have hwm : Measurable w := by
                have hNm : Measurable Nf := by
                  simp only [hNf]
                  exact (measurable_of_countable (fun v : Fin 2 → ℕ => (v 0 : ℝ) + v 1)).comp (hmeasX H)
                exact measurable_real_toNNReal.comp
                  (Real.measurable_exp.comp ((hNm.const_mul lK).add_const _))
              have hwr : ∀ ω, (w ω : ℝ) = Real.exp (lK * Nf ω + 2 * G.rate * G.h) := fun ω =>
                Real.coe_toNNReal _ (Real.exp_pos _).le
              have hle : G.law a b ≤ G.P.withDensity (fun ω => (w ω : ENNReal)) := by
                unfold Game.law
                apply withDensity_mono
                refine Filter.Eventually.of_forall fun ω => ?_
                show ENNReal.ofReal _ ≤ ENNReal.ofReal _
                exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hLL a b ha.2 hb.2 ω))
              have hbnd2 : Integrable (fun ω => D * (A * Sx * Real.exp (lK * Nf ω) +
                  B * Real.exp ((lK + 1) * Nf ω))) G.P :=
                (((hpois lK).const_mul (A * Sx)).add ((hpois (lK + 1)).const_mul B)).const_mul D
              have hwF : ∀ ω, (w ω : ℝ) * F ω ≤ D * (A * Sx * Real.exp (lK * Nf ω) +
                  B * Real.exp ((lK + 1) * Nf ω)) := by
                intro ω
                rw [hwr]
                have e : Real.exp (lK * Nf ω + 2 * G.rate * G.h) = D * Real.exp (lK * Nf ω) := by
                  rw [hD, ← Real.exp_add]; ring_nf
                have e2 : Real.exp ((lK + 1) * Nf ω) = Real.exp (lK * Nf ω) * Real.exp (Nf ω) := by
                  rw [← Real.exp_add]; ring_nf
                rw [e, e2]
                have := hFb ω
                have hp := Real.exp_pos (lK * Nf ω)
                have : D * Real.exp (lK * Nf ω) * F ω ≤ D * Real.exp (lK * Nf ω) * (A * Sx + B * Real.exp (Nf ω)) :=
                  mul_le_mul_of_nonneg_left this (mul_pos hD0 hp).le
                exact this.trans_eq (by ring)
              have hνint : Integrable F (G.P.withDensity (fun ω => (w ω : ENNReal))) := by
                rw [integrable_withDensity_iff_integrable_smul hwm]
                refine Integrable.mono' hbnd2 ((hwm.coe_nnreal_real.mul hFm).aestronglyMeasurable)
                  (Filter.Eventually.of_forall fun ω => ?_)
                simp only [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs]
                rw [abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (hF0 ω))]
                exact hwF ω
              refine ⟨?_, ?_, ?_⟩
              · constructor
                unfold Game.law
                rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
                have hHH : Real.toNNReal G.h = H := Real.toNNReal_of_nonneg hh.le
                refine L6 G hG' (by rw [hHH]; exact hpois 1) (fun ω => Real.exp (lK * Nf ω + 2 * G.rate * G.h)) ?_ ?_ a b ha hb
                · have hb1 : (fun ω => Real.exp (lK * Nf ω + 2 * G.rate * G.h)) = fun ω => Real.exp (lK * Nf ω) * D := by
                    funext ω
                    rw [hD, ← Real.exp_add]
                  rw [hb1]
                  exact (hpois lK).mul_const D
                · intro a' b' ha' hb' ω
                  exact Real.exp_le_exp.2 (hLL a' b' ha' hb' ω)
              · rw [hsupF']; exact hνint.mono_measure hle
              · rw [hsupF']
                calc ∫ ω, F ω ∂(G.law a b) ≤ ∫ ω, F ω ∂(G.P.withDensity (fun ω => (w ω : ENNReal))) :=
                      integral_mono_measure hle (Filter.Eventually.of_forall hF0) hνint
                  _ = ∫ ω, (w ω : ℝ) * F ω ∂G.P := by
                      rw [integral_withDensity_eq_integral_smul hwm]
                      rfl
                  _ ≤ ∫ ω, D * (A * Sx * Real.exp (lK * Nf ω) + B * Real.exp ((lK + 1) * Nf ω)) ∂G.P := by
                      apply integral_mono _ hbnd2 hwF
                      exact (integrable_withDensity_iff_integrable_smul hwm).1 hνint
                  _ = D * (A * Sx * E2 + B * E3) := by
                      rw [integral_const_mul, integral_add ((hpois lK).const_mul _) ((hpois (lK + 1)).const_mul _),
                        integral_const_mul, integral_const_mul]
                  _ ≤ _ := by
                      have hS' : 1 + (x 0 : ℝ) ^ ρ + (x 1 : ℝ) ^ ρ = 1 + Sx := by rw [hSx]; ring
                      rw [hS']
                      exact ar2 A B E1 D E2 E3 Sx hA0 hB0 hE1n hD0.le hE2n hE3n hSx0
