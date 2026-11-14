-- Prove2me | Definitions.Def_RPLib_S3_HypPar
-- name    : RPLib_S3_HypPar
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:44:46.627079+00:00
-- url     : https://prove2.me/theorems/5d219cd5-932e-4254-91a4-bfc0e110ac60
-- title:
--   The Eichler-Selberg trace formula, the hyperbolic and parabolic total
-- statement:
--   The top-edge sum splits into the $c \ne 0$ part, which tends to $0$, and the upper triangular pairs $(\sigma e, \sigma n/e)$; hence $n^{k-1} B_k^{-1} \int_{\mathcal{D}} \tilde K$ equals the sum over $e \mid n$ and $\sigma = \pm 1$ of explicit pair constants, i.e. the hyperbolic term $A_3$ (the parabolic Eisenstein term $A_4$ vanishes for $k \ge 3$).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977

import Mathlib
import Definitions.Def_RPLib_S3_HypParP

/-!
# S3-HypParTerms, O8b: the analytic split of the top edge and the hyperbolic-parabolic total

* `split_point`, `tsum_split`: `Σ'_g wt g topI g = Σ'_{c ≠ 0} + Σ_{e ∣ n} Σ_{σ = ±1} Σ'_b (ut (σe) b (σ n/e))`.
* `norm_topI_le_maj`, `tendsto_cpart`: the `c ≠ 0` part tends to `0` as `Y → ∞`.
* `pairL`, `tendsto_pair`, `pair_conv`: the limit of each pair and its value `pairQ`.
* **`hypPar_main`**: `n^m B_{m+1}⁻¹ ∫_𝒟 Ktil (m+1) = Σ_{e ∣ n} Σ_{σ = ±1} pairQ (σe) (σ n/e)`.
-/

open Complex MeasureTheory Filter
open UpperHalfPlane hiding I
open scoped Topology Real Modular

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

section O8b

variable {M : ℕ} [NeZero M]

lemma ut_injective (a d : ℤ) : Function.Injective (fun b : ℤ => ut a b d) := by
  intro b b' h
  have h01 := congrFun (congrFun h 0) 1
  simpa using h01

lemma pair_facts {n e : ℕ} (he : e ∈ n.divisors) {σ : ℤ} (hσ : σ ∈ ({1, -1} : Finset ℤ)) :
    σ * (e : ℤ) * (σ * ((n / e : ℕ) : ℤ)) = n ∧ (σ * (e : ℤ)).natAbs = e ∧ (σ * (e : ℤ)).sign = σ := by
  have he' := Nat.mem_divisors.1 he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he'.1 (Nat.pos_of_ne_zero he'.2)
  have hepos' : (0 : ℤ) < e := by exact_mod_cast hepos
  have hmul : (e : ℤ) * ((n / e : ℕ) : ℤ) = n := by exact_mod_cast Nat.mul_div_cancel' he'.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl
  · refine ⟨by linear_combination hmul, by simp, ?_⟩
    rw [one_mul]
    exact Int.sign_eq_one_of_pos hepos'
  · refine ⟨by linear_combination hmul, by simp, ?_⟩
    exact Int.sign_eq_neg_one_of_neg (by linarith)

/-- Pointwise split of a function supported on determinant `n`. -/
lemma split_point {n : ℕ} (hn : 0 < n) (Φ : S3.Conj.Mat → ℂ) (hΦ : ∀ g : S3.Conj.Mat, g.det ≠ n → Φ g = 0)
    (g : S3.Conj.Mat) :
    Φ g = Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} Φ g +
      ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        Set.indicator (Set.range fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) Φ g := by
  by_cases hc : g 1 0 = 0
  · have h0 : Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} Φ g = 0 :=
      Set.indicator_of_notMem (by simpa using hc) _
    rw [h0, zero_add]
    by_cases hd : g.det = n
    · have hdet : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
      have had : g 0 0 * g 1 1 = n := by rw [hdet, hc] at hd; simpa using hd
      have hgut : g = ut (g 0 0) (g 0 1) (g 1 1) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [ut, hc]
      have hnz : (0 : ℤ) < n := by exact_mod_cast hn
      have ha0 : g 0 0 ≠ 0 := by intro h; rw [h, zero_mul] at had; omega
      have hnn : n = (g 0 0).natAbs * (g 1 1).natAbs := by
        have := congrArg Int.natAbs had
        rw [Int.natAbs_mul] at this
        simpa using this.symm
      have hapos : 0 < (g 0 0).natAbs := Int.natAbs_pos.2 ha0
      have hmem : (g 0 0).natAbs ∈ n.divisors :=
        Nat.mem_divisors.2 ⟨⟨_, hnn⟩, by omega⟩
      have hsmem : (g 0 0).sign ∈ ({1, -1} : Finset ℤ) := by
        rcases lt_or_gt_of_ne ha0 with h | h
        · simp [Int.sign_eq_neg_one_of_neg h]
        · simp [Int.sign_eq_one_of_pos h]
      have hdiv : n / (g 0 0).natAbs = (g 1 1).natAbs := by
        rw [hnn, Nat.mul_div_cancel_left _ hapos]
      have hdfact : (g 0 0).sign * (((n / (g 0 0).natAbs : ℕ)) : ℤ) = g 1 1 := by
        rw [hdiv]
        rcases lt_or_gt_of_ne ha0 with h | h
        · have hd' : g 1 1 < 0 := by nlinarith
          rw [Int.sign_eq_neg_one_of_neg h, ← Int.sign_eq_neg_one_of_neg hd', Int.sign_mul_natAbs]
        · have hd' : 0 < g 1 1 := by nlinarith
          rw [Int.sign_eq_one_of_pos h, ← Int.sign_eq_one_of_pos hd', Int.sign_mul_natAbs]
      rw [Finset.sum_eq_single_of_mem (g 0 0).natAbs hmem]
      · rw [Finset.sum_eq_single_of_mem (g 0 0).sign hsmem]
        · rw [Set.indicator_of_mem]
          refine ⟨g 0 1, ?_⟩
          simp only
          rw [Int.sign_mul_natAbs, hdfact]
          exact hgut.symm
        · intro σ hσ hne
          refine Set.indicator_of_notMem ?_ _
          rintro ⟨b, hb⟩
          apply hne
          have h00 := congrFun (congrFun hb 0) 0
          simp only [ut_00] at h00
          have := (pair_facts hmem hσ).2.2
          rw [h00] at this
          exact this.symm
      · intro e he hne
        refine Finset.sum_eq_zero fun σ hσ => Set.indicator_of_notMem ?_ _
        rintro ⟨b, hb⟩
        apply hne
        have h00 := congrFun (congrFun hb 0) 0
        simp only [ut_00] at h00
        have := (pair_facts he hσ).2.1
        rw [h00] at this
        exact this.symm
    · rw [hΦ g hd]
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun σ _ => ?_
      by_cases hg : g ∈ Set.range fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))
      · rw [Set.indicator_of_mem hg]
        exact hΦ g hd
      · exact Set.indicator_of_notMem hg _
  · have hR : ∀ (e : ℕ) (σ : ℤ),
        g ∉ Set.range fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ)) := by
      rintro e σ ⟨b, rfl⟩
      simp at hc
    rw [Set.indicator_of_mem (show g ∈ {g : S3.Conj.Mat | g 1 0 ≠ 0} from hc),
      Finset.sum_eq_zero (fun e _ => Finset.sum_eq_zero (fun σ _ => Set.indicator_of_notMem (hR e σ) _)),
      add_zero]

/-- The top-edge sum split into the `c ≠ 0` part and the upper-triangular pairs. -/
theorem tsum_split {n : ℕ} (hn : 0 < n) (Φ : S3.Conj.Mat → ℂ) (hs : Summable Φ)
    (hΦ : ∀ g : S3.Conj.Mat, g.det ≠ n → Φ g = 0) :
    ∑' g, Φ g = ∑' g, Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} Φ g +
      ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        ∑' b : ℤ, Φ (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) := by
  have hpair : ∀ (e : ℕ) (σ : ℤ),
      HasSum (Set.indicator (Set.range fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) Φ)
        (∑' b : ℤ, Φ (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ)))) := by
    intro e σ
    have hinj := ut_injective (σ * e) (σ * ((n / e : ℕ) : ℤ))
    rw [← hinj.hasSum_iff (fun x hx => Set.indicator_of_notMem hx _)]
    have hcomp : (Set.indicator (Set.range fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) Φ) ∘
        (fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) =
        fun b : ℤ => Φ (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) :=
      funext fun b => Set.indicator_of_mem (Set.mem_range_self b) _
    rw [hcomp]
    exact (hs.comp_injective hinj).hasSum
  have hall := (hs.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0}).hasSum.add
    (hasSum_sum (s := n.divisors) fun e _ =>
      hasSum_sum (s := ({1, -1} : Finset ℤ)) fun σ _ => hpair e σ)
  have hfun : (fun g => Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} Φ g +
      ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        Set.indicator (Set.range fun b : ℤ => ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) Φ g) = Φ :=
    funext fun g => (split_point hn Φ hΦ g).symm
  rw [hfun] at hall
  exact hall.tsum_eq

lemma norm_topI_le_maj {g : S3.Conj.Mat} {n : ℤ} (hdet : g.det = n) (hn : 0 < n) (hc : g 1 0 ≠ 0)
    {m : ℕ} (hm : 2 ≤ m) {Y : ℝ} (hY : 0 < Y) (hYn : 4 * (n : ℝ) ≤ Y ^ 2) :
    ‖topI g m Y‖ ≤ 144 * (n : ℝ) ^ 3 / Y * maj g := by
  unfold topI
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := 144 * (n : ℝ) ^ 3 / Y * maj g) (f := fun x : ℝ => VG g m (x + Y * I)) ?_
  · have h1 : |(1 / 2 : ℝ) - -(1 / 2)| = 1 := by norm_num
    rw [h1, mul_one] at h
    exact h
  · intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hz := norm_VG_le_maj hdet hn hc hm (z := (x : ℂ) + Y * I) ?_ ?_ ?_
    · simpa using hz
    · have hre : ((x : ℂ) + Y * I).re = x := by simp
      rw [hre, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    · simpa using hY
    · simpa using hYn

/-- The `c ≠ 0` part of the top edge tends to `0`. -/
theorem tendsto_cpart {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun Y : ℝ => ∑' g : S3.Conj.Mat,
      Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} (fun g => wt M n δ' g * topI g m Y) g) atTop (𝓝 0) := by
  set W0 : ℝ := (Fintype.card (Fin 2 → ZMod M) : ℝ) with hW0
  have hW0nn : 0 ≤ W0 := Nat.cast_nonneg _
  have hS := (hasSum_subtype_iff_indicator (f := maj) (s := cSet n)).mp (summable_maj n).hasSum
  set Smaj : ℝ := ∑' g : cSet n, maj g.1 with hSmaj
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine squeeze_zero_norm' (a := fun Y : ℝ => W0 * (144 * (n : ℝ) ^ 3 / Y) * Smaj) ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 * (n : ℝ))] with Y hY
    have hY1 : 0 < Y := by linarith
    have hYn : 4 * (n : ℝ) ≤ Y ^ 2 := by nlinarith
    refine tsum_of_norm_bounded (hS.mul_left (W0 * (144 * (n : ℝ) ^ 3 / Y))) fun g => ?_
    have hCnn : 0 ≤ W0 * (144 * (n : ℝ) ^ 3 / Y) := by positivity
    have hind : 0 ≤ Set.indicator (cSet n) maj g := Set.indicator_nonneg (fun g _ => maj_nonneg g) g
    by_cases hc : g 1 0 = 0
    · rw [Set.indicator_of_notMem (show g ∉ {g : S3.Conj.Mat | g 1 0 ≠ 0} by simpa using hc), norm_zero]
      exact mul_nonneg hCnn hind
    · rw [Set.indicator_of_mem (show g ∈ {g : S3.Conj.Mat | g 1 0 ≠ 0} from hc)]
      by_cases hd : g.det = n
      · rw [Set.indicator_of_mem (show g ∈ cSet n from ⟨hd, hc⟩), norm_mul]
        have h1 := norm_wt_le n δ' g
        have h2 := norm_topI_le_maj hd hn hc hm hY1 hYn
        calc ‖wt M n δ' g‖ * ‖topI g m Y‖ ≤ W0 * (144 * (n : ℝ) ^ 3 / Y * maj g) :=
              mul_le_mul h1 h2 (norm_nonneg _) hW0nn
          _ = W0 * (144 * (n : ℝ) ^ 3 / Y) * maj g := by ring
      · rw [wt_of_not (fun h => hd h.1), zero_mul, norm_zero]
        exact mul_nonneg hCnn hind
  · have h := ((tendsto_const_nhds (x := 144 * (n : ℝ) ^ 3)).div_atTop tendsto_id).const_mul W0
    simpa using h.mul_const Smaj

/-- The limit of the top edge of one upper-triangular pair `(a, d)`. -/
def pairL (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (m : ℕ) (a d : ℤ) : ℂ :=
  if a = d then (∑ x : ZMod M, wt M n δ' (ut a ((x.val : ℤ) + M) a)) * parC M a m
  else (∑ r ∈ Finset.Ico 0 |a - d|, wt M n δ' (ut a r d)) * hypC a d m

theorem tendsto_pair (n : ℤ) (δ' : ZMod M) {a d : ℤ} (had : 0 < a * d) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun Y : ℝ => ∑' b : ℤ, wt M n δ' (ut a b d) * topI (ut a b d) m Y) atTop
      (𝓝 (pairL M n δ' m a d)) := by
  unfold pairL
  by_cases hγ : a = d
  · rw [if_pos hγ]
    subst hγ
    have hs : a ≠ 0 := by intro h; rw [h, zero_mul] at had; exact lt_irrefl 0 had
    exact tendsto_par n δ' hs hm
  · rw [if_neg hγ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact ((hasSum_hyp n δ' had hγ hm hY).tsum_eq).symm

theorem pair_conv {m : ℕ} (hm : 2 ≤ m) (n : ℤ) (hn : 0 < n) (δ' : ZMod M) {a d : ℤ} (had : a * d = n) :
    (n : ℂ) ^ m * (Bergman.bergmanConst (m + 1))⁻¹ * (-(pairL M n δ' m a d)) =
      ((pairQ M δ' (m + 1) a d : ℚ) : ℂ) := by
  unfold pairL
  split_ifs with h
  · subst h
    have := pair_par (k := m + 1) (by omega) n δ' had hn
    simpa only [Nat.add_sub_cancel] using this
  · have := pair_hyp (k := m + 1) (by omega) n δ' had hn h
    simpa only [Nat.add_sub_cancel] using this

/-- **O8b**: the hyperbolic and parabolic contribution in closed form. -/
theorem hypPar_main {n : ℕ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m)
    (hfi : IntegrableOn (Ktil (m + 1) M (n : ℤ) δ') 𝒟) :
    (n : ℂ) ^ m * (Bergman.bergmanConst (m + 1))⁻¹ * ∫ z in 𝒟, Ktil (m + 1) M (n : ℤ) δ' z =
      ((∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        pairQ M δ' (m + 1) (σ * e) (σ * ((n / e : ℕ) : ℤ)) : ℚ) : ℂ) := by
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hsplit : ∀ Y : ℝ, 1 ≤ Y →
      -∑' g : S3.Conj.Mat, wt M n δ' g * topI g m Y =
        -(∑' g : S3.Conj.Mat,
            Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} (fun g => wt M n δ' g * topI g m Y) g +
          ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
            ∑' b : ℤ, wt M n δ' (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) *
              topI (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) m Y) := by
    intro Y hY
    rw [tsum_split hn (fun g => wt M n δ' g * topI g m Y) (summable_top hnz δ' hm hY)
      (fun g hg => by rw [wt_of_not (fun h => hg h.1), zero_mul])]
  have hlim1 := tendsto_trunc hnz δ' hm hfi
  have hlim2 : Tendsto (fun Y : ℝ =>
      -(∑' g : S3.Conj.Mat,
            Set.indicator {g : S3.Conj.Mat | g 1 0 ≠ 0} (fun g => wt M n δ' g * topI g m Y) g +
          ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
            ∑' b : ℤ, wt M n δ' (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) *
              topI (ut (σ * e) b (σ * ((n / e : ℕ) : ℤ))) m Y)) atTop
      (𝓝 (-(0 + ∑ e ∈ n.divisors, ∑ σ ∈ ({1, -1} : Finset ℤ),
        pairL M n δ' m (σ * e) (σ * ((n / e : ℕ) : ℤ))))) := by
    refine ((tendsto_cpart hnz δ' hm).add (tendsto_finsetSum _ fun e he =>
      tendsto_finsetSum _ fun σ hσ => ?_)).neg
    obtain ⟨hprod, -, -⟩ := pair_facts he hσ
    exact tendsto_pair n δ' (by rw [hprod]; exact hnz) (by omega)
  have hlim2' := hlim2.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    exact (hsplit Y hY).symm)
  have heq := tendsto_nhds_unique hlim1 hlim2'
  rw [heq, zero_add, show ((n : ℕ) : ℂ) = (((n : ℕ) : ℤ) : ℂ) from (Int.cast_natCast n).symm,
    ← Finset.sum_neg_distrib, Finset.mul_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  exact pair_conv hm n hnz δ' (pair_facts he hσ).1

end O8b

end RamanujanPetersson.HypPar


