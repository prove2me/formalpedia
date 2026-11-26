-- Prove2me | solution 1 for ApproximationMetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:40.601813+00:00
-- url     : https://prove2.me/submissions/34c03d7f-3e52-4c6a-90de-5b23bdffb377

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_MassSupFormula
import Definitions.Def_Tablet_PaoliniStepanovExists
import Definitions.Def_Tablet_BBAssertion
import Definitions.Def_Tablet_SurgeryEta
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_ApproximationMetric
import Theorems.Thm_BBAssertion
import Theorems.Thm_SurgeryEta


set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (hAK : MassSupFormulaStatement E) (hPS : PaoliniStepanovExistsStatement E)
    (GP : GeodesicPairing E)
    (T : MetricCurrent1 E) (hbdry : BoundaryZero T.toFun)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (γ : ℕ → ℕ → Curve E) (lam : ℕ → ℕ → ℝ),
      (∀ n : ℕ, ∀ i < n, 0 ≤ lam n i) ∧
      (∀ n : ℕ, ∀ i < n, IsClosedCurve (γ n i)) ∧
      (∀ n : ℕ, ∀ i < n, IsPiecewiseGeodesic (γ n i)) ∧
      (∀ ω : Form1 E, Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, lam n i * (curveCurrent (γ n i) ω / (γ n i).len))
        atTop (nhds (T.toFun ω))) ∧
      (∀ n : ℕ, ∑ i ∈ Finset.range n, |lam n i|
          ≤ (1 + ε) * (massOfFunctional T.toFun).toReal) ∧
      (∀ n : ℕ, ∀ i < n,
          morreyNorm (curveMeasure (γ n i)) ≤ ENNReal.ofReal (2088 / ε ^ 2)) := by
-- BODY
  classical
  obtain ⟨x0⟩ := ‹Nonempty E›
  -- Step 0: the padding curve `g0`, a constant curve of zero length at `x0`.
  set g0 : Curve E :=
    { len := 0
      len_nonneg := le_refl 0
      toFun := fun _ => x0
      clamped := fun _ => rfl
      unitSpeed := by
        intro x hx y hy
        rw [Set.mem_Icc] at hx hy
        have hx0 : x = 0 := le_antisymm hx.2 hx.1
        have hy0 : y = 0 := le_antisymm hy.2 hy.1
        rw [eVariationOn.constant_on (by intro a ha b hb; simp_all)]
        simp [hx0, hy0] } with hg0def
  have hg0closed : IsClosedCurve g0 := rfl
  have hg0pg : IsPiecewiseGeodesic g0 :=
    ⟨0, fun _ => 0, by intro a ha b hb _; rfl, rfl, rfl, by omega⟩
  have hg0cur : ∀ ω : Form1 E, curveCurrent g0 ω = 0 := by
    intro ω; simp [curveCurrent, hg0def]
  have hg0morrey : morreyNorm (curveMeasure g0) = 0 := by
    simp [curveMeasure, hg0def, morreyNorm]
  set M : ℝ := (massOfFunctional T.toFun).toReal with hMdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hεpos2 : (0:ℝ) < 1 + ε := by linarith
  -- Step 1: the degenerate case `T = 0`.
  by_cases hT0 : T.toFun = 0
  · refine ⟨fun _ _ => g0, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n i _; exact le_refl 0
    · intro n i _; exact hg0closed
    · intro n i _; exact hg0pg
    · intro ω
      have h1 : (fun n : ℕ => ∑ _i ∈ Finset.range n,
          (0:ℝ) * (curveCurrent g0 ω / g0.len)) = fun _ => (0:ℝ) := by
        funext n; simp
      rw [h1, hT0]
      simpa using tendsto_const_nhds
    · intro n; simpa using mul_nonneg (le_of_lt hεpos2) hM0
    · intro n i _; rw [hg0morrey]; simp
  -- Step 2: apply `BBAssertion`.
  obtain ⟨nhat, ghat, hnpos, hntop, hclosed, hpg, -, -, hcur, -, hlenlim⟩ :=
    BBAssertion hAK hPS GP T hT0 hbdry
  -- Step 3: apply `SurgeryEta` to each `ghat l i` at `η = ε/2`, totalized off-range.
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hε2a : (0:ℝ) < ε / 2 := by linarith
  have hε2b : ε / 2 ≤ 1 := by linarith
  have hconst : (522 : ℝ) / (ε / 2) ^ 2 = 2088 / ε ^ 2 := by field_simp; ring
  have hsurg : ∀ l i : ℕ, ∃ (N : ℕ) (u : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (u j)) ∧ (∀ j, IsPiecewiseGeodesic (u j)) ∧
      (∀ j, morreyNorm (curveMeasure (u j)) ≤ ENNReal.ofReal (2088 / ε ^ 2)) ∧
      ((1 ≤ l ∧ i < nhat l) →
        ((∀ ω : Form1 E, curveCurrent (ghat l i) ω = ∑ j, curveCurrent (u j) ω) ∧
          (∑ j, (u j).len) ≤ (1 + ε / 2) * (ghat l i).len)) := by
    intro l i
    by_cases h : 1 ≤ l ∧ i < nhat l
    · obtain ⟨N, u, hN, hc, hp, hcurr, hlen, hmor⟩ :=
        SurgeryEta GP (ghat l i) (ε / 2) hε2a hε2b (hclosed l h.1 i h.2) (hpg l h.1 i h.2)
      exact ⟨N, u, hN, hc, hp, by rw [← hconst]; exact hmor, fun _ => ⟨hcurr, hlen⟩⟩
    · exact ⟨1, fun _ => g0, one_pos, fun _ => hg0closed, fun _ => hg0pg,
        fun _ => by rw [hg0morrey]; simp, fun hh => absurd hh h⟩
  choose Nhat gg hNpos hggcl hggpg hggmor hggcond using hsurg
  set Nl : ℕ → ℕ := fun l => ∑ i ∈ Finset.range (nhat l), Nhat l i with hNldef
  have hNge : ∀ l : ℕ, nhat l ≤ Nl l := by
    intro l
    calc nhat l = ∑ _i ∈ Finset.range (nhat l), 1 := by simp
      _ ≤ ∑ i ∈ Finset.range (nhat l), Nhat l i :=
          Finset.sum_le_sum (fun i _ => hNpos l i)
  have hcard : ∀ l : ℕ, Fintype.card ((i : Fin (nhat l)) × Fin (Nhat l ↑i)) = Nl l := by
    intro l
    simp [Fintype.card_sigma, hNldef, Fin.sum_univ_eq_sum_range]
  obtain ⟨eqv⟩ : Nonempty (∀ l : ℕ, ((i : Fin (nhat l)) × Fin (Nhat l ↑i)) ≃ Fin (Nl l)) :=
    ⟨fun l => Fintype.equivFinOfCardEq (hcard l)⟩
  set bar : ℕ → ℕ → Curve E := fun l k =>
    if h : k < Nl l then
      (fun σ : (i : Fin (nhat l)) × Fin (Nhat l ↑i) => gg l ↑σ.1 σ.2) ((eqv l).symm ⟨k, h⟩)
    else g0 with hbardef
  have hreindex : ∀ (l : ℕ) (F : Curve E → ℝ),
      ∑ k ∈ Finset.range (Nl l), F (bar l k)
        = ∑ i ∈ Finset.range (nhat l), ∑ j : Fin (Nhat l i), F (gg l i j) := by
    intro l F
    have hstep : ∀ σ : (i : Fin (nhat l)) × Fin (Nhat l ↑i),
        bar l ↑((eqv l) σ) = gg l ↑σ.1 σ.2 := by
      intro σ
      have h : (↑((eqv l) σ) : ℕ) < Nl l := ((eqv l) σ).isLt
      simp only [hbardef, dif_pos h, Fin.eta]
      exact congrArg (fun τ : (i : Fin (nhat l)) × Fin (Nhat l ↑i) => gg l ↑τ.1 τ.2)
        ((eqv l).symm_apply_apply σ)
    rw [← Fin.sum_univ_eq_sum_range (fun k => F (bar l k)) (Nl l)]
    rw [← Equiv.sum_comp (eqv l) (fun k : Fin (Nl l) => F (bar l ↑k))]
    simp only [hstep]
    rw [Fintype.sum_sigma]
    exact Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (Nhat l i), F (gg l i j)) (nhat l)
  have hbarcl : ∀ l k : ℕ, IsClosedCurve (bar l k) := by
    intro l k
    simp only [hbardef]
    split
    · exact hggcl _ _ _
    · exact hg0closed
  have hbarpg : ∀ l k : ℕ, IsPiecewiseGeodesic (bar l k) := by
    intro l k
    simp only [hbardef]
    split
    · exact hggpg _ _ _
    · exact hg0pg
  have hbarmor : ∀ l k : ℕ,
      morreyNorm (curveMeasure (bar l k)) ≤ ENNReal.ofReal (2088 / ε ^ 2) := by
    intro l k
    simp only [hbardef]
    split
    · exact hggmor _ _ _
    · rw [hg0morrey]; simp
  -- Step 4: eq. lengthlimsup, in the eventual form needed for Step 5.
  have hDpos : ∀ l : ℕ, 1 ≤ l → (0:ℝ) < (nhat l : ℝ) * l := by
    intro l hl
    have h1 : (0:ℝ) < (nhat l : ℝ) := by exact_mod_cast hnpos l
    have h2 : (0:ℝ) < (l : ℝ) := by exact_mod_cast hl
    exact mul_pos h1 h2
  have hAle : ∀ l : ℕ, 1 ≤ l →
      (1 / ((nhat l : ℝ) * l)) * ∑ k ∈ Finset.range (Nl l), (bar l k).len
        ≤ (1 + ε / 2) *
            ((1 / ((nhat l : ℝ) * l)) * ∑ i ∈ Finset.range (nhat l), (ghat l i).len) := by
    intro l hl
    have hsum : ∑ k ∈ Finset.range (Nl l), (bar l k).len
        ≤ (1 + ε / 2) * ∑ i ∈ Finset.range (nhat l), (ghat l i).len := by
      rw [hreindex l (fun c => c.len), Finset.mul_sum]
      exact Finset.sum_le_sum (fun i hi => (hggcond l i ⟨hl, Finset.mem_range.mp hi⟩).2)
    have hinv : (0:ℝ) ≤ 1 / ((nhat l : ℝ) * l) := le_of_lt (one_div_pos.mpr (hDpos l hl))
    calc (1 / ((nhat l : ℝ) * l)) * ∑ k ∈ Finset.range (Nl l), (bar l k).len
        ≤ (1 / ((nhat l : ℝ) * l)) *
            ((1 + ε / 2) * ∑ i ∈ Finset.range (nhat l), (ghat l i).len) :=
          mul_le_mul_of_nonneg_left hsum hinv
      _ = (1 + ε / 2) *
            ((1 / ((nhat l : ℝ) * l)) * ∑ i ∈ Finset.range (nhat l), (ghat l i).len) := by
          ring
  have hBlim : Tendsto (fun l : ℕ => (1 + ε / 2) *
      ((1 / ((nhat l : ℝ) * l)) * ∑ i ∈ Finset.range (nhat l), (ghat l i).len))
      atTop (nhds ((1 + ε / 2) * 1)) := hlenlim.const_mul _
  have hev1 : ∀ᶠ l : ℕ in atTop, (1 + ε / 2) *
      ((1 / ((nhat l : ℝ) * l)) * ∑ i ∈ Finset.range (nhat l), (ghat l i).len) < 1 + ε :=
    hBlim.eventually_lt_const (by linarith)
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp (hev1.and (eventually_ge_atTop 1))
  have hscaled : ∀ l : ℕ, L0 ≤ l →
      (1 / ((nhat l : ℝ) * l)) * ∑ k ∈ Finset.range (Nl l), (bar l k).len ≤ 1 + ε := by
    intro l hl
    obtain ⟨h1, h2⟩ := hL0 l hl
    exact le_trans (hAle l h2) (le_of_lt h1)
  have hL0one : ∀ l : ℕ, L0 ≤ l → 1 ≤ l := fun l hl => (hL0 l hl).2
  -- Step 5: extracting the subsequence `(l_r)`.
  have hNtop : Tendsto Nl atTop atTop := tendsto_atTop_mono hNge hntop
  have hstepex : ∀ m : ℕ, ∃ m' : ℕ, m < m' ∧ L0 ≤ m' ∧ Nl m < Nl m' := by
    intro m
    obtain ⟨m', h1, h2, h3⟩ :=
      ((hNtop.eventually_gt_atTop (Nl m)).and
        ((eventually_gt_atTop m).and (eventually_ge_atTop L0))).exists
    exact ⟨m', h2, h3, h1⟩
  obtain ⟨lseq, hlseq0, hlseqstep⟩ :
      ∃ L : ℕ → ℕ, L 0 = L0 ∧
        ∀ r : ℕ, L r < L (r + 1) ∧ L0 ≤ L (r + 1) ∧ Nl (L r) < Nl (L (r + 1)) := by
    refine ⟨fun r => Nat.rec L0 (fun _ prev => (hstepex prev).choose) r, rfl, fun r => ?_⟩
    exact (hstepex _).choose_spec
  have hlseqge : ∀ r : ℕ, L0 ≤ lseq r := by
    intro r
    cases r with
    | zero => rw [hlseq0]
    | succ r => exact (hlseqstep r).2.1
  have hlseqmono : StrictMono lseq := strictMono_nat_of_lt_succ (fun r => (hlseqstep r).1)
  have hNlseqmono : StrictMono (fun r => Nl (lseq r)) :=
    strictMono_nat_of_lt_succ (fun r => (hlseqstep r).2.2)
  have hlseqtop : Tendsto lseq atTop atTop := hlseqmono.tendsto_atTop
  -- `r(n)`, via `Nat.findGreatest`.
  obtain ⟨rr, hrrdef⟩ :
      ∃ f : ℕ → ℕ, ∀ n : ℕ, f n = Nat.findGreatest (fun r => Nl (lseq r) ≤ n) n :=
    ⟨_, fun _ => rfl⟩
  have hrrle : ∀ n : ℕ, Nl (lseq 0) ≤ n → Nl (lseq (rr n)) ≤ n := by
    intro n hn
    rw [hrrdef]
    exact Nat.findGreatest_spec (P := fun r => Nl (lseq r) ≤ n) (Nat.zero_le n) hn
  have hrrgt : ∀ n : ℕ, Nl (lseq 0) ≤ n → n < Nl (lseq (rr n + 1)) := by
    intro n hn
    by_contra hcon
    push_neg at hcon
    have h1 : rr n + 1 ≤ Nl (lseq (rr n + 1)) := hNlseqmono.le_apply
    refine Nat.findGreatest_is_greatest (P := fun r => Nl (lseq r) ≤ n) ?_
      (le_trans h1 hcon) hcon
    rw [← hrrdef]
    exact Nat.lt_succ_self _
  have hrrtop : Tendsto rr atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun R => ⟨Nl (lseq R), fun n hn => ?_⟩)
    have hRle : R ≤ Nl (lseq R) := hNlseqmono.le_apply
    rw [hrrdef]
    exact Nat.le_findGreatest (le_trans hRle hn) hn
  -- Step 6: constructing `γ` and `lam`.
  have hDp : ∀ r : ℕ, (0:ℝ) < (nhat (lseq r) : ℝ) * (lseq r) :=
    fun r => hDpos _ (hL0one _ (hlseqge r))
  have hcurzero : ∀ (cv : Curve E) (ω : Form1 E), cv.len = 0 → curveCurrent cv ω = 0 := by
    intro cv ω h; simp [curveCurrent, h]
  -- Step 8: the divided-term identity (pm-0040 (1)).
  have hdivid : ∀ a d ℓ c : ℝ, d ≠ 0 → (ℓ = 0 → c = 0) →
      a * ℓ / d * (c / ℓ) = a / d * c := by
    intro a d ℓ c hd hℓ
    rcases eq_or_ne ℓ 0 with h | h
    · simp [h, hℓ h]
    · field_simp
  obtain ⟨gam, hgamdef⟩ : ∃ f : ℕ → ℕ → Curve E, ∀ n i : ℕ,
      f n i = if Nl (lseq 0) ≤ n ∧ i < Nl (lseq (rr n)) then bar (lseq (rr n)) i else g0 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨lam, hlamdef⟩ : ∃ f : ℕ → ℕ → ℝ, ∀ n i : ℕ,
      f n i = if Nl (lseq 0) ≤ n ∧ i < Nl (lseq (rr n)) then
        M * (bar (lseq (rr n)) i).len / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n))) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hlamzero : ∀ n i : ℕ, ¬(Nl (lseq 0) ≤ n ∧ i < Nl (lseq (rr n))) → lam n i = 0 := by
    intro n i h; rw [hlamdef, if_neg h]
  have hlamnonneg : ∀ n i : ℕ, 0 ≤ lam n i := by
    intro n i
    by_cases h : Nl (lseq 0) ≤ n ∧ i < Nl (lseq (rr n))
    · rw [hlamdef, if_pos h]
      exact div_nonneg (mul_nonneg hM0 (bar _ _).len_nonneg) (le_of_lt (hDp _))
    · rw [hlamzero n i h]
  refine ⟨gam, lam, fun n i _ => hlamnonneg n i, ?_, ?_, ?_, ?_, ?_⟩
  -- Step 7: clause (a), closedness and piecewise-geodesicity.
  · intro n i _
    rw [hgamdef]
    split
    · exact hbarcl _ _
    · exact hg0closed
  · intro n i _
    rw [hgamdef]
    split
    · exact hbarpg _ _
    · exact hg0pg
  -- Step 9: clause (b), the limit.
  · intro ω
    have key : ∀ n : ℕ, Nl (lseq 0) ≤ n →
        ∑ i ∈ Finset.range n, lam n i * (curveCurrent (gam n i) ω / (gam n i).len)
          = M / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n))) *
              ∑ k ∈ Finset.range (Nl (lseq (rr n))), curveCurrent (bar (lseq (rr n)) k) ω := by
      intro n hn
      have hsub : Finset.range (Nl (lseq (rr n))) ⊆ Finset.range n :=
        Finset.range_subset_range.mpr (hrrle n hn)
      have hout : ∀ i ∈ Finset.range n, i ∉ Finset.range (Nl (lseq (rr n))) →
          lam n i * (curveCurrent (gam n i) ω / (gam n i).len) = 0 := by
        intro i _ hi
        rw [hlamzero n i (fun hcon => hi (Finset.mem_range.mpr hcon.2)), zero_mul]
      rw [← Finset.sum_subset hsub hout, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hc : Nl (lseq 0) ≤ n ∧ i < Nl (lseq (rr n)) := ⟨hn, Finset.mem_range.mp hi⟩
      rw [hlamdef n i, hgamdef n i, if_pos hc, if_pos hc]
      exact hdivid M _ _ _ (ne_of_gt (hDp _)) (fun h0 => hcurzero _ ω h0)
    have hSlim : Tendsto (fun r : ℕ =>
        M / ((nhat (lseq r) : ℝ) * (lseq r)) *
          ∑ k ∈ Finset.range (Nl (lseq r)), curveCurrent (bar (lseq r) k) ω)
        atTop (nhds (T.toFun ω)) := by
      have hV : ∀ r : ℕ,
          M / ((nhat (lseq r) : ℝ) * (lseq r)) *
            ∑ k ∈ Finset.range (Nl (lseq r)), curveCurrent (bar (lseq r) k) ω
          = M / ((nhat (lseq r) : ℝ) * (lseq r)) *
            ∑ i ∈ Finset.range (nhat (lseq r)), curveCurrent (ghat (lseq r) i) ω := by
        intro r
        congr 1
        rw [hreindex (lseq r) (fun c => curveCurrent c ω)]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        exact ((hggcond (lseq r) i ⟨hL0one _ (hlseqge r), Finset.mem_range.mp hi⟩).1 ω).symm
      simp only [hV]
      exact (hcur ω).comp hlseqtop
    have h1 : Tendsto (fun n : ℕ =>
        M / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n))) *
          ∑ k ∈ Finset.range (Nl (lseq (rr n))), curveCurrent (bar (lseq (rr n)) k) ω)
        atTop (nhds (T.toFun ω)) := hSlim.comp hrrtop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (Nl (lseq 0))] with n hn
    exact (key n hn).symm
  -- Step 10: clause (c), the mass bound.
  · intro n
    by_cases hn : Nl (lseq 0) ≤ n
    · have hsub : Finset.range (Nl (lseq (rr n))) ⊆ Finset.range n :=
        Finset.range_subset_range.mpr (hrrle n hn)
      have h1 : ∑ i ∈ Finset.range n, |lam n i|
          = ∑ i ∈ Finset.range (Nl (lseq (rr n))), |lam n i| := by
        refine (Finset.sum_subset hsub ?_).symm
        intro i _ hi
        rw [hlamzero n i (fun hcon => hi (Finset.mem_range.mpr hcon.2)), abs_zero]
      have h2 : ∑ i ∈ Finset.range (Nl (lseq (rr n))), |lam n i|
          = M / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n))) *
            ∑ k ∈ Finset.range (Nl (lseq (rr n))), (bar (lseq (rr n)) k).len := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hc : Nl (lseq 0) ≤ n ∧ i < Nl (lseq (rr n)) := ⟨hn, Finset.mem_range.mp hi⟩
        rw [abs_of_nonneg (hlamnonneg n i), hlamdef n i, if_pos hc]
        ring
      rw [h1, h2]
      have hsc := hscaled (lseq (rr n)) (hlseqge (rr n))
      have h3 : M / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n))) *
          ∑ k ∈ Finset.range (Nl (lseq (rr n))), (bar (lseq (rr n)) k).len
          = M * ((1 / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n)))) *
              ∑ k ∈ Finset.range (Nl (lseq (rr n))), (bar (lseq (rr n)) k).len) := by
        ring
      rw [h3]
      calc M * ((1 / ((nhat (lseq (rr n)) : ℝ) * (lseq (rr n)))) *
              ∑ k ∈ Finset.range (Nl (lseq (rr n))), (bar (lseq (rr n)) k).len)
          ≤ M * (1 + ε) := mul_le_mul_of_nonneg_left hsc hM0
        _ = (1 + ε) * M := by ring
    · have h1 : ∑ i ∈ Finset.range n, |lam n i| = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [hlamzero n i (fun hcon => hn hcon.1), abs_zero]
      rw [h1]
      exact mul_nonneg (le_of_lt hεpos2) hM0
  -- Step 11: clause (d), the Morrey bound.
  · intro n i _
    rw [hgamdef]
    split
    · exact hbarmor _ _
    · rw [hg0morrey]; simp
