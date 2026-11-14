-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Percentile
-- name    : BCFGJPSSV26_Stable_Percentile
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:42.690209+00:00
-- url     : https://prove2.me/theorems/74fef2b8-befa-49ad-bb9b-624b136c3e37
-- title:
--   BCFGJPSSV26.Stable.Percentile — Percentiles and cores
-- statement:
--   This is module `BCFGJPSSV26.Stable.Percentile` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   For a set `C` of clients with a center `c` (in the analysis: an optimal cluster and its center):
--
--   * `BCFGJPSSV26.Stable.costAt`: the cost `∑_{j ∈ C} d(j, c)` of `C` at `c`;
--   * `BCFGJPSSV26.Stable.per` [BCFGJPSSV26b, Section 2]: the `ε`-percentile, the least distance
--     `t = d(j, c)`, `j ∈ C`, such that at least `ε |C|` clients of `C` are within `t` of `c`;
--   * `BCFGJPSSV26.Stable.core`: the clients within `(1 + γ) per` of `c`.
--
--   The basic facts: at least `ε |C|` clients are within `per`, fewer than
--   `ε |C|` strictly closer (`BCFGJPSSV26.Stable.per_count_le`, `BCFGJPSSV26.Stable.per_count_lt`),
--   hence `(1 - ε) |C| per ≤ cost` (`BCFGJPSSV26.Stable.per_mul_le_costAt`); the distance from `c`
--   to a set `S` is at most `per` plus the average distance of the core to `S`
--   (`BCFGJPSSV26.Stable.dSet_center_le_per`), and `|C| d(c, S) ≤ cost(C, c) + cost_S(C)`
--   (`BCFGJPSSV26.Stable.card_mul_dSet_le`).
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Percentile`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Percentile.lean

module

public import Definitions.Def_BCFGJPSSV26_Basic_Metric

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Percentile` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Percentiles and cores

For a set `C` of clients with a center `c` (in the analysis: an optimal cluster and its center):

* `BCFGJPSSV26.Stable.costAt`: the cost `∑_{j ∈ C} d(j, c)` of `C` at `c`;
* `BCFGJPSSV26.Stable.per` [BCFGJPSSV26b, Section 2]: the `ε`-percentile, the least distance
  `t = d(j, c)`, `j ∈ C`, such that at least `ε |C|` clients of `C` are within `t` of `c`;
* `BCFGJPSSV26.Stable.core`: the clients within `(1 + γ) per` of `c`.

The basic facts: at least `ε |C|` clients are within `per`, fewer than
`ε |C|` strictly closer (`BCFGJPSSV26.Stable.per_count_le`, `BCFGJPSSV26.Stable.per_count_lt`),
hence `(1 - ε) |C| per ≤ cost` (`BCFGJPSSV26.Stable.per_mul_le_costAt`); the distance from `c`
to a set `S` is at most `per` plus the average distance of the core to `S`
(`BCFGJPSSV26.Stable.dSet_center_le_per`), and `|C| d(c, S) ≤ cost(C, c) + cost_S(C)`
(`BCFGJPSSV26.Stable.card_mul_dSet_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable (I : Instance)

/-- The cost `∑_{j ∈ C} d(j, c)` of the clients of `C` at the facility `c`. -/
noncomputable def costAt (c : Fin I.m) (C : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ C, I.dd (.inl j) (.inr c)

open Classical in
/-- The **`ε`-percentile** of `C` around `c`: the least distance `t = d(j, c)`, `j ∈ C`, such that
at least `ε |C|` clients of `C` are within `t`; `0` if there is none (only if `C = ∅` or
`ε > 1`). -/
noncomputable def per (ε : ℝ) (C : Finset (Fin I.n)) (c : Fin I.m) : ℝ :=
  if h : ((C.image fun j ↦ I.dd (.inl j) (.inr c)).filter fun t ↦
      ε * C.card ≤ (C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ t).card).Nonempty then
    ((C.image fun j ↦ I.dd (.inl j) (.inr c)).filter fun t ↦
      ε * C.card ≤ (C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ t).card).min' h
  else 0

/-- The **core** `core_γ(C) = {j ∈ C : d(j, c) ≤ (1 + γ) per}`. -/
noncomputable def core (ε γ : ℝ) (C : Finset (Fin I.n)) (c : Fin I.m) : Finset (Fin I.n) :=
  C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ (1 + γ) * per I ε C c

variable {I} {ε : ℝ}

/-! ### The percentile -/

theorem per_nonneg (hv : I.Valid) (ε : ℝ) (C : Finset (Fin I.n)) (c : Fin I.m) :
    0 ≤ per I ε C c := by
  classical
  unfold per
  split_ifs with h
  · have := Finset.min'_mem _ h
    simp only [mem_filter, mem_image] at this
    obtain ⟨⟨j, -, hj⟩, -⟩ := this
    rw [← hj]
    exact Instance.dd_nonneg hv _ _
  · exact le_rfl

/-- The percentile is attained, and satisfies its defining condition. -/
private theorem per_spec (hε : ε ≤ 1) {C : Finset (Fin I.n)} (hC : C.Nonempty) (c : Fin I.m) :
    (∃ j ∈ C, I.dd (.inl j) (.inr c) = per I ε C c) ∧
      ε * C.card ≤ (C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ per I ε C c).card := by
  classical
  have hne : ((C.image fun j ↦ I.dd (.inl j) (.inr c)).filter fun t ↦
      ε * C.card ≤ (C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ t).card).Nonempty := by
    obtain ⟨j₀, hj₀, hmax⟩ := C.exists_max_image (fun j ↦ I.dd (.inl j) (.inr c)) hC
    refine ⟨I.dd (.inl j₀) (.inr c), mem_filter.2 ⟨mem_image_of_mem _ hj₀, ?_⟩⟩
    rw [filter_true_of_mem hmax]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hε
  have h := min'_mem _ hne
  unfold per
  rw [dif_pos hne]
  simp only [mem_filter, mem_image] at h
  exact ⟨h.1, h.2⟩

/-- The percentile is at most every distance satisfying its defining condition. -/
private theorem per_le_of_mem {C : Finset (Fin I.n)} (c : Fin I.m) {j : Fin I.n} (hj : j ∈ C)
    (h : ε * C.card ≤
      (C.filter fun j' ↦ I.dd (.inl j') (.inr c) ≤ I.dd (.inl j) (.inr c)).card) :
    per I ε C c ≤ I.dd (.inl j) (.inr c) := by
  classical
  have hmem : I.dd (.inl j) (.inr c) ∈ ((C.image fun j ↦ I.dd (.inl j) (.inr c)).filter
      fun t ↦ ε * C.card ≤ (C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ t).card) :=
    mem_filter.2 ⟨mem_image_of_mem _ hj, h⟩
  unfold per
  rw [dif_pos ⟨_, hmem⟩]
  exact min'_le _ _ hmem

/-- At least `ε |C|` clients of `C` are within `per` of `c`. -/
theorem per_count_le (hε : ε ≤ 1) {C : Finset (Fin I.n)} (hC : C.Nonempty) (c : Fin I.m) :
    ε * C.card ≤ (C.filter fun j ↦ I.dd (.inl j) (.inr c) ≤ per I ε C c).card :=
  (per_spec hε hC c).2

/-- Fewer than `ε |C|` clients of `C` are strictly closer than `per`. -/
theorem per_count_lt (hε0 : 0 < ε) (hε : ε ≤ 1) {C : Finset (Fin I.n)} (hC : C.Nonempty)
    (c : Fin I.m) :
    ((C.filter fun j ↦ I.dd (.inl j) (.inr c) < per I ε C c).card : ℝ) < ε * C.card := by
  classical
  have _ : ε ≤ 1 := hε
  by_contra hlt
  push Not at hlt
  have hpos : (0 : ℝ) < ε * C.card := mul_pos hε0 (by exact_mod_cast hC.card_pos)
  have hA : (C.filter fun j ↦ I.dd (.inl j) (.inr c) < per I ε C c).Nonempty := by
    rw [← card_pos]
    have : (0 : ℝ) < (C.filter fun j ↦ I.dd (.inl j) (.inr c) < per I ε C c).card :=
      hpos.trans_le hlt
    exact_mod_cast this
  obtain ⟨j₁, hj₁, hmax⟩ := exists_max_image _ (fun j ↦ I.dd (.inl j) (.inr c)) hA
  have hj₁' := (mem_filter.1 hj₁)
  have hle : per I ε C c ≤ I.dd (.inl j₁) (.inr c) := by
    refine per_le_of_mem c hj₁'.1 (hlt.trans ?_)
    exact_mod_cast card_le_card fun j hj ↦ mem_filter.2 ⟨(mem_filter.1 hj).1, hmax j hj⟩
  exact absurd hj₁'.2 (not_lt.2 hle)

/-- The percentile is the distance of some client of `C`. -/
theorem exists_eq_per (hε : ε ≤ 1) {C : Finset (Fin I.n)} (hC : C.Nonempty) (c : Fin I.m) :
    ∃ j ∈ C, I.dd (.inl j) (.inr c) = per I ε C c :=
  (per_spec hε hC c).1

/-- `(1 - ε) |C| per ≤ ∑_{j ∈ C} d(j, c)`: more than `(1 - ε)|C|` clients pay at least
`per`. -/
theorem per_mul_le_costAt (hv : I.Valid) (hε0 : 0 < ε) (hε : ε ≤ 1) {C : Finset (Fin I.n)}
    (hC : C.Nonempty) (c : Fin I.m) : (1 - ε) * C.card * per I ε C c ≤ costAt I c C := by
  classical
  have hlt := per_count_lt hε0 hε hC c
  have hsplit := card_filter_add_card_filter_not (s := C)
    (fun j ↦ I.dd (.inl j) (.inr c) < per I ε C c)
  have hsplit' : ((C.filter fun j ↦ I.dd (.inl j) (.inr c) < per I ε C c).card : ℝ) +
      (C.filter fun j ↦ ¬ I.dd (.inl j) (.inr c) < per I ε C c).card = C.card := by
    exact_mod_cast hsplit
  have hper := per_nonneg hv ε C c
  have hG : ((C.filter fun j ↦ ¬ I.dd (.inl j) (.inr c) < per I ε C c).card : ℝ) *
      per I ε C c ≤ costAt I c C := by
    calc _ = ∑ _j ∈ C.filter (fun j ↦ ¬ I.dd (.inl j) (.inr c) < per I ε C c), per I ε C c := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ C.filter (fun j ↦ ¬ I.dd (.inl j) (.inr c) < per I ε C c),
            I.dd (.inl j) (.inr c) :=
          sum_le_sum fun j hj ↦ not_lt.1 (mem_filter.1 hj).2
      _ ≤ costAt I c C :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ ↦
            Instance.dd_nonneg hv _ _
  have : (1 - ε) * C.card ≤ (C.filter fun j ↦ ¬ I.dd (.inl j) (.inr c) < per I ε C c).card := by
    linarith
  calc (1 - ε) * C.card * per I ε C c
      ≤ (C.filter fun j ↦ ¬ I.dd (.inl j) (.inr c) < per I ε C c).card * per I ε C c :=
        mul_le_mul_of_nonneg_right this hper
    _ ≤ costAt I c C := hG

/-- `per ≤ (1 + 2ε) avg` for `ε ≤ 1/2`. -/
theorem per_le_avg (hv : I.Valid) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) {C : Finset (Fin I.n)}
    (hC : C.Nonempty) (c : Fin I.m) :
    per I ε C c ≤ (1 + 2 * ε) * (costAt I c C / C.card) := by
  have h3 := per_mul_le_costAt hv hε (by linarith) hC c
  have hper := per_nonneg hv ε C c
  have hcard : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  rw [mul_div_assoc', le_div_iff₀ hcard]
  have hk : 0 ≤ ε * (1 - 2 * ε) := mul_nonneg hε.le (by linarith)
  have : 0 ≤ ε * (1 - 2 * ε) * (C.card * per I ε C c) :=
    mul_nonneg hk (mul_nonneg hcard.le hper)
  nlinarith

/-! ### Cores -/

theorem core_subset (ε γ : ℝ) (C : Finset (Fin I.n)) (c : Fin I.m) : core I ε γ C c ⊆ C :=
  filter_subset _ _

theorem core_mono {ε γ γ' : ℝ} (hγ : γ ≤ γ') (hv : I.Valid) (C : Finset (Fin I.n))
    (c : Fin I.m) : core I ε γ C c ⊆ core I ε γ' C c := by
  intro j hj
  simp only [core, mem_filter] at hj ⊢
  refine ⟨hj.1, hj.2.trans ?_⟩
  have := per_nonneg hv ε C c
  nlinarith

/-- `|core_0| ≥ ε |C|`. -/
theorem card_core_ge (hv : I.Valid) (hε : ε ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) {C : Finset (Fin I.n)}
    (hC : C.Nonempty) (c : Fin I.m) : ε * C.card ≤ (core I ε γ C c).card := by
  refine (per_count_le hε hC c).trans ?_
  exact_mod_cast card_le_card fun j hj ↦ by
    simp only [core, mem_filter] at hj ⊢
    refine ⟨hj.1, hj.2.trans ?_⟩
    have := per_nonneg hv ε C c
    nlinarith

/-! ### Distances of the center -/

/-- `d(c, S) ≤ per + cost_S(core_0)/(ε |C|)`: average the triangle inequality over the
core, which has at least `ε |C|` clients. -/
theorem dSet_center_le_per (hv : I.Valid) (hε : 0 < ε) (hε' : ε ≤ 1) {C : Finset (Fin I.n)}
    (hC : C.Nonempty) (c : Fin I.m) (S : Finset (Fin I.m)) :
    I.dSet (.inr c) S ≤ per I ε C c + I.costOn S (core I ε 0 C c) / (ε * C.card) := by
  have hK := card_core_ge hv hε' le_rfl hC c (γ := 0)
  have hεC : 0 < ε * C.card := mul_pos hε (by exact_mod_cast hC.card_pos)
  have hKpos : (0 : ℝ) < (core I ε 0 C c).card := hεC.trans_le hK
  have hcost := Instance.costOn_nonneg hv S (core I ε 0 C c)
  have hsum : ((core I ε 0 C c).card : ℝ) * I.dSet (.inr c) S ≤
      (core I ε 0 C c).card * per I ε C c + I.costOn S (core I ε 0 C c) := by
    have h : ∀ j ∈ core I ε 0 C c, I.dSet (.inr c) S ≤ per I ε C c + I.dSet (.inl j) S := by
      intro j hj
      have h1 := Instance.dSet_triangle hv (.inr c) (.inl j) S
      have h2 := (mem_filter.1 hj).2
      rw [Instance.dd_comm hv] at h1
      linarith
    calc ((core I ε 0 C c).card : ℝ) * I.dSet (.inr c) S
        = ∑ j ∈ core I ε 0 C c, I.dSet (.inr c) S := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ core I ε 0 C c, (per I ε C c + I.dSet (.inl j) S) := sum_le_sum h
      _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]; rfl
  have h1 : I.dSet (.inr c) S ≤ per I ε C c + I.costOn S (core I ε 0 C c) /
      (core I ε 0 C c).card := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hKpos]
    linarith
  have h2 : I.costOn S (core I ε 0 C c) / (core I ε 0 C c).card ≤
      I.costOn S (core I ε 0 C c) / (ε * C.card) :=
    div_le_div_of_nonneg_left hcost hεC hK
  linarith

/-- `|C| d(c, S) ≤ ∑_{j ∈ C} d(j, c) + cost_S(C)`. -/
theorem card_mul_dSet_le (hv : I.Valid) (C : Finset (Fin I.n)) (c : Fin I.m)
    (S : Finset (Fin I.m)) : C.card * I.dSet (.inr c) S ≤ costAt I c C + I.costOn S C := by
  have h : ∀ j ∈ C, I.dSet (.inr c) S ≤ I.dd (.inl j) (.inr c) + I.dSet (.inl j) S := by
    intro j _
    have := Instance.dSet_triangle hv (.inr c) (.inl j) S
    rwa [Instance.dd_comm hv] at this
  calc (C.card : ℝ) * I.dSet (.inr c) S = ∑ j ∈ C, I.dSet (.inr c) S := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ C, (I.dd (.inl j) (.inr c) + I.dSet (.inl j) S) := sum_le_sum h
    _ = costAt I c C + I.costOn S C := by rw [sum_add_distrib]; rfl

end BCFGJPSSV26.Stable


