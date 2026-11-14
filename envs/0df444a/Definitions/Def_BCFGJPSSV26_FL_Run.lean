-- Prove2me | Definitions.Def_BCFGJPSSV26_FL_Run
-- name    : BCFGJPSSV26_FL_Run
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:05:44.395174+00:00
-- url     : https://prove2.me/theorems/4cdf23f5-0913-44c2-b0a9-d91b9c3c8538
-- title:
--   BCFGJPSSV26.FL.Run — Theorem 1.4: the greedy run
-- statement:
--   This is module `BCFGJPSSV26.FL.Run` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The guarantee of the greedy run (`BCFGJPSSV26.FL.runFL_spec`): if `n ≥ 2`, `m ≥ 2`, `f > 0`
--   and a nonempty set `O` has a positive cost, the run is a list of distinct facilities `S` with
--   `cost S + λ f |S| ≤ λ (cost O + f |O|)`.
--
--   * **The scaled space** (`BCFGJPSSV26.FL.scSpace`): `d / t + 1` off the diagonal, a pseudometric
--     with client–facility distances at least `1`. As clients and facilities are distinct points,
--     every set of facilities costs `cost / t + n` there (`BCFGJPSSV26.FL.coreCost_ctxFL`,
--     `BCFGJPSSV26.FL.costF_scSpace`).
--   * **The context** satisfies the hypotheses of `Greedy/Alg/Bridge.lean`
--     (`BCFGJPSSV26.FL.hyp_ctxFL`), so CompleteSolution gives a `0`-valid solution
--     (`BCFGJPSSV26.Greedy.Ctx.complete_sol`) at the scaled opening cost `f̂ = λ (1 - δ) f / t`.
--   * **The robust LMP guarantee** (`BCFGJPSSV26.Greedy.robust_lmp`) applies with slack `η = 0`
--     (validity and solutions do not depend on the slack parameter, `BCFGJPSSV26.FL.sol_eta`):
--     `(1 - δ) connCost + s f̂ ≤ (ρ + 6δ) cost(O) + |O| f̂` for the `s` regular atoms of the solution.
--     Scaled back by `t / (1 - δ)`, with `ρ' = (ρ + 6δ) / (1 - δ)`,
--     `cost S + λ f |S| ≤ ρ' cost O + (ρ' - 1) n t + λ f |O|`. Since `cost O ≥ d_min` and
--     `n t ≤ d_min / 10⁵`, this is at most `λ (cost O + f |O|)` for `δ = 10⁻⁶`
--     (`BCFGJPSSV26.FL.fl_arith`).
--
--   **Contents.** The module is published as a whole: 13 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.FL.fl_arith`, `BCFGJPSSV26.FL.runFL_spec`, `BCFGJPSSV26.FL.sol_eta` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_FL_Run`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Run.lean

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.FL.Run` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Theorem 1.4: the greedy run

The guarantee of the greedy run (`BCFGJPSSV26.FL.runFL_spec`): if `n ≥ 2`, `m ≥ 2`, `f > 0`
and a nonempty set `O` has a positive cost, the run is a list of distinct facilities `S` with
`cost S + λ f |S| ≤ λ (cost O + f |O|)`.

* **The scaled space** (`BCFGJPSSV26.FL.scSpace`): `d / t + 1` off the diagonal, a pseudometric
  with client–facility distances at least `1`. As clients and facilities are distinct points,
  every set of facilities costs `cost / t + n` there (`BCFGJPSSV26.FL.coreCost_ctxFL`,
  `BCFGJPSSV26.FL.costF_scSpace`).
* **The context** satisfies the hypotheses of `Greedy/Alg/Bridge.lean`
  (`BCFGJPSSV26.FL.hyp_ctxFL`), so CompleteSolution gives a `0`-valid solution
  (`BCFGJPSSV26.Greedy.Ctx.complete_sol`) at the scaled opening cost `f̂ = λ (1 - δ) f / t`.
* **The robust LMP guarantee** (`BCFGJPSSV26.Greedy.robust_lmp`) applies with slack `η = 0`
  (validity and solutions do not depend on the slack parameter, `BCFGJPSSV26.FL.sol_eta`):
  `(1 - δ) connCost + s f̂ ≤ (ρ + 6δ) cost(O) + |O| f̂` for the `s` regular atoms of the solution.
  Scaled back by `t / (1 - δ)`, with `ρ' = (ρ + 6δ) / (1 - δ)`,
  `cost S + λ f |S| ≤ ρ' cost O + (ρ' - 1) n t + λ f |O|`. Since `cost O ≥ d_min` and
  `n t ≤ d_min / 10⁵`, this is at most `λ (cost O + f |O|)` for `δ = 10⁻⁶`
  (`BCFGJPSSV26.FL.fl_arith`).
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-! ### The scaled space -/

/-- **The scaled pseudometric**: `d / t + 1` off the diagonal. -/
def scSpace (I : Instance) (hI : I.Valid) (t : ℚ) (ht : 0 < t) : Space I.n I.m where
  D a b := if a = b then 0 else I.d a b / t + 1
  nonneg a b := by
    split_ifs
    · exact le_rfl
    · have := div_nonneg (hI.nonneg a b) ht.le
      linarith
  self a := by simp
  comm a b := by
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), hI.comm]
  triangle a b c := by
    have hnn : ∀ a b, 0 ≤ (if a = b then 0 else I.d a b / t + 1) := fun a b ↦ by
      split_ifs
      · exact le_rfl
      · have := div_nonneg (hI.nonneg a b) ht.le
        linarith
    by_cases hac : a = c
    · rw [if_pos hac]
      exact add_nonneg (hnn a b) (hnn b c)
    by_cases hab : a = b
    · subst hab
      simp
    by_cases hbc : b = c
    · subst hbc
      simp
    rw [if_neg hac, if_neg hab, if_neg hbc]
    have h : I.d a c / t ≤ I.d a b / t + I.d b c / t := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (hI.triangle a b c) ht.le
    linarith

/-- The scaled client–facility distances. -/
theorem scSpace_d {hI : I.Valid} {t : ℚ} {ht : 0 < t} (j : Fin I.n) (i : Fin I.m) :
    (scSpace I hI t ht).d j i = I.d (.inl j) (.inr i) / t + 1 := by
  simp [Space.d, scSpace]

/-- The entries of the scaled table, `0` outside it. -/
theorem stabFL_getD (x : Raw) (f : ℚ) (j i : ℕ) :
    ((stabFL x f).getD j []).getD i 0 =
      if j < x.n ∧ i < x.m then x.fdist j i / tFL x f + 1 else 0 := by
  by_cases hj : j < x.n
  · by_cases hi : i < x.m
    · rw [if_pos ⟨hj, hi⟩]
      simp [stabFL, List.getD_eq_getElem?_getD, hj, hi]
    · rw [if_neg fun h ↦ hi h.2]
      simp [stabFL, List.getD_eq_getElem?_getD, hj, hi]
  · rw [if_neg fun h ↦ hj h.1]
    simp [stabFL, List.getD_eq_getElem?_getD, hj]

theorem stabFL_entry (f : ℚ) (j : Fin I.n) (i : Fin I.m) :
    ((stabFL (toRaw I) f).getD j []).getD i 0 = I.d (.inl j) (.inr i) / tFL (toRaw I) f + 1 := by
  rw [stabFL_getD, if_pos ⟨j.2, i.2⟩, ← Raw.fdist_toRaw (.inl j) i]
  rfl

/-! ### The least positive distance -/

theorem mem_guesses_toRaw {j : Fin I.n} {i : Fin I.m} (h : 0 < I.d (.inl j) (.inr i)) :
    I.d (.inl j) (.inr i) ∈ guesses (toRaw I) := by
  unfold guesses
  rw [List.mem_filter, decide_eq_true_iff]
  refine ⟨List.mem_flatMap.2 ⟨j, by simp, List.mem_map.2 ⟨i, by simp, ?_⟩⟩, h⟩
  exact Raw.fdist_toRaw (.inl j) i

theorem pos_of_mem_guesses {x : Raw} {q : ℚ} (h : q ∈ guesses x) : 0 < q := by
  unfold guesses at h
  exact of_decide_eq_true (List.mem_filter.1 h).2

/-- **The least positive distance** is positive and at most every positive cost. -/
theorem dminFL_spec (hI : I.Valid) {O : Finset (Fin I.m)} (hO : O.Nonempty)
    (h : 0 < ∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i)) :
    0 < dminFL (toRaw I) ∧ dminFL (toRaw I) ≤ ∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i) := by
  obtain ⟨j, -, hj⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ ↦ (0 : ℚ))
    (by simpa using h)
  obtain ⟨i, -, he⟩ := exists_mem_eq_inf' hO fun i ↦ I.d (.inl j) (.inr i)
  have hpos : 0 < I.d (.inl j) (.inr i) := he ▸ hj
  have hmem := mem_guesses_toRaw hpos
  obtain ⟨hm, hle⟩ := Combine.minQ_spec (List.ne_nil_of_mem hmem)
  refine ⟨pos_of_mem_guesses hm, (hle _ hmem).trans ?_⟩
  rw [← he]
  exact single_le_sum (f := fun j ↦ O.inf' hO fun i ↦ I.d (.inl j) (.inr i))
    (fun j _ ↦ le_inf' _ _ fun i _ ↦ hI.nonneg _ _) (mem_univ j)

/-- The cost of a nonempty set, computed exactly. -/
theorem cast_costO {O : Finset (Fin I.m)} (hO : O.Nonempty) :
    ((∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i) : ℚ) : ℝ) = I.cost O := by
  rw [← Instance.costF_eq_cost hO, Instance.costF, Rat.cast_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  obtain ⟨i₀, hi₀, he⟩ := exists_mem_eq_inf' hO fun i ↦ I.d (.inl j) (.inr i)
  refine le_antisymm (Instance.le_dSet hO fun i hi ↦ ?_) ?_
  · unfold Instance.dd
    exact_mod_cast inf'_le (fun i ↦ I.d (.inl j) (.inr i)) hi
  · refine (Instance.dSet_le hi₀ _).trans (le_of_eq ?_)
    unfold Instance.dd
    rw [he]

/-! ### Costs in the scaled space -/

/-- The least of an affine image `g / t + 1` is the affine image of the least. -/
theorem minQ_map_affine {β : Type} {l : List β} (hl : l ≠ []) (g : β → ℚ) {t : ℚ}
    (ht : 0 < t) : Combine.minQ (l.map fun b ↦ g b / t + 1) = Combine.minQ (l.map g) / t + 1 := by
  obtain ⟨h1, h2⟩ := Combine.minQ_spec (l := l.map g) (by simpa using hl)
  obtain ⟨h3, h4⟩ := Combine.minQ_spec (l := l.map fun b ↦ g b / t + 1) (by simpa using hl)
  obtain ⟨b1, hb1, e1⟩ := List.mem_map.1 h1
  obtain ⟨b3, hb3, e3⟩ := List.mem_map.1 h3
  refine le_antisymm ?_ ?_
  · have := h4 (g b1 / t + 1) (List.mem_map.2 ⟨b1, hb1, rfl⟩)
    rwa [e1] at this
  · rw [← e3]
    have := div_le_div_of_nonneg_right (h2 _ (List.mem_map.2 ⟨b3, hb3, rfl⟩)) ht.le
    linarith

/-- **The scaled cost of a list of facilities** is `cost / t + n`. -/
theorem coreCost_ctxFL {f : ℚ} {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m)
    (ht : 0 < tFL (toRaw I) f) :
    coreCost ((ctxFL (toRaw I) f).ip.n, (ctxFL (toRaw I) f).ip.m, (ctxFL (toRaw I) f).ip.k,
      (ctxFL (toRaw I) f).tab) S = (toRaw I).cost S / tFL (toRaw I) f + I.n := by
  have hlen : min (distTable I).length I.n = I.n := by simp [distTable]
  unfold coreCost Raw.cost Combine.costQ
  change ((List.range I.n).map fun j ↦ Combine.minQ (S.map fun i ↦
    ((stabFL (toRaw I) f).getD j []).getD i 0)).sum =
      ((List.range (min (distTable I).length I.n)).map fun j ↦ Combine.minQ (S.map fun i ↦
        ((distTable I).getD j []).getD (I.n + i) 0)).sum / tFL (toRaw I) f + I.n
  rw [hlen, Ctx.list_sum_map_range, Ctx.list_sum_map_range, sum_div]
  have hn : (I.n : ℚ) = ∑ _j ∈ range I.n, (1 : ℚ) := by simp
  rw [hn, ← sum_add_distrib]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j < I.n := mem_range.1 hj
  have e : (S.map fun i ↦ ((stabFL (toRaw I) f).getD j []).getD i 0) =
      S.map fun i ↦ (toRaw I).fdist j i / tFL (toRaw I) f + 1 :=
    List.map_congr_left fun i hi ↦ by
      rw [stabFL_getD, if_pos ⟨hj', hm i hi⟩]
  rw [e, minQ_map_affine hS _ ht]
  rfl

/-- **The scaled cost of a nonempty set** is `cost / t + n`. -/
theorem costF_scSpace {hI : I.Valid} {t : ℚ} {ht : 0 < t} {O : Finset (Fin I.m)}
    (hO : O.Nonempty) :
    costF (scSpace I hI t ht).d O = (∑ j, O.inf' hO fun i ↦ I.d (.inl j) (.inr i)) / t + I.n := by
  unfold costF
  simp only [dif_pos hO]
  rw [sum_div]
  have hn : (I.n : ℚ) = ∑ _j : Fin I.n, (1 : ℚ) := by simp
  rw [hn, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  obtain ⟨i₀, hi₀, he⟩ := exists_mem_eq_inf' hO fun i ↦ I.d (.inl j) (.inr i)
  refine le_antisymm ?_ (le_inf' _ _ fun i hi ↦ ?_)
  · refine (inf'_le _ hi₀).trans (le_of_eq ?_)
    rw [scSpace_d, he]
  · rw [scSpace_d]
    have := div_le_div_of_nonneg_right (inf'_le (fun i ↦ I.d (.inl j) (.inr i)) hi) ht.le
    linarith

/-! ### The hypotheses on the context -/

theorem fhatFL_nonneg {x : Raw} {f : ℚ} (hf : 0 ≤ f) (ht : 0 < tFL x f) : 0 ≤ fhatFL x f := by
  unfold fhatFL lmpC δ0
  have := ht.le
  positivity

/-- **The hypotheses of `Greedy/Alg/Bridge.lean` hold** for the context of the greedy run on the
scaled space, when `n ≥ 2` and `m ≥ 2` (the bound `M` is computed from the instance, the other
parameters as in `BCFGJPSSV26.Greedy.hyp_ctx`). -/
theorem hyp_ctxFL (hI : I.Valid) (hn : 2 ≤ I.n) (hm : 2 ≤ I.m) {f : ℚ} (hf : 0 ≤ f)
    (ht : 0 < tFL (toRaw I) f) : (ctxFL (toRaw I) f).Hyp (scSpace I hI _ ht) := by
  have hn' : (2 : ℚ) ≤ (toRaw I).n := by exact_mod_cast hn
  have hfh := fhatFL_nonneg hf ht
  have hdmax : ∀ (j : Fin I.n) (i : Fin I.m), I.d (.inl j) (.inr i) ≤ (toRaw I).dMaxQ := by
    intro j i
    have h1 := Instance.dd_lt_dMax hI (.inl j) (.inr i)
    rw [← Raw.dMaxQ_toRaw] at h1
    unfold Instance.dd at h1
    exact_mod_cast h1.le
  have hdM0 : 0 < (toRaw I).dMaxQ := by
    have := Instance.dMax_pos hI
    rw [← Raw.dMaxQ_toRaw] at this
    exact_mod_cast this
  have hM1 : 1 ≤ MFL (toRaw I) f := by
    unfold MFL
    have := div_nonneg hdM0.le ht.le
    linarith
  have hε : (0 : ℚ) < ε0 := by norm_num [ε0, δ0]
  have hδ : (0 : ℚ) < δ0 := by norm_num [δ0]
  have hη : 0 < ηFL (toRaw I).n := by
    unfold ηFL
    have : (0 : ℚ) < (toRaw I).n := by linarith
    positivity
  have hd1 : ∀ (j : Fin I.n) (i : Fin I.m), 1 ≤ (scSpace I hI _ ht).d j i := fun j i ↦ by
    rw [scSpace_d]
    have := div_nonneg (hI.nonneg (.inl j) (.inr i)) ht.le
    linarith
  have hdM : ∀ (j : Fin I.n) (i : Fin I.m), (scSpace I hI _ ht).d j i ≤ MFL (toRaw I) f :=
    fun j i ↦ by
      rw [scSpace_d]
      unfold MFL
      have := div_le_div_of_nonneg_right (hdmax j i) ht.le
      linarith
  have hn'' : (2 : ℚ) ≤ I.n := hn'
  refine
    { dist_eq := fun j i ↦ ?_
      dist_nonneg := fun j i ↦ ?_
      d1 := hd1
      dM := hdM
      two_le_n := hn
      one_le_k := le_rfl
      k_lt_n := hn
      k_lt_m := hm
      good := ?_
      one_le_M := hM1
      η_eq := rfl
      fmin_eq := rfl
      fmax_eq := rfl
      one_le_R := Nat.le_add_left 1 _
      θ_last := ?_
      K_eq := rfl
      fstep := ?_
      ustep := hyp_ctx_step_le hη
      L_ge := le_rfl }
  · exact (stabFL_entry f j i).trans (scSpace_d j i).symm
  · change 0 ≤ ((stabFL (toRaw I) f).getD j []).getD i 0
    rw [stabFL_getD]
    split_ifs with h
    · obtain ⟨hj, hi⟩ := h
      rw [show (toRaw I).fdist j i = I.d (.inl ⟨j, hj⟩) (.inr ⟨i, hi⟩) from
        Raw.fdist_toRaw (.inl ⟨j, hj⟩) ⟨i, hi⟩]
      have := div_nonneg (hI.nonneg (.inl ⟨j, hj⟩) (.inr ⟨i, hi⟩)) ht.le
      linarith
    · exact le_rfl
  · refine ⟨hδ, show δ0 ≤ 1 / 100 by norm_num [δ0], hε, le_rfl, hη.le, ?_, le_rfl⟩
    change ((toRaw I).n : ℚ) * ηFL (toRaw I).n ≤ δ0 * ε0 / 10
    have h1 := eta_bound (n := ((toRaw I).n : ℚ)) (s := 1) (δ := δ0) (by linarith) (by linarith)
    unfold ηFL
    rw [one_mul] at h1
    rw [show δ0 * ε0 / 10 = δ0 ^ 2 / 100 by unfold ε0; ring]
    exact h1
  · change 4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f + γ * MFL (toRaw I) f ≤
      (1 + ε0 ^ 2) ^ (RFL (toRaw I) f - 1)
    have hR : RFL (toRaw I) f - 1 =
        ⌈1 / ε0 ^ 2⌉₊ * Nat.clog 2 ⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ := by
      simp [RFL]
    rw [hR]
    refine le_trans ?_ (hyp_ctx_bernoulli hε _)
    have h1 : 5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f ≤
        ⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ := Nat.le_ceil _
    have h2 : (⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ : ℚ) ≤
        2 ^ Nat.clog 2 ⌈5 * ((toRaw I).n : ℚ) * MFL (toRaw I) f⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    have h3 : γ * MFL (toRaw I) f ≤ (toRaw I).n * MFL (toRaw I) f :=
      mul_le_mul_of_nonneg_right (by norm_num [γ]; linarith) (by linarith)
    linarith
  · change (4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f - δ0) / 2 ^ Nat.clog 2
      ⌈4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f / ηFL (toRaw I).n⌉₊ ≤ ηFL (toRaw I).n
    refine le_trans ?_ (hyp_ctx_step_le (A := 4 * ((toRaw I).n : ℚ) * MFL (toRaw I) f) hη)
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ### The robust LMP guarantee with slack `0` -/

end BCFGJPSSV26.FL


