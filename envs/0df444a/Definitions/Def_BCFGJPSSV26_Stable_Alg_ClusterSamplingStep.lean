-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep
-- name    : BCFGJPSSV26_Stable_Alg_ClusterSamplingStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:12:50.206684+00:00
-- url     : https://prove2.me/theorems/d70efd2b-a77a-4102-9f5a-371c2f85f456
-- title:
--   BCFGJPSSV26.Stable.Alg.ClusterSamplingStep — The analysis of the cluster sampling: one step
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.ClusterSamplingStep` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Every good chunk keeps the invariant (`BCFGJPSSV26.Stable.KSData.inv_step`), mode by mode, along
--   the case analysis of the proof of the cluster-sampling theorem [BCFGJPSSV26b, Section 4.7].
--
--   **Contents.** The module is published as a whole: 42 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.KSData.inv_step` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingStep.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.ClusterSamplingStep` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The analysis of the cluster sampling: one step

Every good chunk keeps the invariant (`BCFGJPSSV26.Stable.KSData.inv_step`), mode by mode, along
the case analysis of the proof of the cluster-sampling theorem [BCFGJPSSV26b, Section 4.7].
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

theorem nodup_append_singleton {α : Type*} {l : List α} {a : α} :
    (l ++ [a]).Nodup ↔ a ∉ l ∧ l.Nodup := by
  rw [← List.concat_eq_append, List.nodup_concat]

/-! ### The radii of the dummies -/

/-- Two grid points `x < x'` differ by at least `r₀/N⁴`. -/
theorem grid_sub_ge {N : ℕ} (hN : 1 ≤ N) {r₀ : ℚ} (hr : 0 ≤ r₀) {x x' : ℕ} (h : x < x') :
    r₀ / (N : ℚ) ^ 4 ≤ grid N r₀ x' - grid N r₀ x := by
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hq : (1 : ℚ) ≤ ((N : ℚ) + 1) / N := by rw [le_div_iff₀ (by linarith)]; linarith
  have h1 : (((N : ℚ) + 1) / N) ^ (x + 1) ≤ (((N : ℚ) + 1) / N) ^ x' := pow_le_pow_right₀ hq h
  have h2 : (1 : ℚ) ≤ (((N : ℚ) + 1) / N) ^ x := one_le_pow₀ hq
  have h3 : (((N : ℚ) + 1) / N) ^ (x + 1) - (((N : ℚ) + 1) / N) ^ x =
      (((N : ℚ) + 1) / N) ^ x * (1 / N) := by
    rw [pow_succ]
    field_simp
    ring
  have h4 : 1 / (N : ℚ) ≤ (((N : ℚ) + 1) / N) ^ x' - (((N : ℚ) + 1) / N) ^ x := by
    have : 1 / (N : ℚ) ≤ (((N : ℚ) + 1) / N) ^ x * (1 / N) :=
      le_mul_of_one_le_left (by positivity) h2
    linarith
  unfold grid
  have h5 : r₀ / (N : ℚ) ^ 4 = r₀ / (N : ℚ) ^ 3 * (1 / N) := by
    field_simp
  rw [h5, ← mul_sub]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **The dummies of one leader are distinct**: `ksRad` is injective in the index `t ≤ 2 s`. -/
theorem ksRad_inj {N s : ℕ} (hN : 1 ≤ N) {r₀ : ℚ} (hr : 0 < r₀) {x x' t t' : ℕ}
    (ht : t ≤ 2 * s) (ht' : t' ≤ 2 * s) (h : ksRad N s r₀ x t = ksRad N s r₀ x' t') :
    t = t' := by
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℚ) < (N : ℚ) ^ 4 * (2 * s + 2) := by positivity
  unfold ksRad at h
  -- the shifts differ by less than `r₀/N⁴`
  have hsh : ∀ {a b : ℕ}, a ≤ 2 * s → b ≤ 2 * s →
      r₀ * a / ((N : ℚ) ^ 4 * (2 * s + 2)) - r₀ * b / ((N : ℚ) ^ 4 * (2 * s + 2)) <
        r₀ / (N : ℚ) ^ 4 := by
    intro a b ha hb
    have ha' : (a : ℚ) ≤ 2 * s := by exact_mod_cast ha
    have hb' : (0 : ℚ) ≤ b := Nat.cast_nonneg b
    rw [← sub_div, ← mul_sub, div_lt_div_iff₀ hc (by positivity)]
    have : r₀ * (a - b) * N ^ 4 ≤ r₀ * (2 * s) * N ^ 4 := by
      have : r₀ * (a - b) ≤ r₀ * (2 * s) := mul_le_mul_of_nonneg_left (by linarith) hr.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    nlinarith [pow_pos (by linarith : (0 : ℚ) < N) 4]
  rcases lt_trichotomy x x' with hx | rfl | hx
  · have := grid_sub_ge hN hr.le hx
    have := hsh ht ht'
    linarith
  · have h' : r₀ * t / ((N : ℚ) ^ 4 * (2 * s + 2)) = r₀ * t' / ((N : ℚ) ^ 4 * (2 * s + 2)) := by
      linarith
    rw [div_left_inj' hc.ne', mul_right_inj' hr.ne'] at h'
    exact_mod_cast h'
  · have := grid_sub_ge hN hr.le hx
    have := hsh ht' ht
    linarith

/-- **The radius of a new dummy**: between the distance `d` and `(1 + κ + 6ε) per`. -/
theorem ksRad_bounds {N s : ℕ} (hN : 201 ≤ N) {r₀ : ℚ} (hr : 0 ≤ r₀) {x t : ℕ}
    (ht : t ≤ 2 * s) {d p κ : ℝ} (hp : 0 ≤ p) (hg1 : d ≤ (grid N r₀ x : ℝ))
    (hg2 : (grid N r₀ x : ℝ) ≤ (1 + 1 / (N : ℝ)) * d) (hd : d ≤ (1 + κ + 3 * (1 / N)) * p)
    (hκ : κ ≤ 23 / 65) (hr15 : (r₀ : ℝ) ≤ 15 * p) :
    d ≤ (ksRad N s r₀ x t : ℝ) ∧ (ksRad N s r₀ x t : ℝ) ≤ (1 + κ + 6 * (1 / N)) * p := by
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hr' : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr
  have ht' : (t : ℝ) ≤ 2 * s := by exact_mod_cast ht
  have hc : (0 : ℝ) < (N : ℝ) ^ 4 * (2 * s + 2) := by positivity
  have hsh0 : 0 ≤ (r₀ : ℝ) * t / ((N : ℝ) ^ 4 * (2 * s + 2)) := by positivity
  have hsh1 : (r₀ : ℝ) * t / ((N : ℝ) ^ 4 * (2 * s + 2)) ≤ r₀ / (N : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hc (by positivity)]
    have : (r₀ : ℝ) * t ≤ r₀ * (2 * s + 2) := mul_le_mul_of_nonneg_left (by linarith) hr'
    nlinarith [pow_pos hNpos 4]
  have hcast : (ksRad N s r₀ x t : ℝ) =
      (grid N r₀ x : ℝ) + (r₀ : ℝ) * t / ((N : ℝ) ^ 4 * (2 * s + 2)) := by
    unfold ksRad
    push_cast
    ring
  rw [hcast]
  refine ⟨by linarith, ?_⟩
  set e : ℝ := 1 / N with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 201 := by rw [he]; exact one_div_le_one_div_of_le (by norm_num) hN'
  have hr4 : (r₀ : ℝ) / (N : ℝ) ^ 4 = r₀ * e ^ 4 := by rw [he]; field_simp
  have h1 : (grid N r₀ x : ℝ) ≤ (1 + e) * ((1 + κ + 3 * e) * p) :=
    hg2.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have h2 : (r₀ : ℝ) * e ^ 4 ≤ 15 * p * e ^ 4 := mul_le_mul_of_nonneg_right hr15 (by positivity)
  have h3 : (1 + e) * ((1 + κ + 3 * e) * p) + 15 * p * e ^ 4 ≤ (1 + κ + 6 * e) * p := by
    have : e * (1 + κ + 3 * e) + 15 * e ^ 4 ≤ 3 * e := by
      have : e ^ 4 ≤ e * (1 / 201) ^ 3 := by
        rw [show e ^ 4 = e * e ^ 3 by ring]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0.le he1 3) he0.le
      nlinarith
    nlinarith
  linarith

variable (K : KSData)

/-! ### Monotonicity -/

theorem cc_zero_mono {del del' : List ℕ} {D D' : List DumQ} (h : K.cc 0 del D)
    (hD : K.OB D' ⊆ K.OB D) : K.cc 0 del' D' := by
  classical
  have hv := K.H.valid
  unfold cc GoodL wt at *
  simp only [↓reduceIte] at *
  refine lt_of_le_of_lt (sum_le_sum_of_subset_of_nonneg
    (biUnion_subset_biUnion_of_subset_left _ hD) fun c _ _ ↦ Instance.costOn_nonneg hv _ _) h

theorem GamSub.mono {K : KSData} {del : List ℕ} {D D' : List DumQ} (h : K.GamSub del D)
    (hD : K.OB D' ⊆ K.OB D) : K.GamSub del D' := by
  classical
  exact fun c hc ↦ h c (biUnion_subset_biUnion_of_subset_left _ hD hc)

theorem Base.del_append {K : KSData} {del : List ℕ} {D : List DumQ} (hb : K.Base del D) {i : ℕ}
    (hi : i < K.X.I.m) (hS : K.fac i ∈ K.X.S \ K.X.LSX K.w₁.OL) (hnd : i ∉ del) :
    K.Base (del ++ [i]) D where
  dums_nodup := hb.dums_nodup
  card := hb.card
  rad := hb.rad
  del_nodup := nodup_append_singleton.2 ⟨hnd, hb.del_nodup⟩
  del_sub := fun i' hi' ↦ by
    rcases List.mem_append.1 hi' with hi' | hi'
    · exact hb.del_sub i' hi'
    · rw [List.mem_singleton.1 hi']
      exact ⟨hi, hS⟩

theorem Base.dums_append {K : KSData} {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    {d : DumQ} {c : Fin K.X.I.m} (hp : K.pick (K.matched D) d.1 = some c) (hnd : d ∉ D)
    (hrad : K.X.I.dd (.inr c) (K.toDum d).leader ≤ (K.toDum d).radius ∧
      (K.toDum d).radius ≤ (1 + K.X.kap c + 6 * K.X.ε) * K.X.per c) :
    K.Base del (D ++ [d]) := by
  obtain ⟨-, hcM, -⟩ := K.pick_some hp
  obtain ⟨e1, e2⟩ := K.ghost_append_some hp
  refine ⟨nodup_append_singleton.2 ⟨hnd, hb.dums_nodup⟩, ?_, ?_, hb.del_nodup, hb.del_sub⟩
  · rw [e1, card_insert_of_notMem hcM, hb.card, List.length_append, List.length_singleton]
  · intro c' hc'
    rw [e1] at hc'
    rw [e2]
    rcases mem_insert.1 hc' with rfl | hc'
    · rw [Function.update_self]
      exact hrad
    · have hne : c' ≠ c := fun h ↦ hcM (h ▸ hc')
      rw [Function.update_of_ne hne]
      exact hb.rad c' hc'

/-! ### The steps, mode by mode -/

theorem step_tag0 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 0, l, r₀) u =
      if j = K.X.s then (if ph = 0 then (1, 0, del, D, 0, l, r₀) else (2, 0, del, D, 0, l, r₀))
      else if cbit K.X.b u then (ph, j + 1, del, D, 0, l, r₀)
      else (ph, j, del, D, 1, l, r₀) := by
  dsimp only [step, ksStep]
  rw [if_neg hph]
  rfl

theorem step_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 1, l, r₀) u =
      if K.cand del = [] then (ph, j + 1, del, D, 0, l, r₀)
      else (ph, j, del, D, 2, K.sampled (ph, j, del, D, 1, l, r₀) u, r₀) := by
  dsimp only [step, ksStep]
  rw [if_neg hph]
  rfl

theorem step_tag2 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 2, l, r₀) u =
      if del.length ≤ K.X.s ∧ cbit K.X.b u = true then (ph, j + 1, del ++ [l], D, 0, l, r₀)
      else (ph, j, del, D, 3, l, r₀) := by
  dsimp only [step, ksStep]
  rw [if_neg hph]
  rfl

theorem step_tag3 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 3, l, r₀) u =
      if 2 * K.X.s < D.length + del.length then (ph, j + 1, del, D, 0, l, r₀)
      else if K.LS.filter (fun c ↦ decide (c ∉ del ∧ c ≠ l)) = [] then
        (ph, j + 1, del, D, 0, l, r₀)
      else if cbit K.X.b u then
        (ph, j, del, D, 4, l, (toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l))
      else (ph, j, del ++ [K.nearOther del l], D, 3, l, r₀) := by
  dsimp only [step, ksStep]
  rw [if_neg hph]
  rfl

theorem step_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 4, l, r₀) u =
      if 2 * K.X.s < D.length + del.length then (ph, j + 1, del ++ [l], D, 0, l, r₀)
      else (ph, j, del, D ++ [(K.X.I.n + l,
        ksRad K.X.P.N K.X.s r₀ (cunif (Par.Gr K.X.P.N) u) D.length)], 5, l, r₀) := by
  dsimp only [step, ksStep]
  rw [if_neg hph]
  rfl

theorem step_tag5 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} (hph : ph ≠ 2)
    (u : ℕ) : K.step (ph, j, del, D, 5, l, r₀) u =
      if cbit K.X.b u then (ph, j + 1, del ++ [l], D, 0, l, r₀)
      else (ph, j, del, D, 4, l, r₀) := by
  dsimp only [step, ksStep]
  rw [if_neg hph]
  rfl

/-! ### Building the invariant -/

theorem Inv.mk_start {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j ≤ K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hs : K.cc ph del D ∨ j ≤ del.length) :
    K.Inv (ph, j, del, D, 0, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj
  j_lt := fun h ↦ absurd rfl h
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ _ ↦ hs
  prog := fun _ h ↦ absurd rfl h
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ h ↦ absurd h (by simp)
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_phase2 {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h0 : K.cc 0 del D) (h1 : K.cc 1 del D) : K.Inv (2, 0, del, D, 0, l, r₀) where
  base := hb
  phase_le := le_rfl
  j_le := Nat.zero_le _
  j_lt := fun h ↦ absurd rfl h
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := fun _ ↦ h0
  ph2 := fun _ ↦ ⟨h1, rfl⟩
  start := fun h ↦ absurd h (by simp)
  prog := fun h ↦ absurd h (by simp)
  sample := fun h ↦ absurd h (by simp)
  radd := fun h ↦ absurd h (by simp)
  mid := fun h ↦ absurd h (by simp)
  dg := fun h ↦ absurd h (by simp)
  rg := fun h ↦ absurd h (by simp)
  rad0 := fun h ↦ absurd h (by simp)

theorem Inv.mk_sample {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hns : ¬ K.cc ph del D) :
    K.Inv (ph, j, del, D, 1, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ _ ↦ hns
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ h ↦ absurd h (by simp)
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_radd {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i) (hg : K.GamSub del D)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hl : l ∈ K.LS) (hld : l ∉ del)
    (hgood : K.fac l ∈ K.GoodL ph del D) :
    K.Inv (ph, j, del, D, 2, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun _ ↦ hg
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ _ ↦ ⟨hl, hld, hgood⟩
  mid := fun _ h ↦ absurd h (by simp)
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_dg {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i)
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hm : K.Mid del D l)
    (hdg : K.DGc del D l) :
    K.Inv (ph, j, del, D, 3, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ .inl (hlead d hd)
  gam := fun h ↦ absurd h (by simp)
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ _ ↦ hm
  dg := fun _ _ ↦ hdg
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ h ↦ absurd h (by simp)

theorem Inv.mk_rg {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t))
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hm : K.Mid del D l)
    (hrg : K.RGc D l) (hr : K.Rad0 D l r₀) :
    K.Inv (ph, j, del, D, 4, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ (hlead d hd).imp id fun h ↦ ⟨by simp, h⟩
  gam := fun h ↦ absurd h (by simp)
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ _ ↦ hm
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ _ ↦ hrg
  rad0 := fun _ _ ↦ hr

theorem Inv.mk_rgb {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hb : K.Base del D) (hph : ph < 2) (hj : j < K.X.s)
    (hlead : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t))
    (h1 : 1 ≤ ph → K.cc 0 del D) (hp : j ≤ del.length) (hm : K.Mid del D l)
    (hr : K.Rad0 D l r₀) :
    K.Inv (ph, j, del, D, 5, l, r₀) where
  base := hb
  phase_le := by simp only [KSState.phase_mk]; omega
  j_le := hj.le
  j_lt := fun _ ↦ hj
  tag_le := by simp
  leaders := fun d hd ↦ (hlead d hd).imp id fun h ↦ ⟨by simp, h⟩
  gam := fun h ↦ absurd h (by simp)
  ph1 := h1
  ph2 := fun h ↦ by simp only [KSState.phase_mk] at h; omega
  start := fun _ h ↦ absurd h (by simp)
  prog := fun _ _ ↦ hp
  sample := fun _ h ↦ absurd h (by simp)
  radd := fun _ h ↦ absurd h (by simp)
  mid := fun _ _ ↦ hm
  dg := fun _ h ↦ absurd h (by simp)
  rg := fun _ h ↦ absurd h (by simp)
  rad0 := fun _ _ ↦ hr

/-! ### Geometry of satellites -/

theorem mem_Gam {c c' : Fin K.X.I.m} : c' ∈ K.X.Gam c ↔ c' ∈ K.X.S ∧
    K.X.dF c' c ≤ (1 + K.X.kap c + 2 * K.X.ε) * K.X.per c ∧
      ∃ j ∈ K.X.C c, K.X.dist j c' ≤ K.X.ε * K.X.per c := by
  unfold Ctx.Gam
  rw [mem_filter]

theorem mem_GamE {c c' : Fin K.X.I.m} : c' ∈ K.X.GamE c ↔ c' ∈ K.X.S ∧
    K.X.dF c' c ≤ (1 + K.X.kap c + 3 * K.X.ε) * K.X.per c ∧
      ∃ j ∈ K.X.C c, K.X.dist j c' ≤ 2 * K.X.ε * K.X.per c := by
  unfold Ctx.GamE
  rw [mem_filter]

theorem dF_comm (a b : Fin K.X.I.m) : K.X.dF a b = K.X.dF b a :=
  Instance.dd_comm K.H.valid _ _

theorem dF_tri (a b c : Fin K.X.I.m) : K.X.dF a c ≤ K.X.dF a b + K.X.dF b c :=
  Instance.dd_triangle K.H.valid _ _ _

theorem dist_tri (j : Fin K.X.I.n) (b c : Fin K.X.I.m) :
    K.X.dist j c ≤ K.X.dist j b + K.X.dF b c :=
  Instance.dd_triangle K.H.valid _ _ _

theorem eps_le_one : K.X.ε ≤ 1 := by have := K.H.eps_lt; linarith

theorem per_nonneg' (c : Fin K.X.I.m) : 0 ≤ K.X.per c := per_nonneg K.H.valid _ _ _

/-- A center within `ε² per₀` of a satellite of `c₀` is a loose satellite of `c₀`. -/
theorem GamE_of_near {c₀ ℓ c' : Fin K.X.I.m} (hℓ : ℓ ∈ K.X.Gam c₀) (hc' : c' ∈ K.X.S)
    (hd : K.X.dF ℓ c' ≤ K.X.ε ^ 2 * K.X.per c₀) : c' ∈ K.X.GamE c₀ := by
  obtain ⟨-, h1, j, hj, h2⟩ := K.mem_Gam.1 hℓ
  have hp := K.per_nonneg' c₀
  have he := K.H.eps_pos
  have he1 := K.eps_le_one
  have hee : K.X.ε ^ 2 * K.X.per c₀ ≤ K.X.ε * K.X.per c₀ :=
    mul_le_mul_of_nonneg_right (by nlinarith) hp
  refine K.mem_GamE.2 ⟨hc', ?_, j, hj, ?_⟩
  · have := K.dF_tri c' ℓ c₀
    rw [K.dF_comm c' ℓ] at this
    nlinarith
  · have := K.dist_tri j ℓ c'
    nlinarith

/-- A center within `3 ε² per` of a satellite of `c` is a loose satellite of `c`. -/
theorem GamE_of_near' {c ℓ c' : Fin K.X.I.m} (hc' : c' ∈ K.X.Gam c) (hℓ : ℓ ∈ K.X.S)
    (hd : K.X.dF ℓ c' ≤ 3 * K.X.ε ^ 2 * K.X.per c) : ℓ ∈ K.X.GamE c := by
  obtain ⟨-, h1, j, hj, h2⟩ := K.mem_Gam.1 hc'
  have hp := K.per_nonneg' c
  have he := K.H.eps_pos
  have he1 := K.H.eps_lt
  have hee : 3 * K.X.ε ^ 2 * K.X.per c ≤ K.X.ε * K.X.per c :=
    mul_le_mul_of_nonneg_right (by nlinarith) hp
  refine K.mem_GamE.2 ⟨hℓ, ?_, j, hj, ?_⟩
  · have := K.dF_tri ℓ c' c
    nlinarith
  · have := K.dist_tri j c' ℓ
    rw [K.dF_comm c' ℓ] at this
    nlinarith

theorem isFar_of_OB {D : List DumQ} {c : Fin K.X.I.m} (hc : c ∈ K.OB D) : K.X.IsFar c :=
  K.w₁.isFar K.H (mem_sdiff.1 (K.mem_OB.1 hc).1).1

theorem kap_le (c : Fin K.X.I.m) : K.X.kap c ≤ 23 / 65 := (kappa_mem _).2

theorem kap_ge (c : Fin K.X.I.m) : 12 / 65 ≤ K.X.kap c := (kappa_mem _).1

/-- **A kept satellite at the right distance** (from `BCFGJPSSV26.Stable.Hyp.no_dense_cores`). -/
theorem exists_far_sat {c₀ ℓ : Fin K.X.I.m} (hc₀ : K.X.IsFar c₀) (hℓ : ℓ ∈ K.X.Gam c₀) :
    ∃ w ∈ K.X.Gam c₀, K.X.ε * K.X.per c₀ / 2 ≤ K.X.dF ℓ w ∧ K.X.dF ℓ w < 5 * K.X.per c₀ := by
  obtain ⟨c₁, h₁, c₂, h₂, h12⟩ := K.H.no_dense_cores hc₀
  have hp := hc₀.per_pos
  have he := K.H.eps_pos
  have he1 := K.H.eps_lt
  have hk := K.kap_le c₀
  have hup : ∀ w ∈ K.X.Gam c₀, K.X.dF ℓ w < 5 * K.X.per c₀ := by
    intro w hw
    have a1 := (K.mem_Gam.1 hℓ).2.1
    have a2 := (K.mem_Gam.1 hw).2.1
    have := K.dF_tri ℓ c₀ w
    rw [K.dF_comm c₀ w] at this
    nlinarith
  have htri := K.dF_tri c₁ ℓ c₂
  rw [K.dF_comm c₁ ℓ] at htri
  by_cases h : K.X.ε * K.X.per c₀ / 2 ≤ K.X.dF ℓ c₁
  · exact ⟨c₁, h₁, h, hup c₁ h₁⟩
  · exact ⟨c₂, h₂, by linarith, hup c₂ h₂⟩

/-! ### The good chunks, mode by mode -/

theorem good_tag0 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 0, l, r₀) u ↔
      (j = K.X.s ∨ (cbit K.X.b u = true ↔ K.cc ph del D)) := by
  rw [Good, KSState.phase_mk, if_neg hph]
  rfl

theorem good_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 1, l, r₀) u ↔
      K.fac (K.sampled (ph, j, del, D, 1, l, r₀) u) ∈ K.GoodL ph del D := by
  rw [Good, KSState.phase_mk, if_neg hph]
  rfl

theorem good_tag2 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 2, l, r₀) u ↔
      (cbit K.X.b u = true ↔ K.fac l ∉ K.X.GamOf (K.OB D)) := by
  rw [Good, KSState.phase_mk, if_neg hph]
  rfl

theorem good_tag3 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 3, l, r₀) u ↔
      (cbit K.X.b u = true ↔ ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c ∧
        K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ)) := by
  rw [Good, KSState.phase_mk, if_neg hph]
  rfl

theorem good_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 4, l, r₀) u ↔
      ∀ c, K.pick (K.matched D) (K.X.I.n + l) = some c →
        K.X.dF c (K.fac l) ≤ (grid K.X.P.N r₀ (cunif (Par.Gr K.X.P.N) u) : ℝ) ∧
          (grid K.X.P.N r₀ (cunif (Par.Gr K.X.P.N) u) : ℝ) ≤ (1 + K.X.ε) * K.X.dF c (K.fac l) := by
  rw [Good, KSState.phase_mk, if_neg hph]
  rfl

theorem good_tag5 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hph : ph ≠ 2) : K.Good (ph, j, del, D, 5, l, r₀) u ↔
      (cbit K.X.b u = true ↔ ¬ ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c) := by
  rw [Good, KSState.phase_mk, if_neg hph]
  rfl

/-! ### The steps -/

/-- `SAMPLE`: a good center is sampled. -/
theorem inv_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 1, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 1, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 1, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hlead : ∀ d ∈ D, ∃ i ∈ del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hns : ¬ K.cc ph del D := hI.sample hph2 rfl
  rw [K.good_tag1 hph] at hG
  rw [K.step_tag1 hph]
  by_cases hc : K.cand del = []
  · exfalso
    have he : K.LSp del = ∅ := by
      ext c
      rw [LSp, hc]
      simp [Instance.centers]
    exact hns (K.cc_of_empty (subset_empty.1 (he ▸ K.GoodL_subset hg)))
  · rw [if_neg hc]
    have hmem := getD_wsample_mem (toRaw K.X.I) K.LS K.Λ₁ ph del D hc K.X.b u
    have hmem' := List.mem_filter.1 hmem
    exact Inv.mk_radd K hb hph2 hj hlead hg h1 hp hmem'.1 (of_decide_eq_true hmem'.2) hG

/-- `RGB`: stop (and delete `ℓ`) exactly when `ℓ` leads no unmatched cluster any more; then every
cluster of `O_B` that lost a satellite in this iteration was matched. -/
theorem inv_tag5 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ} {u : ℕ}
    (hI : K.Inv (ph, j, del, D, 5, l, r₀)) (hph : ph ≠ 2)
    (hG : K.Good (ph, j, del, D, 5, l, r₀) u) : K.Inv (K.step (ph, j, del, D, 5, l, r₀) u) := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have h1 : 1 ≤ ph → K.cc 0 del D := hI.ph1
  have hj : j < K.X.s := hI.j_lt (by simp)
  have hp : j ≤ del.length := hI.prog hph2 (by simp)
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hr : K.Rad0 D l r₀ := hI.rad0 hph2 (by simp)
  have hleadI : ∀ d ∈ D, (∃ i ∈ del, d.1 = K.X.I.n + i) ∨ (4 ≤ 5 ∧ d.1 = K.X.I.n + l ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < D.length, d.2 = ksRad K.X.P.N K.X.s r₀ x t) := hI.leaders
  rw [K.good_tag5 hph] at hG
  rw [K.step_tag5 hph]
  by_cases hc : cbit K.X.b u = true
  · rw [if_pos hc]
    have hno := hG.1 hc
    have hb' := hb.del_append hm.lt hm.mem hm.nmem
    refine Inv.mk_start K hb' hph2 (by omega) ?_ ?_
      (fun h ↦ K.cc_zero_mono (h1 h) subset_rfl) (.inr (by simp; omega))
    · intro d hd
      rcases hleadI d hd with ⟨i, hi, he⟩ | ⟨-, he, -⟩
      · exact ⟨i, List.mem_append_left _ hi, he⟩
      · exact ⟨l, List.mem_append_right _ (List.mem_singleton_self l), he⟩
    · intro c hc' hcd
      obtain ⟨c₁, hc₁, hcc₁⟩ := mem_biUnion.1 hc'
      rcases List.mem_append.1 hcd with h | h
      · exact hno ⟨c₁, hc₁, hm.lose c₁ hc₁ ⟨c, hcc₁, h⟩⟩
      · have : c = K.fac l := by rw [← List.mem_singleton.1 h, K.fac_fin]
        rw [this] at hcc₁
        exact hno ⟨c₁, hc₁, K.X.Gam_subset_GamE K.H.valid c₁ hcc₁⟩
  · rw [if_neg hc]
    have hex : ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c := by
      by_contra h
      exact hc (hG.2 h)
    exact Inv.mk_rg K hb hph2 hj (fun d hd ↦ (hleadI d hd).imp id fun h ↦ h.2) h1 hp hm hex hr

end KSData

end BCFGJPSSV26.Stable


