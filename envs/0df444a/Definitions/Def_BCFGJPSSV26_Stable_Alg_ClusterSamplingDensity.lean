-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
-- name    : BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:14:45.648459+00:00
-- url     : https://prove2.me/theorems/be00df10-62e2-442a-8be4-a70763b0be72
-- title:
--   BCFGJPSSV26.Stable.Alg.ClusterSamplingDensity — The analysis of the cluster sampling: densities
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.ClusterSamplingDensity` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   From every invariant state, at least a fraction `q₂ = 1/(12 N³)` of the chunks is good
--   (`BCFGJPSSV26.Stable.KSData.card_good`): fair bits give `1/2`; the sampling step gives
--   `ε³/6 - m/2^b ≥ ε³/12` (the good centers weigh at least `ε³ opt` out of at most `6 opt`); the
--   radius step gives `1/(2 G_r)`, a grid point being in the right interval.
--
--   **Contents.** The module is published as a whole: 10 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.KSData.card_good` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingDensity.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.ClusterSamplingDensity` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The analysis of the cluster sampling: densities

From every invariant state, at least a fraction `q₂ = 1/(12 N³)` of the chunks is good
(`BCFGJPSSV26.Stable.KSData.card_good`): fair bits give `1/2`; the sampling step gives
`ε³/6 - m/2^b ≥ ε³/12` (the good centers weigh at least `ε³ opt` out of at most `6 opt`); the
radius step gives `1/(2 G_r)`, a grid point being in the right interval.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

theorem one_le_b : 1 ≤ K.X.b := by
  have := K.X.P.hN
  unfold Ctx.b Par.bits
  omega

theorem N_pos' : (0 : ℝ) < K.X.P.N := K.X.P.N_pos'

theorem q₂_eq : K.X.P.q₂ = 1 / (12 * (K.X.P.N : ℝ) ^ 3) := rfl

theorem q₂_nonneg : 0 ≤ K.X.P.q₂ := by
  rw [q₂_eq]
  have := K.N_pos'
  positivity

theorem q₂_le_half : K.X.P.q₂ ≤ 1 / 2 := by
  rw [q₂_eq]
  have : (201 : ℝ) ≤ K.X.P.N := K.X.P.N_ge
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 201) this 3]

theorem card_fin_b : (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) = 2 ^ K.X.b := by
  rw [Fintype.card_fin]
  push_cast
  rfl

/-- Fair bits: half of the chunks. -/
theorem card_bit_iff (P : Prop) [Decidable P] :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
        (cbit K.X.b u = true ↔ P)).card := by
  have h := card_cbit K.one_le_b (decide P)
  have he : ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
      (cbit K.X.b u = true ↔ P)) =
      (univ.filter fun u : Fin (2 ^ K.X.b) ↦ cbit K.X.b u = decide P) := by
    ext u
    simp only [mem_filter, mem_univ, true_and]
    cases cbit K.X.b u <;> by_cases hP : P <;> simp [hP]
  rw [he, h, K.card_fin_b]
  have h2 : (2 : ℝ) ^ K.X.b = 2 * 2 ^ (K.X.b - 1) := by
    rw [← pow_succ']
    congr 1
    have := K.one_le_b
    omega
  have hq := K.q₂_le_half
  push_cast
  rw [h2]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (K.X.b - 1)]

theorem card_mono {P Q : Fin (2 ^ K.X.b) → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ u, P u → Q u) :
    (((univ : Finset (Fin (2 ^ K.X.b))).filter P).card : ℝ) ≤ (univ.filter Q).card := by
  exact_mod_cast card_le_card fun u hu ↦ mem_filter.2 ⟨mem_univ _, h u (mem_filter.1 hu).2⟩

theorem card_all (P : Fin (2 ^ K.X.b) → Prop) [DecidablePred P] (hP : ∀ u, P u) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter P).card := by
  rw [filter_true_of_mem fun u _ ↦ hP u, card_univ]
  have hq := K.q₂_le_half
  have : (0 : ℝ) ≤ Fintype.card (Fin (2 ^ K.X.b)) := Nat.cast_nonneg _
  nlinarith

open Classical in
/-- **Density of the radius step.** -/
theorem card_good_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hI : K.Inv (ph, j, del, D, 4, l, r₀)) (hph : ph ≠ 2) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
        K.Good (ph, j, del, D, 4, l, r₀) u).card := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hr : K.Rad0 D l r₀ := hI.rad0 hph2 (by simp)
  rcases hpick : K.pick (K.matched D) (K.X.I.n + l) with _ | c
  · refine K.card_all _ fun u ↦ (K.good_tag4 hph).2 fun c h ↦ ?_
    rw [hpick] at h
    exact absurd h (by simp)
  obtain ⟨hcO, hcM, hcand⟩ := K.pick_some hpick
  have hcOB : c ∈ K.OB D := K.mem_OB.2 ⟨hcO, hcM⟩
  have hlc : K.fac l ∈ K.X.GamE c := by
    rw [← K.fac_val hm.lt] at hcand
    exact K.cand_iff.1 hcand
  have hfar := K.isFar_of_OB hcOB
  have hp := hfar.per_pos
  have hN := K.N_pos'
  have hN' : (201 : ℝ) ≤ K.X.P.N := K.X.P.N_ge
  have heps : K.X.ε = 1 / (K.X.P.N : ℝ) := rfl
  have he := K.H.eps_pos
  have he1 : K.X.ε ≤ 1 / 201 := K.X.P.eps_le
  obtain ⟨hr0, hr1, hr2⟩ : 0 < (r₀ : ℝ) ∧ K.X.ε ^ 2 * K.X.per c / 3 ≤ r₀ ∧
      (r₀ : ℝ) ≤ 15 * K.X.per c := ⟨hr.1, hr.2 c hcOB hlc⟩
  set d := K.X.dF c (K.fac l) with hd
  -- `d` is at least `η per/(1 + 2ε)`, at most `(1 + κ + 3ε) per`
  have hdlo : eta * (K.X.per c / (1 + 2 * K.X.ε)) < d := by
    have h1 := hfar.far
    have h2 := hfar.avg_ge
    have h3 : 0 ≤ K.X.avgS c := by
      unfold Ctx.avgS
      exact div_nonneg (Instance.costOn_nonneg K.H.valid _ _) (Nat.cast_nonneg _)
    have h4 : K.X.dOS c ≤ d := Instance.dSet_le (mem_sdiff.1 hm.mem).1 _
    have : eta * (K.X.per c / (1 + 2 * K.X.ε)) ≤ eta * K.X.avgO c :=
      mul_le_mul_of_nonneg_left h2 (by unfold eta; norm_num)
    nlinarith
  have hdhi : d ≤ 2 * K.X.per c := by
    have h1 := (K.mem_GamE.1 hlc).2.1
    rw [K.dF_comm] at h1
    have := K.kap_le c
    nlinarith
  have hlo : (r₀ : ℝ) / (K.X.P.N : ℝ) ^ 3 ≤ d := by
    have h1 : (r₀ : ℝ) / (K.X.P.N : ℝ) ^ 3 = (r₀ : ℝ) * K.X.ε ^ 3 := by rw [heps]; field_simp
    rw [h1]
    have h2 : (r₀ : ℝ) * K.X.ε ^ 3 ≤ 15 * K.X.per c * K.X.ε ^ 3 :=
      mul_le_mul_of_nonneg_right hr2 (by positivity)
    have h3 : 15 * K.X.ε ^ 3 ≤ eta / (1 + 2 * K.X.ε) := by
      rw [le_div_iff₀ (by positivity)]
      unfold eta
      have : K.X.ε ^ 3 ≤ (1 / 201) ^ 3 := pow_le_pow_left₀ he.le he1 3
      nlinarith
    have h4 : 15 * K.X.per c * K.X.ε ^ 3 ≤ eta * (K.X.per c / (1 + 2 * K.X.ε)) :=
      calc 15 * K.X.per c * K.X.ε ^ 3 = K.X.per c * (15 * K.X.ε ^ 3) := by ring
        _ ≤ K.X.per c * (eta / (1 + 2 * K.X.ε)) := mul_le_mul_of_nonneg_left h3 hp.le
        _ = eta * (K.X.per c / (1 + 2 * K.X.ε)) := by ring
    linarith
  have hhi : (1 + 1 / (K.X.P.N : ℝ)) * d ≤ (K.X.P.N : ℝ) ^ 7 * r₀ := by
    have h1 : K.X.per c ≤ 3 * (K.X.P.N : ℝ) ^ 2 * r₀ := by
      have : K.X.ε ^ 2 * K.X.per c / 3 = K.X.per c / (3 * (K.X.P.N : ℝ) ^ 2) := by
        rw [heps]; field_simp
      rw [this, div_le_iff₀ (by positivity)] at hr1
      linarith
    have h2 : (1 + 1 / (K.X.P.N : ℝ)) ≤ 2 := by
      have : 1 / (K.X.P.N : ℝ) ≤ 1 := by rw [div_le_one hN]; linarith
      linarith
    have h3 : 12 * (K.X.P.N : ℝ) ^ 2 ≤ (K.X.P.N : ℝ) ^ 7 := by
      have : (12 : ℝ) ≤ (K.X.P.N : ℝ) ^ 5 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 201) hN' 5
        linarith
      nlinarith [pow_pos hN 2]
    have hd0 : 0 ≤ d := Instance.dd_nonneg K.H.valid _ _
    calc (1 + 1 / (K.X.P.N : ℝ)) * d ≤ 2 * (2 * K.X.per c) :=
          mul_le_mul h2 hdhi hd0 (by norm_num)
      _ ≤ 12 * (K.X.P.N : ℝ) ^ 2 * r₀ := by nlinarith
      _ ≤ (K.X.P.N : ℝ) ^ 7 * r₀ := mul_le_mul_of_nonneg_right h3 hr0.le
  obtain ⟨x, hx, hx1, hx2⟩ := exists_grid_mem (by have := K.X.P.hN; omega) hr0 hlo hhi r₀ rfl
  have hGr0 : 0 < Par.Gr K.X.P.N := by unfold Par.Gr; omega
  have hGrK : Par.Gr K.X.P.N ≤ 2 ^ K.X.b := by
    have := K.twoPow_b_ge
    have hm := K.m_pos
    have hN2 : 10 * K.X.P.N ^ 2 + 1 ≤ 12 * K.X.P.N ^ 3 := by
      have : 1 ≤ K.X.P.N := by have := K.X.P.hN; omega
      nlinarith [Nat.pow_le_pow_left this 2]
    unfold Par.Gr
    nlinarith
  have hc := card_cunif hGr0 hGrK hx
  have hsub : ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
      cunif (Par.Gr K.X.P.N) u = x) ⊆
      (univ.filter fun u ↦ K.Good (ph, j, del, D, 4, l, r₀) u) := by
    intro u hu
    rw [mem_filter] at hu ⊢
    refine ⟨mem_univ _, (K.good_tag4 hph).2 fun c' hc' ↦ ?_⟩
    rw [hpick] at hc'
    obtain rfl := Option.some.inj hc'
    rw [hu.2, heps]
    exact ⟨hx1, hx2⟩
  refine le_trans ?_ (le_trans hc (by exact_mod_cast card_le_card hsub))
  rw [K.card_fin_b, q₂_eq]
  have hGr : (2 : ℝ) * (Par.Gr K.X.P.N : ℕ) ≤ 12 * (K.X.P.N : ℝ) ^ 3 := by
    unfold Par.Gr
    push_cast
    nlinarith [pow_pos hN 2]
  have hK0 : (0 : ℝ) < 2 ^ K.X.b := by positivity
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left hK0.le (by positivity) hGr

end KSData

end BCFGJPSSV26.Stable


