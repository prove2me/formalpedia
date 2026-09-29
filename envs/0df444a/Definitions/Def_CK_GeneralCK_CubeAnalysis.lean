-- Prove2me | Definitions.Def_CK_GeneralCK_CubeAnalysis
-- name    : CK_GeneralCK_CubeAnalysis
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:21:12.603093+00:00
-- url     : https://prove2.me/theorems/c289f4e0-1bd0-4386-9aa5-9f56a6b97a65
-- title:
--   Courtade–Kumar proof module `GeneralCK.CubeAnalysis` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CubeAnalysis` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CubeAnalysis` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CubeAnalysis (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CubeAnalysis.lean)

import Definitions.Def_CK_GeneralCK_BellmanStatement
import Definitions.Def_CK_GeneralCK_ProfileBasics
import Definitions.Def_GeneralCK_cube_analysis

namespace GeneralCK.CubeAnalysis
open scoped BigOperators













theorem sum_slices {n : ℕ} (v : Cube (n+1) → ℝ) :
    ∑ x, v x = (∑ x, slice v false x) + ∑ x, slice v true x := by
  have h := (consEquiv n).sum_comp v
  simpa [consEquiv, slice, Fintype.sum_prod_type, Fintype.sum_bool, add_comm] using h.symm

theorem mean_succ {n : ℕ} (v : Cube (n+1) → ℝ) :
    mean v = (mean (slice v false) + mean (slice v true)) / 2 := by
  unfold mean
  rw [sum_slices]
  simp only [zpow_neg, zpow_natCast, pow_succ, mul_inv_rev]
  ring

theorem mean_zero (v : Cube 0 → ℝ) (x : Cube 0) : mean v = v x := by
  have he (y : Cube 0) : v y = v x := congrArg v (Subsingleton.elim _ _)
  simp [mean, he, Cube]

theorem mean_const (n : ℕ) (c : ℝ) : mean (fun _ : Cube n => c) = c := by
  simp [mean, Cube, zpow_neg, zpow_natCast]

theorem mean_mono {n : ℕ} {v w : Cube n → ℝ} (h : ∀ x, v x ≤ w x) : mean v ≤ mean w := by
  unfold mean
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_strictMono {n : ℕ} {v w : Cube n → ℝ} (h : ∀ x, v x < w x) :
    mean v < mean w := by
  unfold mean
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ => h x

theorem mean_interior {n : ℕ} {v : Cube n → ℝ} (h : ∀ x, 0 < v x ∧ v x < 1) :
    0 < mean v ∧ mean v < 1 := by
  constructor
  · simpa only [mean_const] using mean_strictMono (fun x => (h x).1)
  · simpa only [mean_const] using mean_strictMono (fun x => (h x).2)







/-- Reindex the stated Fin-valued Bellman premise along any finite enumeration. -/
theorem bellman_fintype (hB : FiniteHybridBellman) {α : Type*} [Fintype α]
    (w u v : α → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hu : ∀ i, 0 < u i ∧ u i < 1) (hv : ∀ i, 0 < v i ∧ v i < 1) :
    B (((∑ i, w i * u i) + ∑ i, w i * v i) / 2)
      (((∑ i, w i * H (u i)) + ∑ i, w i * H (v i)) / 2) ≤
    (B (∑ i, w i * u i) (∑ i, w i * H (u i)) +
      B (∑ i, w i * v i) (∑ i, w i * H (v i))) / 2 +
      ∑ i, w i * interiorCost (u i) (v i) := by
  classical
  let e := (Fintype.equivFin α).symm
  have reindex (f : α → ℝ) : (∑ i, f (e i)) = ∑ i, f i := e.sum_comp f
  have hh := hB (Fintype.card α) (w ∘ e) (u ∘ e) (v ∘ e)
    (fun i => hw (e i)) (by simpa only [Function.comp_apply, reindex] using hs)
    (fun i => hu (e i)) (fun i => hv (e i))
  dsimp only [Function.comp_apply] at hh
  rw [reindex (fun i => w i * u i), reindex (fun i => w i * v i),
    reindex (fun i => w i * H (u i)), reindex (fun i => w i * H (v i)),
    reindex (fun i => w i * interiorCost (u i) (v i))] at hh
  exact hh

theorem bellman_uniform (hB : FiniteHybridBellman) {n : ℕ} (u v : Cube n → ℝ)
    (hu : ∀ x, 0 < u x ∧ u x < 1) (hv : ∀ x, 0 < v x ∧ v x < 1) :
    B ((mean u + mean v) / 2) ((mean (H ∘ u) + mean (H ∘ v)) / 2) ≤
      (B (mean u) (mean (H ∘ u)) + B (mean v) (mean (H ∘ v))) / 2 +
      mean (fun x => interiorCost (u x) (v x)) := by
  have hw : (∑ _ : Cube n, (2 : ℝ) ^ (-(n : ℤ))) = 1 := by
    simp [Cube, zpow_neg, zpow_natCast]
  have h := bellman_fintype hB (fun _ => (2 : ℝ) ^ (-(n : ℤ))) u v
      (fun _ => by positivity) hw hu hv
  simpa only [← Finset.mul_sum, mean, Function.comp_apply] using h

/-- Manuscript Lemma 1.3, assuming only its stated hybrid Bellman premise. -/
theorem static_induction (hB : FiniteHybridBellman) (n : ℕ) (v : Cube n → ℝ)
    (hv : ∀ x, 0 < v x ∧ v x < 1) :
    B (mean v) (mean (H ∘ v)) ≤ energy n v := by
  induction n with
  | zero =>
    rw [mean_zero v default, mean_zero (H ∘ v) default]
    simpa [energy] using (B_H (hv default).1 (hv default).2).le
  | succ n ih =>
    have hfalse := ih (slice v false) (fun x => hv (Fin.cons false x))
    have htrue := ih (slice v true) (fun x => hv (Fin.cons true x))
    have hb := bellman_uniform hB (slice v false) (slice v true)
      (fun x => hv (Fin.cons false x)) (fun x => hv (Fin.cons true x))
    rw [mean_succ v, mean_succ (H ∘ v)]
    change B ((mean (slice v false) + mean (slice v true)) / 2)
      ((mean (H ∘ slice v false) + mean (H ∘ slice v true)) / 2) ≤ _
    dsimp only [energy]
    linarith

end GeneralCK.CubeAnalysis


