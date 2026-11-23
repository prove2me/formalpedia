-- Prove2me | Definitions.Def_FracTruthSched_PaddingLimitToolkit
-- name    : FracTruthSched_PaddingLimitToolkit
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:28.116209+00:00
-- url     : https://prove2.me/theorems/2f71542c-775e-45ae-b866-1c899c7430ed
-- title:
--   Compactness and normalized-disutility toolkit for limit mechanisms
-- statement:
--   Reusable, sorry-free infrastructure for Appendix A.2–A.4. The module contains: (1) a Tychonoff/ultrafilter compactness theorem extracting coordinatewise limits for a sequence in any product of closed real intervals, with the ultrafilter finer than `atTop`; (2) the zero-row identity and bounds $0\le V_i(t)\le\sum_jt_{ij}$ for normalized disutility on nonnegative admissible inputs; (3) truthfulness in the closed form $V_i(t)-V_i(b_i,t_{-i})\le\sum_j(t_{ij}-b_j)x_{ij}(b_i,t_{-i})$; and (4) reconstruction $P_i(t)=\sum_jt_{ij}x_{ij}(t)-V_i(t)$, with proofs that reconstruction preserves normalized disutility, feasibility and truthfulness. These are exactly the common ingredients of the rational diagonal limit and the real ceiling-rounding limit.
-- source:
--   Anastasiadis et al., arXiv:2611.06642v1, Appendix A.2, p.26 (Claim 8) and Appendix A.3, pp.26–27 (Claim 9). The paper's diagonal subsequence is replaced by Tychonoff compactness and an ultrafilter finer than atTop; the normalized disutility bounds and reconstruction are elementary consequences of §2.1 truthfulness and feasibility used in these limit arguments.

import Mathlib
import Definitions.Def_FracTruthSched_disutility
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn

set_option autoImplicit false

open Filter Topology Set

namespace FracTruthSched.PaddingLimit

/-- Coordinatewise compactness for a sequence in a product of real intervals.
An ultrafilter finer than `atTop` replaces the paper's diagonal subsequence. -/
lemma exists_ultrafilter_limit {ι : Type*} (a : ℕ → ι → ℝ) (lo hi : ι → ℝ)
    (ha : ∀ h q, a h q ∈ Set.Icc (lo q) (hi q)) :
    ∃ (U : Ultrafilter ℕ) (L : ι → ℝ), (↑U : Filter ℕ) ≤ atTop ∧
      (∀ q, L q ∈ Set.Icc (lo q) (hi q)) ∧
      ∀ q, Tendsto (fun h => a h q) U (𝓝 (L q)) := by
  classical
  obtain ⟨U, hU⟩ := Filter.exists_ultrafilter_le (atTop : Filter ℕ)
  let A : ι → Type := fun q => ↥(Set.Icc (lo q) (hi q))
  let F : ℕ → (q : ι) → A q := fun h q => ⟨a h q, ha h q⟩
  obtain ⟨L, -, hL⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set ((q : ι) → A q))).ultrafilter_le_nhds
      (Ultrafilter.map F U) (by simp)
  have htF : Tendsto F U (𝓝 L) := hL
  have htcoord (q : ι) : Tendsto (fun h => F h q) U (𝓝 (L q)) :=
    (continuous_apply q).continuousAt.tendsto.comp htF
  refine ⟨U, fun q => (L q : ℝ), hU, fun q => (L q).2, ?_⟩
  intro q
  change Tendsto (fun h => (F h q : ℝ)) U (𝓝 (L q : ℝ))
  exact continuous_subtype_val.continuousAt.tendsto.comp (htcoord q)

/-- Normalized disutility vanishes at a zero row. -/
lemma disutility_at_zero_row {n : ℕ} {τ : Type*} [Fintype τ] (M : FracMech n τ)
    (t : Fin n → τ → ℝ) (i : Fin n) : disutility M (Function.update t i 0) i = 0 := by
  simp [disutility]

/-- At a zero report truthfulness makes the payment reference point an upper bound. -/
lemma payment_at_zero_row_le {n : ℕ} {τ : Type*} [Fintype τ]
    {D : (Fin n → τ → ℝ) → Prop} {M : FracMech n τ} (htruth : IsTruthfulOn D M)
    {t : Fin n → τ → ℝ} (ht : D t) (i : Fin n)
    (hz : D (Function.update t i 0)) : M.P t i ≤ M.P (Function.update t i 0) i := by
  have h := htruth (Function.update t i 0) hz i (t i) (by simpa using ht)
  simpa using h

/-- Lower compactness bound for normalized disutility on nonnegative admissible inputs. -/
lemma disutility_nonneg {n : ℕ} {τ : Type*} [Fintype τ]
    {D : (Fin n → τ → ℝ) → Prop} {M : FracMech n τ}
    (hfeas : IsFeasibleOn D M) (htruth : IsTruthfulOn D M)
    {t : Fin n → τ → ℝ} (ht : D t) (i : Fin n)
    (hz : D (Function.update t i 0)) (hrow : ∀ j, 0 ≤ t i j) :
    0 ≤ disutility M t i := by
  have hp := payment_at_zero_row_le htruth ht i hz
  have hs : 0 ≤ ∑ j, t i j * M.x t i j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hrow j) ((hfeas t ht).1 i j).1)
  dsimp [disutility]
  linarith

/-- Upper compactness bound for normalized disutility on nonnegative admissible inputs. -/
lemma disutility_le_sum {n : ℕ} {τ : Type*} [Fintype τ]
    {D : (Fin n → τ → ℝ) → Prop} {M : FracMech n τ}
    (hfeas : IsFeasibleOn D M) (htruth : IsTruthfulOn D M)
    {t : Fin n → τ → ℝ} (ht : D t) (i : Fin n)
    (hz : D (Function.update t i 0)) (hrow : ∀ j, 0 ≤ t i j) :
    disutility M t i ≤ ∑ j, t i j := by
  let z := Function.update t i 0
  have h := htruth t ht i 0 hz
  have hle : disutility M t i ≤ ∑ j, t i j * M.x z i j := by
    dsimp [disutility, z] at *
    linarith
  calc
    disutility M t i ≤ ∑ j, t i j * M.x z i j := hle
    _ ≤ ∑ j, t i j := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [(hfeas z hz).1 i j |>.1, (hfeas z hz).1 i j |>.2, hrow j]

/-- Truthfulness written using only normalized disutility and the allocation at the
reported input. This is the closed inequality used in both limit arguments. -/
lemma normalized_truthful {n : ℕ} {τ : Type*} [Fintype τ]
    {D : (Fin n → τ → ℝ) → Prop} {M : FracMech n τ} (htruth : IsTruthfulOn D M)
    {t : Fin n → τ → ℝ} (ht : D t) (i : Fin n) (b : τ → ℝ)
    (hb : D (Function.update t i b)) :
    disutility M t i - disutility M (Function.update t i b) i ≤
      ∑ j, (t i j - b j) * M.x (Function.update t i b) i j := by
  have hz0 : Function.update (Function.update t i b) i 0 = Function.update t i 0 := by
    funext u
    by_cases hui : u = i
    · subst u; simp
    · simp [Function.update_of_ne hui]
  have h := htruth t ht i b hb
  simp only [disutility, Function.update_self, hz0]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  linarith

/-- Reconstruct a mechanism from an allocation and normalized disutility. -/
noncomputable def mechanismOfXV {n : ℕ} {τ : Type*} [Fintype τ]
    (x : (Fin n → τ → ℝ) → Fin n → τ → ℝ)
    (V : (Fin n → τ → ℝ) → Fin n → ℝ) : FracMech n τ where
  x := x
  P t i := (∑ j, t i j * x t i j) - V t i

lemma disutility_mechanismOfXV {n : ℕ} {τ : Type*} [Fintype τ]
    (x : (Fin n → τ → ℝ) → Fin n → τ → ℝ)
    (V : (Fin n → τ → ℝ) → Fin n → ℝ)
    (hV : ∀ t i, V (Function.update t i 0) i = 0) (t : Fin n → τ → ℝ) (i : Fin n) :
    disutility (mechanismOfXV x V) t i = V t i := by
  simp [disutility, mechanismOfXV, hV]

lemma feasible_mechanismOfXV {n : ℕ} {τ : Type*} [Fintype τ]
    {D : (Fin n → τ → ℝ) → Prop}
    (x : (Fin n → τ → ℝ) → Fin n → τ → ℝ)
    (V : (Fin n → τ → ℝ) → Fin n → ℝ)
    (hx0 : ∀ t, D t → ∀ i j, 0 ≤ x t i j)
    (hx1 : ∀ t, D t → ∀ i j, x t i j ≤ 1)
    (hxsum : ∀ t, D t → ∀ j, ∑ i, x t i j = 1) : IsFeasibleOn D (mechanismOfXV x V) := by
  intro t ht
  exact ⟨fun i j => ⟨hx0 t ht i j, hx1 t ht i j⟩, hxsum t ht⟩

lemma truthful_mechanismOfXV {n : ℕ} {τ : Type*} [Fintype τ]
    {D : (Fin n → τ → ℝ) → Prop}
    (x : (Fin n → τ → ℝ) → Fin n → τ → ℝ)
    (V : (Fin n → τ → ℝ) → Fin n → ℝ)
    (hIC : ∀ t, D t → ∀ i b, D (Function.update t i b) →
      V t i - V (Function.update t i b) i ≤
        ∑ j, (t i j - b j) * x (Function.update t i b) i j) :
    IsTruthfulOn D (mechanismOfXV x V) := by
  intro t ht i b hb
  have h := hIC t ht i b hb
  have hs : (∑ j, (b j - t i j) * x (Function.update t i b) i j) =
      -(∑ j, (t i j - b j) * x (Function.update t i b) i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [mechanismOfXV, Function.update_self]
  calc
    (∑ j, b j * x (Function.update t i b) i j) - V (Function.update t i b) i -
        ∑ j, t i j * x (Function.update t i b) i j =
        (∑ j, (b j - t i j) * x (Function.update t i b) i j) -
          V (Function.update t i b) i := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ -V t i := by rw [hs]; linarith
    _ = (∑ j, t i j * x t i j) - V t i - ∑ j, t i j * x t i j := by ring

end FracTruthSched.PaddingLimit


