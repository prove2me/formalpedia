-- Prove2me | Definitions.Def_ChapterNonnegResolvent
-- name    : ChapterNonnegResolvent
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T14:10:46.32005+00:00
-- url     : https://prove2.me/theorems/3e94fa96-1936-46d3-a914-7817282b2c73
-- title:
--   Chapter NonnegResolvent
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNonnegResolvent.lean`): generated def bundle for ChapterNonnegResolvent. See BookProof/ChapterNonnegResolvent.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNonnegResolvent.lean

import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Mathlib


/-!
# The resolvent family and the Yosida approximation of a non-negative self-adjoint relation

`BookProof.ChapterNonnegSquareRoot` produced, for a non-negative self-adjoint linear
relation `T` on a complex Hilbert space `F` and every `a > 0`, the everywhere-defined
bounded operator `R a = invCLMAt hT ha = (T + a)⁻¹` solving `a x + T x = h`, with
`‖R a h‖ ≤ ‖h‖ / a`.  This chapter develops that family into the standard resolvent
calculus and the Yosida approximation.

* **The first resolvent identity** `R a − R b = (b − a) R a R b` (`invCLMAt_sub`),
  and the commutation `R a R b = R b R a` (`invCLMAt_comm`).
* **Positivity.**  Each `R a` is self-adjoint (`isSelfAdjoint_invCLMAt`) and non-negative
  (`invCLMAt_nonneg`), and `a R a` is a positive contraction (`norm_smul_invCLMAt_le`,
  `smul_invCLMAt_le_one`).
* **`a R a → 1` strongly.**  On the domain, `a R a h − h = − R a k` for `(h, k) ∈ T`
  (`smul_invCLMAt_sub_of_mem`), so `‖a R a h − h‖ ≤ ‖k‖ / a`.  The domain of a
  single-valued non-negative self-adjoint relation is dense (`dense_domain`), whence
  `a R a h → h` for *every* `h` (`tendsto_smul_invCLMAt`, and the sequential form
  `tendsto_smul_resAt`).
* **The Yosida approximation** `T_a = a (1 − a R a) = a − a² R a` (`yosidaCLM`) is a
  bounded, self-adjoint, non-negative operator with `(a R a h, T_a h) ∈ T`
  (`yosidaCLM_mem`); on the domain `T_a h = a R a k` for `(h, k) ∈ T`
  (`yosidaCLM_of_mem`), so `‖T_a h‖ ≤ ‖k‖` (`norm_yosidaCLM_le_of_mem`) and
  `T_a h → k` (`tendsto_yosidaCLM`, `tendsto_yosidaAt`): the bounded operators `T_a`
  approximate `T` pointwise on its domain.  They increase with `a`
  (`yosidaCLM_sub`: `T_b − T_a = (b − a)(1 − a R a)(1 − b R b)`, whence `yosidaCLM_mono`)
  and stay below `T` on its domain (`re_inner_yosidaCLM_le`).

Everything is stated for linear relations, so no single-valuedness is assumed except
where the *strong* convergence statements need a dense domain.
-/

namespace BookProof.NonnegResolvent

open BookProof.ClosureUniqueness BookProof.PositiveSquareRoot BookProof.NonnegSquareRoot
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {T : Submodule ℂ (F × F)} {a b : ℝ}

/-! ## The resolvent identity -/

/-- **The first resolvent identity**: `(T + a)⁻¹ − (T + b)⁻¹ = (b − a) (T + a)⁻¹ (T + b)⁻¹`. -/
theorem invCLMAt_sub (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (hb : 0 < b) (h : F) :
    invCLMAt hT ha h - invCLMAt hT hb h
      = ((b : ℂ) - (a : ℂ)) • invCLMAt hT ha (invCLMAt hT hb h) := by
  have hb1 := invCLMAt_mem hT hb h
  set x := invCLMAt hT hb h with hxdef
  have hmem : (x, (h + ((a : ℂ) - (b : ℂ)) • x) - (a : ℂ) • x) ∈ T := by
    have hsimp : (h + ((a : ℂ) - (b : ℂ)) • x) - (a : ℂ) • x = h - (b : ℂ) • x := by
      module
    rw [hsimp]
    exact hb1
  have hxa : invCLMAt hT ha (h + ((a : ℂ) - (b : ℂ)) • x) = x :=
    invCLMAt_eq_of_mem hT ha hmem
  rw [map_add, map_smul] at hxa
  have hrw : invCLMAt hT ha h = x - ((a : ℂ) - (b : ℂ)) • invCLMAt hT ha x :=
    eq_sub_of_add_eq hxa
  rw [hrw]
  module

/-- The resolvents at two positive parameters commute. -/
theorem invCLMAt_comm (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (hb : 0 < b) (h : F) :
    invCLMAt hT ha (invCLMAt hT hb h) = invCLMAt hT hb (invCLMAt hT ha h) := by
  rcases eq_or_ne a b with rfl | hne
  · rfl
  · have h1 := invCLMAt_sub hT ha hb h
    have h2 := invCLMAt_sub hT hb ha h
    have hc : ((b : ℂ) - (a : ℂ)) ≠ 0 := by
      intro hh
      exact hne (by exact_mod_cast (sub_eq_zero.1 hh).symm)
    have e2 : ((b : ℂ) - (a : ℂ)) • invCLMAt hT hb (invCLMAt hT ha h)
        = invCLMAt hT ha h - invCLMAt hT hb h := by
      rw [show ((b : ℂ) - (a : ℂ)) = -((a : ℂ) - (b : ℂ)) by ring, neg_smul, ← h2]
      abel
    exact smul_right_injective F hc (h1.symm.trans e2.symm)

/-! ## Positivity of the resolvent -/

/-- `⟪(T + a)⁻¹ h, k⟫ = ⟪h, (T + a)⁻¹ k⟫`. -/
theorem inner_invCLMAt_left (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h k : F) :
    (inner ℂ (invCLMAt hT ha h) k : ℂ) = inner ℂ h (invCLMAt hT ha k) := by
  have h1 := invCLMAt_mem hT ha h
  have h2 := invCLMAt_mem hT ha k
  set x := invCLMAt hT ha h with hxdef
  set u := invCLMAt hT ha k with hudef
  have hs : (inner ℂ (k - (a : ℂ) • u) x : ℂ) = inner ℂ u (h - (a : ℂ) • x) :=
    symm_inner hT h1 h2
  have e3 : (inner ℂ x (k - (a : ℂ) • u) : ℂ) = inner ℂ (h - (a : ℂ) • x) u := by
    have := congrArg (starRingEnd ℂ) hs
    rwa [inner_conj_symm, inner_conj_symm] at this
  have e1 : (inner ℂ x k : ℂ)
      = inner ℂ x ((a : ℂ) • u) + inner ℂ x (k - (a : ℂ) • u) := by
    rw [← inner_add_right]; congr 1; abel
  have e2 : (inner ℂ h u : ℂ)
      = inner ℂ ((a : ℂ) • x) u + inner ℂ (h - (a : ℂ) • x) u := by
    rw [← inner_add_left]; congr 1; abel
  have e4 : (inner ℂ x ((a : ℂ) • u) : ℂ) = inner ℂ ((a : ℂ) • x) u := by
    rw [inner_smul_right, inner_smul_left, Complex.conj_ofReal]
  rw [e1, e2, e3, e4]

/-- **`(T + a)⁻¹` is self-adjoint.** -/
theorem isSelfAdjoint_invCLMAt (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) :
    IsSelfAdjoint (invCLMAt hT ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  exact inner_invCLMAt_left hT ha x y

/-- **`(T + a)⁻¹ ≥ 0`.** -/
theorem invCLMAt_nonneg (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) : 0 ≤ invCLMAt hT ha := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro h
  have hmem := invCLMAt_mem hT ha h
  have hre := hT.nonneg _ hmem
  have him := inner_im_eq_zero hT hmem
  simp only at hre him
  set x := invCLMAt hT ha h with hxdef
  have hsplit : (inner ℂ x h : ℂ)
      = inner ℂ x ((a : ℂ) • x) + inner ℂ x (h - (a : ℂ) • x) := by
    rw [← inner_add_right]; congr 1; abel
  have hxx : (inner ℂ x ((a : ℂ) • x) : ℂ) = ((a * ‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hsplit, hxx]
  constructor
  · apply Complex.ext
    · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    · simp only [RCLike.re_to_complex, Complex.ofReal_im, Complex.add_im, him, add_zero]
  · simp only [RCLike.re_to_complex, Complex.add_re, Complex.ofReal_re]
    have hsq : (0 : ℝ) ≤ a * ‖x‖ ^ 2 := by positivity
    linarith

/-- **`‖a (T + a)⁻¹ h‖ ≤ ‖h‖`**: `a (T + a)⁻¹` is a contraction. -/
theorem norm_smul_invCLMAt_le (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    ‖(a : ℂ) • invCLMAt hT ha h‖ ≤ ‖h‖ := by
  have hb := norm_invCLMAt_le hT ha h
  rw [norm_smul]
  have hnorm : ‖(a : ℂ)‖ = a := by
    simp [abs_of_pos ha]
  rw [hnorm]
  calc a * ‖invCLMAt hT ha h‖ ≤ a * (a⁻¹ * ‖h‖) := by
        exact mul_le_mul_of_nonneg_left hb ha.le
    _ = ‖h‖ := by
        field_simp

/-- **`a (T + a)⁻¹ ≤ 1`.** -/
theorem smul_invCLMAt_le_one (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) :
    (a : ℂ) • invCLMAt hT ha ≤ 1 := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro h
  have hmem := invCLMAt_mem hT ha h
  have hre := hT.nonneg _ hmem
  have him := inner_im_eq_zero hT hmem
  simp only at hre him
  set x := invCLMAt hT ha h with hxdef
  have happ : ((1 : F →L[ℂ] F) - (a : ℂ) • invCLMAt hT ha) h = h - (a : ℂ) • x := rfl
  have hs : (inner ℂ (h - (a : ℂ) • x) x : ℂ) = inner ℂ x (h - (a : ℂ) • x) :=
    symm_inner hT hmem hmem
  have hsplit : (inner ℂ (h - (a : ℂ) • x) h : ℂ)
      = inner ℂ (h - (a : ℂ) • x) ((a : ℂ) • x)
        + inner ℂ (h - (a : ℂ) • x) (h - (a : ℂ) • x) := by
    rw [← inner_add_right]; congr 1; abel
  have hsa : (inner ℂ (h - (a : ℂ) • x) ((a : ℂ) • x) : ℂ)
      = (a : ℂ) * inner ℂ x (h - (a : ℂ) • x) := by
    rw [inner_smul_right, hs]
  have hww : (inner ℂ (h - (a : ℂ) • x) (h - (a : ℂ) • x) : ℂ)
      = ((‖h - (a : ℂ) • x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [happ, hsplit, hsa, hww]
  constructor
  · apply Complex.ext
    · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    · simp only [RCLike.re_to_complex, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, him, zero_mul, mul_zero, add_zero]
  · simp only [RCLike.re_to_complex, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hsq : (0 : ℝ) ≤ ‖h - (a : ℂ) • x‖ ^ 2 := by positivity
    have : (0 : ℝ) ≤ a * (inner ℂ x (h - (a : ℂ) • x) : ℂ).re :=
      mul_nonneg ha.le hre
    linarith

omit [CompleteSpace F] in
/-- A non-negative real multiple of a non-negative operator is non-negative. -/
theorem smul_nonneg_of_nonneg {c : ℝ} (hc : 0 ≤ c) {A : F →L[ℂ] F} (hA : 0 ≤ A) :
    0 ≤ (c : ℂ) • A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex] at hA
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro h
  have happ : ((c : ℂ) • A) h = (c : ℂ) • (A h) := rfl
  rw [happ, inner_smul_left, Complex.conj_ofReal]
  obtain ⟨hc1, hc2⟩ := hA h
  have him : (inner ℂ (A h) h : ℂ).im = 0 := by
    have := congrArg Complex.im hc1
    simpa using this.symm
  constructor
  · apply Complex.ext
    · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    · simp only [RCLike.re_to_complex, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, him, mul_zero, zero_mul, add_zero]
  · simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_nonneg hc hc2

/-! ## `a (T + a)⁻¹ → 1` strongly -/

/-- On the domain of `T`, the resolvent is computed explicitly:
`a (T + a)⁻¹ h = h − (T + a)⁻¹ k` for `(h, k) ∈ T`. -/
theorem smul_invCLMAt_sub_of_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) {h k : F}
    (hk : (h, k) ∈ T) :
    (a : ℂ) • invCLMAt hT ha h - h = -invCLMAt hT ha k := by
  have hx : invCLMAt hT ha ((a : ℂ) • h + k) = h := by
    refine invCLMAt_eq_of_mem hT ha ?_
    simpa using hk
  rw [map_add, map_smul] at hx
  have h2 : (a : ℂ) • invCLMAt hT ha h - h + invCLMAt hT ha k = 0 := by
    rw [sub_add_eq_add_sub, hx, sub_self]
  exact add_eq_zero_iff_eq_neg.mp h2

/-- Hence `‖a (T + a)⁻¹ h − h‖ ≤ ‖k‖ / a` on the domain. -/
theorem norm_smul_invCLMAt_sub_le (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) {h k : F}
    (hk : (h, k) ∈ T) :
    ‖(a : ℂ) • invCLMAt hT ha h - h‖ ≤ a⁻¹ * ‖k‖ := by
  rw [smul_invCLMAt_sub_of_mem hT ha hk, norm_neg]
  exact norm_invCLMAt_le hT ha k

/-- **The domain of a single-valued non-negative self-adjoint relation is dense.** -/
theorem dense_domain (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) :
    Dense (T.map (LinearMap.fst ℂ F F) : Set F) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.2
    (Submodule.topologicalClosure_eq_top_iff.2 ?_)
  refine Submodule.eq_bot_iff _ |>.2 ?_
  intro z hz
  have hzero : ((0 : F), z) ∈ adjPairs T := by
    intro q hq
    have hq1 : q.1 ∈ T.map (LinearMap.fst ℂ F F) :=
      Submodule.mem_map.2 ⟨q, hq, rfl⟩
    have := (Submodule.mem_orthogonal _ _).1 hz q.1 hq1
    simpa using this.symm
  rw [hT.adj] at hzero
  exact hsv z hzero

/-- **`a (T + a)⁻¹ → 1` strongly** as `a → ∞`, for a single-valued `T`. -/
theorem tendsto_smul_invCLMAt (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (h : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : ℝ) (hc : 0 < c), A ≤ c →
      ‖(c : ℂ) • invCLMAt hT hc h - h‖ < ε := by
  have hdense := dense_domain hT hsv
  have hmem : h ∈ closure ((T.map (LinearMap.fst ℂ F F) : Set F)) := hdense h
  obtain ⟨u, hu, hdist⟩ := Metric.mem_closure_iff.1 hmem (ε / 3) (by linarith)
  obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hu
  refine ⟨max 1 (4 * ‖p.2‖ / ε), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro c hc hcA
  have hc3 : 4 * ‖p.2‖ / ε ≤ c := le_trans (le_max_right _ _) hcA
  have hpu : (u, p.2) ∈ T := by
    have : p = (u, p.2) := by
      rw [← hp1]
      simp
    rwa [← this]
  have hdec : (c : ℂ) • invCLMAt hT hc h - h
      = (c : ℂ) • invCLMAt hT hc (h - u) + ((c : ℂ) • invCLMAt hT hc u - u) + (u - h) := by
    rw [map_sub, smul_sub]
    abel
  have hb1 : ‖(c : ℂ) • invCLMAt hT hc (h - u)‖ ≤ ‖h - u‖ :=
    norm_smul_invCLMAt_le hT hc (h - u)
  have hb2 : ‖(c : ℂ) • invCLMAt hT hc u - u‖ ≤ c⁻¹ * ‖p.2‖ :=
    norm_smul_invCLMAt_sub_le hT hc hpu
  have hhu : ‖h - u‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hdist
  have huh : ‖u - h‖ < ε / 3 := by
    rw [norm_sub_rev]
    exact hhu
  have hb2' : c⁻¹ * ‖p.2‖ < ε / 3 := by
    rcases eq_or_lt_of_le (norm_nonneg p.2) with hz | hz
    · rw [← hz, mul_zero]
      linarith
    · have hcpos : 0 < c := hc
      rw [inv_mul_eq_div, div_lt_iff₀ hcpos]
      have h3 : 4 * ‖p.2‖ ≤ c * ε := by
        rw [div_le_iff₀ hε] at hc3
        linarith
      linarith
  calc ‖(c : ℂ) • invCLMAt hT hc h - h‖
      ≤ ‖(c : ℂ) • invCLMAt hT hc (h - u) + ((c : ℂ) • invCLMAt hT hc u - u)‖ + ‖u - h‖ := by
        rw [hdec]
        exact norm_add_le _ _
    _ ≤ ‖(c : ℂ) • invCLMAt hT hc (h - u)‖ + ‖(c : ℂ) • invCLMAt hT hc u - u‖ + ‖u - h‖ := by
        gcongr
        exact norm_add_le _ _
    _ < ε := by
        linarith [hb1.trans_lt hhu, hb2.trans_lt hb2', huh]

/-! ## The Yosida approximation -/

/-- **The Yosida approximation `T_a = a (1 − a (T + a)⁻¹)`**, a bounded operator. -/
noncomputable def yosidaCLM (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) : F →L[ℂ] F :=
  (a : ℂ) • (1 - (a : ℂ) • invCLMAt hT ha)

theorem yosidaCLM_apply (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    yosidaCLM hT ha h = (a : ℂ) • (h - (a : ℂ) • invCLMAt hT ha h) := by
  simp [yosidaCLM]

/-- `(a (T + a)⁻¹ h, T_a h)` is a point of the graph of `T`. -/
theorem yosidaCLM_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (h : F) :
    ((a : ℂ) • invCLMAt hT ha h, yosidaCLM hT ha h) ∈ T := by
  have hmem := T.smul_mem (a : ℂ) (invCLMAt_mem hT ha h)
  rw [Prod.smul_mk] at hmem
  rw [yosidaCLM_apply]
  exact hmem

/-- On the domain, `T_a h = a (T + a)⁻¹ k` for `(h, k) ∈ T`. -/
theorem yosidaCLM_of_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) {h k : F}
    (hk : (h, k) ∈ T) :
    yosidaCLM hT ha h = (a : ℂ) • invCLMAt hT ha k := by
  have h1 := smul_invCLMAt_sub_of_mem hT ha hk
  have h2 : h - (a : ℂ) • invCLMAt hT ha h = invCLMAt hT ha k := by
    rw [← neg_sub, h1, neg_neg]
  rw [yosidaCLM_apply, h2]

/-- **`‖T_a h‖ ≤ ‖k‖`** for `(h, k) ∈ T`: the Yosida approximation is dominated by `T`. -/
theorem norm_yosidaCLM_le_of_mem (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) {h k : F}
    (hk : (h, k) ∈ T) : ‖yosidaCLM hT ha h‖ ≤ ‖k‖ := by
  rw [yosidaCLM_of_mem hT ha hk]
  exact norm_smul_invCLMAt_le hT ha k

/-- `T_a` is self-adjoint. -/
theorem isSelfAdjoint_yosidaCLM (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) :
    IsSelfAdjoint (yosidaCLM hT ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change (inner ℂ (yosidaCLM hT ha x) y : ℂ) = inner ℂ x (yosidaCLM hT ha y)
  simp only [yosidaCLM_apply, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    Complex.conj_ofReal]
  rw [inner_invCLMAt_left hT ha x y]

/-- **`T_a ≥ 0`**: the Yosida approximation of a non-negative relation is non-negative. -/
theorem yosidaCLM_nonneg (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) : 0 ≤ yosidaCLM hT ha :=
  smul_nonneg_of_nonneg ha.le (sub_nonneg.2 (smul_invCLMAt_le_one hT ha))

/-- **`T_a ≤ T` on the domain**: `⟪h, T_a h⟫ ≤ ⟪h, k⟫` for `(h, k) ∈ T`. -/
theorem re_inner_yosidaCLM_le (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) {h k : F}
    (hk : (h, k) ∈ T) :
    (inner ℂ h (yosidaCLM hT ha h) : ℂ).re ≤ (inner ℂ h k : ℂ).re := by
  have hsub : h - (a : ℂ) • invCLMAt hT ha h = invCLMAt hT ha k := by
    rw [← neg_sub, smul_invCLMAt_sub_of_mem hT ha hk, neg_neg]
  have hy : (inner ℂ h (yosidaCLM hT ha h) : ℂ) = inner ℂ ((a : ℂ) • invCLMAt hT ha h) k := by
    rw [yosidaCLM_of_mem hT ha hk, inner_smul_right, inner_smul_left, Complex.conj_ofReal,
      inner_invCLMAt_left hT ha h k]
  have hsplit : (inner ℂ h k : ℂ)
      = inner ℂ ((a : ℂ) • invCLMAt hT ha h) k + inner ℂ (invCLMAt hT ha k) k := by
    rw [← inner_add_left, ← hsub]
    congr 1
    abel
  have hpos : 0 ≤ (inner ℂ (invCLMAt hT ha k) k : ℂ).re := by
    have := (ContinuousLinearMap.isPositive_iff_complex _).1
      ((ContinuousLinearMap.nonneg_iff_isPositive _).1 (invCLMAt_nonneg hT ha)) k
    exact this.2
  rw [hy, hsplit, Complex.add_re]
  linarith

/-! ## The Yosida approximation increases with `a` -/

/-- The operator form of the resolvent identity. -/
theorem invCLMAt_sub_eq (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (hb : 0 < b) :
    invCLMAt hT ha - invCLMAt hT hb = ((b : ℂ) - (a : ℂ)) • (invCLMAt hT ha * invCLMAt hT hb) := by
  ext h
  simpa using invCLMAt_sub hT ha hb h

/-- **`T_b − T_a = (b − a) (1 − a R a)(1 − b R b)`.** -/
theorem yosidaCLM_sub (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (hb : 0 < b) :
    yosidaCLM hT hb - yosidaCLM hT ha
      = ((b : ℂ) - (a : ℂ)) •
        ((1 - (a : ℂ) • invCLMAt hT ha) * (1 - (b : ℂ) • invCLMAt hT hb)) := by
  ext h
  have hres : invCLMAt hT ha h - invCLMAt hT hb h
      = ((b : ℂ) - (a : ℂ)) • invCLMAt hT ha (invCLMAt hT hb h) := invCLMAt_sub hT ha hb h
  simp only [yosidaCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul]
  linear_combination (norm := module) ((a : ℂ) * (b : ℂ)) • hres

/-- **The Yosida approximation increases with `a`.** -/
theorem yosidaCLM_mono (hT : IsNonnegSelfAdjoint T) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    yosidaCLM hT ha ≤ yosidaCLM hT hb := by
  rw [← sub_nonneg, yosidaCLM_sub hT ha hb]
  have hA : (0 : F →L[ℂ] F) ≤ 1 - (a : ℂ) • invCLMAt hT ha :=
    sub_nonneg.2 (smul_invCLMAt_le_one hT ha)
  have hB : (0 : F →L[ℂ] F) ≤ 1 - (b : ℂ) • invCLMAt hT hb :=
    sub_nonneg.2 (smul_invCLMAt_le_one hT hb)
  have hcomm : (1 - (a : ℂ) • invCLMAt hT ha) * (1 - (b : ℂ) • invCLMAt hT hb)
      = (1 - (b : ℂ) • invCLMAt hT hb) * (1 - (a : ℂ) • invCLMAt hT ha) := by
    ext h
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul]
    rw [invCLMAt_comm hT ha hb h]
    module
  have hprod : (0 : F →L[ℂ] F) ≤
      (1 - (a : ℂ) • invCLMAt hT ha) * (1 - (b : ℂ) • invCLMAt hT hb) :=
    (commute_iff_mul_nonneg hA hB).1 hcomm
  have hcast : ((b : ℂ) - (a : ℂ)) = ((b - a : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  exact smul_nonneg_of_nonneg (by linarith) hprod

/-- **`T_a h → k`** for `(h, k) ∈ T`, when `T` is single-valued. -/
theorem tendsto_yosidaCLM (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : ℝ) (hc : 0 < c), A ≤ c → ‖yosidaCLM hT hc h - k‖ < ε := by
  obtain ⟨A, hA, hbound⟩ := tendsto_smul_invCLMAt hT hsv k hε
  refine ⟨A, hA, ?_⟩
  intro c hc hcA
  rw [yosidaCLM_of_mem hT hc hk]
  exact hbound c hc hcA

/-! ## Sequential form -/

/-- The resolvent at `n + 1`, as a sequence of bounded operators. -/
noncomputable def resAt (hT : IsNonnegSelfAdjoint T) (n : ℕ) : F →L[ℂ] F :=
  invCLMAt hT (a := (n : ℝ) + 1) (by positivity)

/-- The Yosida approximation at `n + 1`, as a sequence of bounded operators. -/
noncomputable def yosidaAt (hT : IsNonnegSelfAdjoint T) (n : ℕ) : F →L[ℂ] F :=
  yosidaCLM hT (a := (n : ℝ) + 1) (by positivity)



/-- **`T_{n+1} h → k` for `(h, k) ∈ T`**: the Yosida approximations converge to `T`
pointwise on its domain. -/
theorem tendsto_yosidaAt (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) :
    Filter.Tendsto (fun n : ℕ => yosidaAt hT n h) Filter.atTop (nhds k) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hA, hbound⟩ := tendsto_yosidaCLM hT hsv hk hε
  refine ⟨⌈A⌉₊, fun n hn => ?_⟩
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hAc : A ≤ (n : ℝ) + 1 := by
    have h1 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have h2 : ((⌈A⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [dist_eq_norm]
  exact hbound ((n : ℝ) + 1) hc hAc

end BookProof.NonnegResolvent


