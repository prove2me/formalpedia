-- Prove2me | Definitions.Def_ChapterPositiveSquareRootUnique
-- name    : ChapterPositiveSquareRootUnique
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T13:14:17.460374+00:00
-- url     : https://prove2.me/theorems/65919adc-7430-4ebb-a15a-81ac5b30e5ec
-- title:
--   Chapter PositiveSquareRootUnique
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPositiveSquareRootUnique.lean`): generated def bundle for ChapterPositiveSquareRootUnique. See BookProof/ChapterPositiveSquareRootUnique.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPositiveSquareRootUnique.lean

import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterVonNeumannCore
import Definitions.Def_ChapterUnboundedPolar
import Mathlib


/-!
# `|Ā| = (A* Ā)^{1/2}` is *the* non-negative square root — uniqueness

`BookProof.ChapterUnboundedPolar` constructs `absRel A = |Ā|`, proves it
self-adjoint and non-negative, and proves `|Ā|² = A* Ā` (`absRel_comp_self`).
What was missing — the reason `(A* Ā)^{1/2}` could only be called *a* square root
— is **uniqueness**: that no other non-negative self-adjoint relation squares to
`A* Ā`.  Classically this is read off the spectral theorem for unbounded
self-adjoint operators.  This module proves it with the **bounded** continuous
functional calculus only.

## The argument

Let `T` be a non-negative self-adjoint linear relation (`IsNonnegSelfAdjoint`).

* Part 1.  `1 + T` is injective with closed dense range, hence bijective, so it
  has an everywhere-defined inverse `invCLM T`, a positive contraction; and `T`
  is recovered from it, `T = {(C h, h − C h)}` (`rel_eq_of_invCLM_eq`).
* Part 2.  If moreover `T T ⊆ A* Ā`, then with `C = invCLM T` and
  `R = (1 + A* Ā)⁻¹` one has the **bounded** identity
  `R (1 − 2C + 2C²) = C²` (`resCLM_mul_den`): indeed for `x = C h` and
  `u = C x`, the pair `(u, h − 2x + u)` lies in `T T ⊆ A* Ā` and its coordinates
  add up to `h − 2x + 2u`.
* Part 3.  On the spectrum of `C`, which lies in `[0, 1]`, the identity says
  `R = g(C)` with `g t = t²/(2t² − 2t + 1)`, and `g` is inverted on `[0,1]` by the
  continuous `ψ r = √r/(√r + √(1−r))`.  Hence **`C = ψ(R)`** (`invCLM_eq_cfc`) —
  the inverse of `1 + T` is determined by `A` alone.
* Part 4.  Therefore any two such `T` agree; since `absRel A` is one of them,
  **`T = |Ā|`** (`eq_absRel_of_isNonnegSelfAdjoint`), and `|Ā|` is the unique
  non-negative self-adjoint square root of `A* Ā`
  (`absRel_unique_nonneg_sqrt`).

Only `A : D →ₗ[ℂ] F` on a complex Hilbert space is needed; neither density of `D`
nor symmetry of `A` enters the uniqueness statement.
-/

namespace BookProof.PositiveSquareRoot

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare BookProof.VonNeumannCore BookProof.UnboundedPolar
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Part 1 — a non-negative self-adjoint relation and its bounded inverse -/

/-- A linear relation which is self-adjoint and non-negative. -/
structure IsNonnegSelfAdjoint (T : Submodule ℂ (F × F)) : Prop where
  /-- `T* = T`. -/
  adj : adjPairs T = T
  /-- `⟪x, T x⟫ ≥ 0`. -/
  nonneg : ∀ p ∈ T, 0 ≤ (inner ℂ p.1 p.2 : ℂ).re

variable {T T₁ T₂ : Submodule ℂ (F × F)}

theorem symm_inner (hT : IsNonnegSelfAdjoint T) {p q : F × F} (hp : p ∈ T) (hq : q ∈ T) :
    (inner ℂ q.2 p.1 : ℂ) = inner ℂ q.1 p.2 :=
  (hT.adj.ge hp) q hq

/-- `‖x‖² + ‖T x‖² ≤ ‖x + T x‖²`. -/
theorem norm_sq_add_le (hT : IsNonnegSelfAdjoint T) {p : F × F} (hp : p ∈ T) :
    ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 ≤ ‖p.1 + p.2‖ ^ 2 := by
  have hre := hT.nonneg p hp
  have h := norm_add_sq (𝕜 := ℂ) p.1 p.2
  simp only [RCLike.re_to_complex] at h hre
  linarith

theorem norm_fst_le (hT : IsNonnegSelfAdjoint T) {p : F × F} (hp : p ∈ T) :
    ‖p.1‖ ≤ ‖p.1 + p.2‖ := by
  have h := norm_sq_add_le hT hp
  nlinarith [norm_nonneg p.1, norm_nonneg p.2, norm_nonneg (p.1 + p.2)]

theorem norm_snd_le (hT : IsNonnegSelfAdjoint T) {p : F × F} (hp : p ∈ T) :
    ‖p.2‖ ≤ ‖p.1 + p.2‖ := by
  have h := norm_sq_add_le hT hp
  nlinarith [norm_nonneg p.1, norm_nonneg p.2, norm_nonneg (p.1 + p.2)]

/-- `1 + T` is injective. -/
theorem eq_of_add_eq (hT : IsNonnegSelfAdjoint T) {p q : F × F} (hp : p ∈ T) (hq : q ∈ T)
    (hsum : p.1 + p.2 = q.1 + q.2) : p = q := by
  have hd : p - q ∈ T := T.sub_mem hp hq
  have h0 : (p - q).1 + (p - q).2 = 0 := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [show p.1 - q.1 + (p.2 - q.2) = (p.1 + p.2) - (q.1 + q.2) by abel, hsum, sub_self]
  have h1 : ‖(p - q).1‖ ≤ 0 := by
    have := norm_fst_le hT hd; rwa [h0, norm_zero] at this
  have h2 : ‖(p - q).2‖ ≤ 0 := by
    have := norm_snd_le hT hd; rwa [h0, norm_zero] at this
  have hz : p - q = 0 := by
    refine Prod.ext ?_ ?_
    · simpa using norm_le_zero_iff.1 h1
    · simpa using norm_le_zero_iff.1 h2
  exact sub_eq_zero.1 hz

theorem isClosed_rel (hT : IsNonnegSelfAdjoint T) :
    IsClosed ((T : Submodule ℂ (F × F)) : Set (F × F)) := by
  rw [← hT.adj]
  exact adjPairs_isClosed T

/-- The map `(x, w) ↦ x + w`. -/
def sumMap : (F × F) →ₗ[ℂ] F := LinearMap.fst ℂ F F + LinearMap.snd ℂ F F

@[simp] theorem sumMap_apply (p : F × F) : sumMap p = p.1 + p.2 := rfl

section Complete

variable [CompleteSpace F]

/-- The range of `1 + T` is closed. -/
theorem isClosed_rangeSum (hT : IsNonnegSelfAdjoint T) :
    IsClosed (((T.map sumMap : Submodule ℂ F)) : Set F) := by
  refine IsSeqClosed.isClosed ?_
  intro u h hu hlim
  choose p hp hpu using fun n => Submodule.mem_map.1 (hu n)
  have hnorm : ∀ n m : ℕ,
      ‖(p n).1 - (p m).1‖ ≤ ‖u n - u m‖ ∧ ‖(p n).2 - (p m).2‖ ≤ ‖u n - u m‖ := by
    intro n m
    have hd : p n - p m ∈ T := T.sub_mem (hp n) (hp m)
    have e1 : (p n).1 + (p n).2 = u n := hpu n
    have e2 : (p m).1 + (p m).2 = u m := hpu m
    have hsum : (p n - p m).1 + (p n - p m).2 = u n - u m := by
      simp only [Prod.fst_sub, Prod.snd_sub]
      rw [show (p n).1 - (p m).1 + ((p n).2 - (p m).2)
          = ((p n).1 + (p n).2) - ((p m).1 + (p m).2) by abel, e1, e2]
    refine ⟨?_, ?_⟩
    · have := norm_fst_le hT hd; rwa [hsum] at this
    · have := norm_snd_le hT hd; rwa [hsum] at this
  have hcu : CauchySeq u := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcu
  have hc1 : CauchySeq fun n => (p n).1 := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have h1 := (hnorm n m).1
    have h2 := hN n hn m hm
    rw [dist_eq_norm] at h2 ⊢
    linarith
  have hc2 : CauchySeq fun n => (p n).2 := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have h1 := (hnorm n m).2
    have h2 := hN n hn m hm
    rw [dist_eq_norm] at h2 ⊢
    linarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc1
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc2
  have hmem : (x, w) ∈ T := by
    have hlim2 : Filter.Tendsto p Filter.atTop (nhds (x, w)) := hx.prodMk_nhds hw
    exact (isClosed_rel hT).mem_of_tendsto hlim2 (Filter.Eventually.of_forall hp)
  have hsum : x + w = h := by
    have h1 : Filter.Tendsto (fun n => (p n).1 + (p n).2) Filter.atTop (nhds (x + w)) := hx.add hw
    have h2 : Filter.Tendsto (fun n => (p n).1 + (p n).2) Filter.atTop (nhds h) := by
      have : (fun n => (p n).1 + (p n).2) = u := funext hpu
      rw [this]; exact hlim
    exact tendsto_nhds_unique h1 h2
  exact Submodule.mem_map.2 ⟨(x, w), hmem, hsum⟩

omit [CompleteSpace F] in
/-- The orthogonal complement of the range of `1 + T` is trivial. -/
theorem rangeSum_orthogonal_eq_bot (hT : IsNonnegSelfAdjoint T) :
    ((T.map sumMap : Submodule ℂ F))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hadj : (v, -v) ∈ adjPairs T := by
    intro q hq
    have h0 : (inner ℂ (q.1 + q.2) v : ℂ) = 0 :=
      hv _ (Submodule.mem_map.2 ⟨q, hq, rfl⟩)
    rw [inner_add_left] at h0
    simp only [inner_neg_right]
    linear_combination h0
  have hmemT : (v, -v) ∈ T := by rw [← hT.adj]; exact hadj
  have hre := hT.nonneg _ hmemT
  simp only [inner_neg_right, Complex.neg_re] at hre
  have hnn : (inner ℂ v v : ℂ).re = ‖v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [hnn] at hre
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  simpa using this

/-- **`1 + T` is surjective.** -/
theorem exists_add_eq (hT : IsNonnegSelfAdjoint T) (h : F) :
    ∃ p : F × F, p ∈ T ∧ p.1 + p.2 = h := by
  haveI : CompleteSpace ((T.map sumMap : Submodule ℂ F)) :=
    (isClosed_rangeSum hT).completeSpace_coe
  have htop : (T.map sumMap : Submodule ℂ F) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 (rangeSum_orthogonal_eq_bot hT)
  have hmem : h ∈ (T.map sumMap : Submodule ℂ F) := by rw [htop]; trivial
  obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 hmem
  exact ⟨p, hp, hps⟩

omit [CompleteSpace F] in
/-- The quadratic form of a non-negative self-adjoint relation is real. -/
theorem inner_im_eq_zero (hT : IsNonnegSelfAdjoint T) {p : F × F} (hp : p ∈ T) :
    (inner ℂ p.1 p.2 : ℂ).im = 0 := by
  have h := symm_inner hT hp hp
  have h2 : (starRingEnd ℂ) (inner ℂ p.1 p.2 : ℂ) = inner ℂ p.1 p.2 := by
    rw [inner_conj_symm]; exact h
  exact Complex.conj_eq_iff_im.1 h2

/-- The unique solution pair of `x + T x = h`. -/
noncomputable def invPair (hT : IsNonnegSelfAdjoint T) (h : F) : F × F :=
  Classical.choose (exists_add_eq hT h)

theorem invPair_mem (hT : IsNonnegSelfAdjoint T) (h : F) : invPair hT h ∈ T :=
  (Classical.choose_spec (exists_add_eq hT h)).1

theorem invPair_add (hT : IsNonnegSelfAdjoint T) (h : F) :
    (invPair hT h).1 + (invPair hT h).2 = h :=
  (Classical.choose_spec (exists_add_eq hT h)).2

theorem invPair_unique (hT : IsNonnegSelfAdjoint T) {h : F} {p : F × F} (hp : p ∈ T)
    (hsum : p.1 + p.2 = h) : invPair hT h = p :=
  eq_of_add_eq hT (invPair_mem hT h) hp (by rw [invPair_add, hsum])

/-- `(1 + T)⁻¹` as a linear map. -/
noncomputable def invLin (hT : IsNonnegSelfAdjoint T) : F →ₗ[ℂ] F where
  toFun h := (invPair hT h).1
  map_add' h k := by
    have hpair : invPair hT (h + k) = invPair hT h + invPair hT k := by
      refine invPair_unique hT (T.add_mem (invPair_mem hT h) (invPair_mem hT k)) ?_
      simp only [Prod.fst_add, Prod.snd_add]
      rw [show (invPair hT h).1 + (invPair hT k).1 + ((invPair hT h).2 + (invPair hT k).2)
          = ((invPair hT h).1 + (invPair hT h).2) + ((invPair hT k).1 + (invPair hT k).2) by abel,
        invPair_add, invPair_add]
    rw [hpair]; rfl
  map_smul' c h := by
    have hpair : invPair hT (c • h) = c • invPair hT h := by
      refine invPair_unique hT (T.smul_mem c (invPair_mem hT h)) ?_
      simp only [Prod.smul_fst, Prod.smul_snd, ← smul_add]
      rw [invPair_add]
    rw [hpair]; rfl

theorem invLin_apply (hT : IsNonnegSelfAdjoint T) (h : F) : invLin hT h = (invPair hT h).1 := rfl

theorem invLin_mem (hT : IsNonnegSelfAdjoint T) (h : F) : (invLin hT h, h - invLin hT h) ∈ T := by
  have hmem := invPair_mem hT h
  have hsum := invPair_add hT h
  have heq : (invLin hT h, h - invLin hT h) = invPair hT h := by
    rw [invLin_apply, Prod.ext_iff]
    exact ⟨rfl, (eq_sub_of_add_eq' hsum).symm⟩
  rw [heq]; exact hmem

theorem norm_invLin_le (hT : IsNonnegSelfAdjoint T) (h : F) : ‖invLin hT h‖ ≤ ‖h‖ := by
  have := norm_fst_le hT (invPair_mem hT h)
  rwa [invPair_add] at this

/-- **`(1 + T)⁻¹`, a positive contraction.** -/
noncomputable def invCLM (hT : IsNonnegSelfAdjoint T) : F →L[ℂ] F :=
  (invLin hT).mkContinuous 1 (fun h => by simpa using norm_invLin_le hT h)

@[simp] theorem invCLM_apply (hT : IsNonnegSelfAdjoint T) (h : F) : invCLM hT h = invLin hT h := rfl

theorem invCLM_mem (hT : IsNonnegSelfAdjoint T) (h : F) : (invCLM hT h, h - invCLM hT h) ∈ T :=
  invLin_mem hT h

theorem invCLM_eq_of_mem (hT : IsNonnegSelfAdjoint T) {x h : F} (hx : (x, h - x) ∈ T) :
    invCLM hT h = x := by
  have hp := invPair_unique hT hx (show x + (h - x) = h by abel)
  rw [invCLM_apply, invLin_apply, hp]

theorem inner_invCLM_left (hT : IsNonnegSelfAdjoint T) (h k : F) :
    (inner ℂ (invCLM hT h) k : ℂ) = inner ℂ h (invCLM hT k) := by
  have h1 : (invCLM hT h, h - invCLM hT h) ∈ T := invCLM_mem hT h
  have h2 : (invCLM hT k, k - invCLM hT k) ∈ T := invCLM_mem hT k
  have hs : (inner ℂ (k - invCLM hT k) (invCLM hT h) : ℂ)
      = inner ℂ (invCLM hT k) (h - invCLM hT h) := symm_inner hT h1 h2
  have e3 : (inner ℂ (invCLM hT h) (k - invCLM hT k) : ℂ)
      = inner ℂ (h - invCLM hT h) (invCLM hT k) := by
    have := congrArg (starRingEnd ℂ) hs
    rwa [inner_conj_symm, inner_conj_symm] at this
  have e1 : (inner ℂ (invCLM hT h) k : ℂ)
      = inner ℂ (invCLM hT h) (invCLM hT k) + inner ℂ (invCLM hT h) (k - invCLM hT k) := by
    rw [← inner_add_right]; congr 1; abel
  have e2 : (inner ℂ h (invCLM hT k) : ℂ)
      = inner ℂ (invCLM hT h) (invCLM hT k) + inner ℂ (h - invCLM hT h) (invCLM hT k) := by
    rw [← inner_add_left]; congr 1; abel
  rw [e1, e2, e3]

/-- `(1 + T)⁻¹` is self-adjoint. -/
theorem isSelfAdjoint_invCLM (hT : IsNonnegSelfAdjoint T) : IsSelfAdjoint (invCLM hT) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  exact inner_invCLM_left hT x y

/-- **`(1 + T)⁻¹ ≥ 0`.** -/
theorem invCLM_nonneg (hT : IsNonnegSelfAdjoint T) : 0 ≤ invCLM hT := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro h
  have hmem := invCLM_mem hT h
  have hre := hT.nonneg _ hmem
  have him := inner_im_eq_zero hT hmem
  simp only at hre him
  have hsplit : (inner ℂ (invCLM hT h) h : ℂ)
      = inner ℂ (invCLM hT h) (invCLM hT h) + inner ℂ (invCLM hT h) (h - invCLM hT h) := by
    rw [← inner_add_right]; congr 1; abel
  have hxx : (inner ℂ (invCLM hT h) (invCLM hT h) : ℂ) = ((‖invCLM hT h‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hsplit, hxx]
  constructor
  · apply Complex.ext
    · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    · simp only [RCLike.re_to_complex, Complex.ofReal_im, Complex.add_im, him, add_zero]
  · simp only [RCLike.re_to_complex, Complex.add_re, Complex.ofReal_re]
    have hsq : (0:ℝ) ≤ ‖invCLM hT h‖ ^ 2 := by positivity
    linarith

/-- **`(1 + T)⁻¹ ≤ 1`.** -/
theorem invCLM_le_one (hT : IsNonnegSelfAdjoint T) : invCLM hT ≤ 1 := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro h
  have hmem := invCLM_mem hT h
  have hre := hT.nonneg _ hmem
  have him := inner_im_eq_zero hT hmem
  simp only at hre him
  have happ : ((1 : F →L[ℂ] F) - invCLM hT) h = h - invCLM hT h := rfl
  have hs : (inner ℂ (h - invCLM hT h) (invCLM hT h) : ℂ)
      = inner ℂ (invCLM hT h) (h - invCLM hT h) := symm_inner hT hmem hmem
  have hsplit : (inner ℂ (h - invCLM hT h) h : ℂ)
      = inner ℂ (h - invCLM hT h) (invCLM hT h)
        + inner ℂ (h - invCLM hT h) (h - invCLM hT h) := by
    rw [← inner_add_right]; congr 1; abel
  have hww : (inner ℂ (h - invCLM hT h) (h - invCLM hT h) : ℂ)
      = ((‖h - invCLM hT h‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [happ, hsplit, hs, hww]
  constructor
  · apply Complex.ext
    · simp only [RCLike.re_to_complex, Complex.ofReal_re]
    · simp only [RCLike.re_to_complex, Complex.ofReal_im, Complex.add_im, him, add_zero]
  · simp only [RCLike.re_to_complex, Complex.add_re, Complex.ofReal_re]
    have hsq : (0:ℝ) ≤ ‖h - invCLM hT h‖ ^ 2 := by positivity
    linarith

/-- **The relation is recovered from its resolvent.** -/
theorem rel_eq_of_invCLM_eq (hT₁ : IsNonnegSelfAdjoint T₁) (hT₂ : IsNonnegSelfAdjoint T₂)
    (heq : invCLM hT₁ = invCLM hT₂) : T₁ = T₂ := by
  have key : ∀ {S₁ S₂ : Submodule ℂ (F × F)} (h1 : IsNonnegSelfAdjoint S₁)
      (h2 : IsNonnegSelfAdjoint S₂), invCLM h1 = invCLM h2 → S₁ ≤ S₂ := by
    intro S₁ S₂ h1 h2 he p hp
    have hx : invCLM h1 (p.1 + p.2) = p.1 := invCLM_eq_of_mem h1 (by simpa using hp)
    have hmem := invCLM_mem h2 (p.1 + p.2)
    rw [← he, hx] at hmem
    simpa using hmem
  exact le_antisymm (key hT₁ hT₂ heq) (key hT₂ hT₁ heq.symm)

/-! ## Part 2 — the bounded identity forced by `T T ⊆ A* Ā` -/

variable {D : Submodule ℂ F}

/-- **The bounded identity.**  If `T T ⊆ A* Ā` then, with `C = (1 + T)⁻¹` and
`R = (1 + A* Ā)⁻¹`, `R (1 − 2C + 2C²) = C²`. -/
theorem resCLM_mul_den (A : D →ₗ[ℂ] F) (hT : IsNonnegSelfAdjoint T)
    (hsq : ∀ p : F × F, (∃ w, (p.1, w) ∈ T ∧ (w, p.2) ∈ T) → p ∈ factorRel A) :
    resCLM A * (1 - invCLM hT - invCLM hT + invCLM hT * invCLM hT + invCLM hT * invCLM hT)
      = invCLM hT * invCLM hT := by
  refine ContinuousLinearMap.ext fun h => ?_
  have h1 : (invCLM hT h, h - invCLM hT h) ∈ T := invCLM_mem hT h
  have h2 : (invCLM hT (invCLM hT h), invCLM hT h - invCLM hT (invCLM hT h)) ∈ T :=
    invCLM_mem hT (invCLM hT h)
  have h3 : (invCLM hT h - invCLM hT (invCLM hT h),
      (h - invCLM hT h) - (invCLM hT h - invCLM hT (invCLM hT h))) ∈ T := by
    have := T.sub_mem h1 h2
    simpa using this
  have h4 : (invCLM hT (invCLM hT h),
      (h - invCLM hT h) - (invCLM hT h - invCLM hT (invCLM hT h))) ∈ factorRel A :=
    hsq _ ⟨invCLM hT h - invCLM hT (invCLM hT h), h2, h3⟩
  have hsum : invCLM hT (invCLM hT h)
      + ((h - invCLM hT h) - (invCLM hT h - invCLM hT (invCLM hT h)))
      = h - invCLM hT h - invCLM hT h + invCLM hT (invCLM hT h)
        + invCLM hT (invCLM hT h) := by abel
  have hres := resPair_unique (A := A) h4 hsum
  have hval : resCLM A (h - invCLM hT h - invCLM hT h + invCLM hT (invCLM hT h)
      + invCLM hT (invCLM hT h)) = invCLM hT (invCLM hT h) := by
    rw [resCLM_apply, resLin_apply, hres]
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hval

/-! ## Part 3 — the functional calculus: `C = ψ(R)` -/

/-- `g t = t² / (2t² − 2t + 1)`, written without division by a possibly vanishing
denominator: `2t² − 2t + 1 = t² + (1 − t)² > 0`. -/
noncomputable def gFun : ℝ → ℝ := fun t => t * t / (1 - t - t + t * t + t * t)

/-- `ψ r = √r / (√r + √(1 − r))`, the inverse of `g` on `[0, 1]`. -/
noncomputable def psiFun : ℝ → ℝ := fun r => Real.sqrt r / (Real.sqrt r + Real.sqrt (1 - r))

theorem den_pos (t : ℝ) : 0 < 1 - t - t + t * t + t * t := by
  nlinarith [sq_nonneg (t - 1), sq_nonneg t]

@[fun_prop] theorem continuous_den :
    Continuous (fun t : ℝ => 1 - t - t + t * t + t * t) := by fun_prop

@[fun_prop] theorem continuous_gFun : Continuous gFun := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun t => ne_of_gt (den_pos t)

theorem psi_den_pos (r : ℝ) : 0 < Real.sqrt r + Real.sqrt (1 - r) := by
  rcases le_or_gt r 0 with hr | hr
  · have : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.2 (by linarith)
    have := Real.sqrt_nonneg r
    linarith
  · have : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    have := Real.sqrt_nonneg (1 - r)
    linarith

@[fun_prop] theorem continuous_psiFun : Continuous psiFun := by
  refine Continuous.div (Real.continuous_sqrt) ?_ fun r => ne_of_gt (psi_den_pos r)
  exact Real.continuous_sqrt.add (Real.continuous_sqrt.comp (by fun_prop))

/-- `ψ (g t) = t` on `[0, 1]`. -/
theorem psi_gFun {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : psiFun (gFun t) = t := by
  obtain ⟨ht0, ht1⟩ := ht
  have hd : 0 < 1 - t - t + t * t + t * t := den_pos t
  have hdne : (1 - t - t + t * t + t * t) ≠ 0 := ne_of_gt hd
  have hsd : 0 < Real.sqrt (1 - t - t + t * t + t * t) := Real.sqrt_pos.2 hd
  have hs : Real.sqrt (1 - t - t + t * t + t * t) ≠ 0 := ne_of_gt hsd
  have hsq : Real.sqrt (1 - t - t + t * t + t * t) ^ 2 = 1 - t - t + t * t + t * t :=
    Real.sq_sqrt hd.le
  have h1 : Real.sqrt (gFun t) = t / Real.sqrt (1 - t - t + t * t + t * t) := by
    have hrw : gFun t = (t / Real.sqrt (1 - t - t + t * t + t * t)) ^ 2 := by
      rw [div_pow, hsq, gFun, sq]
    rw [hrw]
    exact Real.sqrt_sq (by positivity)
  have h2 : Real.sqrt (1 - gFun t) = (1 - t) / Real.sqrt (1 - t - t + t * t + t * t) := by
    have hval : 1 - gFun t = (1 - t) * (1 - t) / (1 - t - t + t * t + t * t) := by
      rw [gFun, eq_div_iff hdne, sub_mul, div_mul_cancel₀ _ hdne]
      ring
    have hrw : 1 - gFun t = ((1 - t) / Real.sqrt (1 - t - t + t * t + t * t)) ^ 2 := by
      rw [div_pow, hsq, hval, sq]
    rw [hrw]
    refine Real.sqrt_sq ?_
    have h1t : (0:ℝ) ≤ 1 - t := by linarith
    positivity
  rw [psiFun, h1, h2, ← add_div, show t + (1 - t) = 1 by ring, one_div, div_div,
    mul_inv_cancel₀ hs, div_one]

section Cfc

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `1 − 2C + 2C²` as a continuous functional calculus expression. -/
theorem cfc_den (C : H →L[ℂ] H) (hC : 0 ≤ C) :
    cfc (fun t : ℝ => 1 - t - t + t * t + t * t) C
      = 1 - C - C + C * C + C * C := by
  have hsa : IsSelfAdjoint C := hC.isSelfAdjoint
  rw [cfc_add (R := ℝ) C (fun t : ℝ => 1 - t - t + t * t) (fun t : ℝ => t * t),
    cfc_add (R := ℝ) C (fun t : ℝ => 1 - t - t) (fun t : ℝ => t * t),
    cfc_sub (R := ℝ) (fun t : ℝ => 1 - t) (fun t : ℝ => t) C,
    cfc_sub (R := ℝ) (fun _ : ℝ => 1) (fun t : ℝ => t) C,
    cfc_mul (R := ℝ) (fun t : ℝ => t) (fun t : ℝ => t) C,
    cfc_const_one ℝ C, cfc_id' ℝ C]

theorem isUnit_den (C : H →L[ℂ] H) (hC : 0 ≤ C) :
    IsUnit (1 - C - C + C * C + C * C : H →L[ℂ] H) := by
  have hsa : IsSelfAdjoint C := hC.isSelfAdjoint
  rw [← cfc_den C hC,
    isUnit_cfc_iff (R := ℝ) (fun t : ℝ => 1 - t - t + t * t + t * t) C
      continuous_den.continuousOn hsa]
  intro t _
  exact ne_of_gt (den_pos t)

theorem cfc_gFun_mul_den (C : H →L[ℂ] H) (hC : 0 ≤ C) :
    cfc gFun C * (1 - C - C + C * C + C * C) = C * C := by
  have hsa : IsSelfAdjoint C := hC.isSelfAdjoint
  have hmul : cfc (fun t : ℝ => gFun t * (1 - t - t + t * t + t * t)) C
      = cfc gFun C * cfc (fun t : ℝ => 1 - t - t + t * t + t * t) C := by
    rw [cfc_mul (R := ℝ) _ _ C]
  have hcongr : cfc (fun t : ℝ => gFun t * (1 - t - t + t * t + t * t)) C
      = cfc (fun t : ℝ => t * t) C := by
    refine cfc_congr fun t _ => ?_
    rw [gFun, div_mul_cancel₀ _ (ne_of_gt (den_pos t))]
  have hsquare : cfc (fun t : ℝ => t * t) C = C * C := by
    rw [cfc_mul (R := ℝ) (fun t : ℝ => t) (fun t : ℝ => t) C, cfc_id' ℝ C]
  rw [← cfc_den C hC, ← hmul, hcongr, hsquare]

/-- The bounded identity `R (1 − 2C + 2C²) = C²` forces `R = g(C)`. -/
theorem eq_cfc_gFun (C R : H →L[ℂ] H) (hC : 0 ≤ C)
    (hid : R * (1 - C - C + C * C + C * C) = C * C) : R = cfc gFun C := by
  have hcancel : R * (1 - C - C + C * C + C * C)
      = cfc gFun C * (1 - C - C + C * C + C * C) := by
    rw [hid, cfc_gFun_mul_den C hC]
  exact (isUnit_den C hC).mul_right_cancel hcancel

/-- Hence `C = ψ(R)`: the inverse of `1 + T` is determined by `R`. -/
theorem eq_cfc_psiFun (C R : H →L[ℂ] H) (hC : 0 ≤ C) (hC1 : C ≤ 1)
    (hid : R * (1 - C - C + C * C + C * C) = C * C) : C = cfc psiFun R := by
  have hsa : IsSelfAdjoint C := hC.isSelfAdjoint
  have hg := eq_cfc_gFun C R hC hid
  have hcomp : cfc (psiFun ∘ gFun) C = cfc psiFun (cfc gFun C) :=
    cfc_comp psiFun gFun C hsa continuous_psiFun.continuousOn continuous_gFun.continuousOn
  have hspec := UnboundedPolar.spectrum_subset_Icc hC hC1
  have hcongr : cfc (psiFun ∘ gFun) C = cfc (id : ℝ → ℝ) C :=
    cfc_congr fun t ht => psi_gFun (hspec ht)
  rw [cfc_id ℝ C] at hcongr
  rw [hg, ← hcomp, hcongr]

end Cfc

/-! ## Part 4 — uniqueness of the non-negative square root -/

/-- With `T T ⊆ A* Ā`, the resolvent of `T` is `ψ` of the resolvent of `A* Ā`. -/
theorem invCLM_eq_cfc (A : D →ₗ[ℂ] F) (hT : IsNonnegSelfAdjoint T)
    (hsq : ∀ p : F × F, (∃ w, (p.1, w) ∈ T ∧ (w, p.2) ∈ T) → p ∈ factorRel A) :
    invCLM hT = cfc psiFun (resCLM A) :=
  eq_cfc_psiFun (invCLM hT) (resCLM A) (invCLM_nonneg hT) (invCLM_le_one hT)
    (resCLM_mul_den A hT hsq)

/-- `|Ā|` is a non-negative self-adjoint relation. -/
theorem isNonnegSelfAdjoint_absRel (A : D →ₗ[ℂ] F) : IsNonnegSelfAdjoint (absRel A) where
  adj := adjPairs_absRel A
  nonneg := by
    intro p hp
    have h := absRel_quadForm_nonneg A hp
    have hre : 0 ≤ (inner ℂ p.2 p.1 : ℂ).re := by
      have := Complex.le_def.1 h
      simpa using this.1
    have hconj : (inner ℂ p.2 p.1 : ℂ) = (starRingEnd ℂ) (inner ℂ p.1 p.2 : ℂ) :=
      (inner_conj_symm _ _).symm
    rwa [hconj, Complex.conj_re] at hre

/-- **Uniqueness of the non-negative self-adjoint square root of `A* Ā`.**  Every
non-negative self-adjoint relation whose square is contained in `A* Ā` is `|Ā|`. -/
theorem eq_absRel_of_isNonnegSelfAdjoint (A : D →ₗ[ℂ] F) (hT : IsNonnegSelfAdjoint T)
    (hsq : ∀ p : F × F, (∃ w, (p.1, w) ∈ T ∧ (w, p.2) ∈ T) → p ∈ factorRel A) :
    T = absRel A := by
  have habs : ∀ p : F × F,
      (∃ w, (p.1, w) ∈ absRel A ∧ (w, p.2) ∈ absRel A) → p ∈ factorRel A := by
    intro p hp
    have hmem : p ∈ {q : F × F | ∃ w, (q.1, w) ∈ absRel A ∧ (w, q.2) ∈ absRel A} := hp
    rw [absRel_comp_self A] at hmem
    exact hmem
  exact rel_eq_of_invCLM_eq hT (isNonnegSelfAdjoint_absRel A)
    ((invCLM_eq_cfc A hT hsq).trans (invCLM_eq_cfc A (isNonnegSelfAdjoint_absRel A) habs).symm)

/-- **`|Ā| = (A* Ā)^{1/2}` is the unique non-negative self-adjoint square root.** -/
theorem absRel_unique_nonneg_sqrt (A : D →ₗ[ℂ] F) :
    IsNonnegSelfAdjoint (absRel A) ∧
      {p : F × F | ∃ w, (p.1, w) ∈ absRel A ∧ (w, p.2) ∈ absRel A}
        = (factorRel A : Set (F × F)) ∧
      ∀ T : Submodule ℂ (F × F), IsNonnegSelfAdjoint T →
        {p : F × F | ∃ w, (p.1, w) ∈ T ∧ (w, p.2) ∈ T} = (factorRel A : Set (F × F)) →
        T = absRel A := by
  refine ⟨isNonnegSelfAdjoint_absRel A, absRel_comp_self A, fun S hS hsq => ?_⟩
  refine eq_absRel_of_isNonnegSelfAdjoint A hS fun p hp => ?_
  have hmem : p ∈ {q : F × F | ∃ w, (q.1, w) ∈ S ∧ (w, q.2) ∈ S} := hp
  rw [hsq] at hmem
  exact hmem

end Complete

end BookProof.PositiveSquareRoot


