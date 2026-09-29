-- Prove2me | Definitions.Def_ChapterComplexShiftCore
-- name    : ChapterComplexShiftCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:17:31.886646+00:00
-- url     : https://prove2.me/theorems/acad4a3d-6f7a-4ef4-bbb1-50adf16ba673
-- title:
--   The abstract core of `BookProof.ChapterHashimotoComplexShifts`: for a symmetric operator `A` on a domain of a complex Hi ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ComplexShiftCore`, source chapter `BookProof/ChapterComplexShiftCore.lean`).
--
--   The abstract core of `BookProof.ChapterHashimotoComplexShifts`: for a symmetric operator `A` on a domain of a complex Hilbert space and a shift `γ` off the real axis, `‖(γ − A)x‖ ≥ |Im γ| ‖x‖` (`norm_cshiftMap_ge`), so `γ − A` is injective with closed range, and for a self-adjoint `A` it is bijective (`cshiftMap_surjective`).
--
--   This material depends on `BookProof.ChapterFarisLavineCore` and Mathlib alone; it is separated out so that the unbounded-operator chapters that need only the shift bound do not have to build the whole SIRK/Hashimoto development.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterComplexShiftCore.lean

import Mathlib
import Definitions.Def_ChapterFarisLavineCore

/-!
# The non-real shift `γ − A` of a symmetric operator

The abstract core of `BookProof.ChapterHashimotoComplexShifts`: for a symmetric
operator `A` on a domain of a complex Hilbert space and a shift `γ` off the real
axis, `‖(γ − A)x‖ ≥ |Im γ| ‖x‖` (`norm_cshiftMap_ge`), so `γ − A` is injective
with closed range, and for a self-adjoint `A` it is bijective
(`cshiftMap_surjective`).

This material depends on `BookProof.ChapterFarisLavineCore` and Mathlib alone; it
is separated out so that the unbounded-operator chapters that need only the shift
bound do not have to build the whole SIRK/Hashimoto development.
-/

namespace BookProof.HashimotoShiftInvert

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

theorem inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [inner_im_swap (T x) (x : F)] at h
  linarith

theorem quadForm_im (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by
  rw [inner_im_swap (N x) (x : F), inner_apply_self_im N hN x, neg_zero]

open Filter Topology

/-! ## A self-adjoint operator is closed -/

section Closed

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

/-- **A self-adjoint operator is closed.**  Clause 4 of
`IsPositiveSelfAdjointExtension` ("every vector that behaves like a domain
vector is one") makes the graph of `A` closed. -/
theorem closed_of_selfAdjointCriterion {A : Dom →ₗ[ℂ] F}
    (hsym : SymmetricOn Dom A)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {ι : Type*} {l : Filter ι} [l.NeBot] {x : ι → Dom} {p : F} {q : F}
    (hx : Tendsto (fun n => ((x n : F))) l (nhds p))
    (hA : Tendsto (fun n => A (x n)) l (nhds q)) :
    ∃ h : p ∈ Dom, A ⟨p, h⟩ = q := by
  refine hsa p q fun v => ?_
  have h1 : Tendsto (fun n => (inner ℂ (A v) ((x n : F)) : ℂ)) l (nhds (inner ℂ (A v) p)) :=
    tendsto_const_nhds.inner hx
  have h2 : Tendsto (fun n => (inner ℂ ((v : F)) (A (x n)) : ℂ)) l (nhds (inner ℂ (v : F) q)) :=
    tendsto_const_nhds.inner hA
  have heq : (fun n => (inner ℂ (A v) ((x n : F)) : ℂ))
      = fun n => (inner ℂ (v : F) (A (x n)) : ℂ) :=
    funext fun n => hsym v (x n)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Closed

/-! ## Part 1 — the non-real shift bound -/

section CBound

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

/-- The shifted operator `γ I − A` on the domain of `A`, for a **complex** shift
`γ`.  This is the operator the Hashimoto/SIRK algorithm inverts. -/
noncomputable def cshiftMap (A : Dom →ₗ[ℂ] F) (γ : ℂ) : Dom →ₗ[ℂ] F :=
  γ • Dom.subtype - A

@[simp] theorem cshiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℂ) (x : Dom) :
    cshiftMap A γ x = γ • (x : F) - A x := rfl

/-- **The non-real shift bound.**  For a *symmetric* operator `A` and a shift
`γ` off the real axis, `‖(γ − A)x‖ ≥ |Im γ| ‖x‖`.  No positivity of `A` and no
boundedness are used: the imaginary part of the shift alone bounds `γ − A`
below, which is why the resolvent the algorithm iterates is bounded. -/
theorem norm_cshiftMap_ge {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A) (γ : ℂ) (x : Dom) :
    |γ.im| * ‖(x : F)‖ ≤ ‖cshiftMap A γ x‖ := by
  have him : (inner ℂ (x : F) (cshiftMap A γ x) : ℂ).im = γ.im * ‖(x : F)‖ ^ 2 := by
    rw [cshiftMap_apply, inner_sub_right, inner_smul_right, Complex.sub_im, Complex.mul_im,
      inner_self_eq_norm_sq_to_K, quadForm_im A hsym x]
    simp [← Complex.ofReal_pow]
  have h2 : |(inner ℂ (x : F) (cshiftMap A γ x) : ℂ).im| ≤ ‖(x : F)‖ * ‖cshiftMap A γ x‖ :=
    le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm _ _)
  rw [him, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖(x : F)‖ ^ 2)] at h2
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]; simp
  · nlinarith [abs_nonneg γ.im]

/-- A non-real shift makes the shifted operator injective, for any symmetric `A`. -/
theorem cshiftMap_injective {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    {γ : ℂ} (hγ : γ.im ≠ 0) : Function.Injective (cshiftMap A γ) := by
  intro x y hxy
  have h : |γ.im| * ‖((x - y : Dom) : F)‖ ≤ ‖cshiftMap A γ (x - y)‖ := norm_cshiftMap_ge hsym _ _
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hx : ‖((x - y : Dom) : F)‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg ((x - y : Dom) : F)]) (norm_nonneg _)
  have hz : x - y = 0 := Subtype.ext (by simpa using (by simpa using hx : ((x - y : Dom) : F) = 0))
  exact sub_eq_zero.mp hz

end CBound

/-! ## Part 2 — for a self-adjoint operator a non-real shift is a bijection -/

section CSurjective

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

/-- The range of `γ − A`, as a submodule. -/
noncomputable def cshiftRange (A : Dom →ₗ[ℂ] F) (γ : ℂ) : Submodule ℂ F :=
  LinearMap.range (cshiftMap A γ)

/-- **The range of `γ − A` is closed** — because `γ − A` is bounded below by
`|Im γ|` and a self-adjoint operator is closed. -/
theorem cshiftRange_isClosed {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℂ} (hγ : γ.im ≠ 0) : IsClosed ((cshiftRange A γ : Submodule ℂ F) : Set F) := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  refine IsSeqClosed.isClosed ?_
  intro u p hu hup
  choose x hx using hu
  have hcauchy : CauchySeq (fun n => ((x n : F))) := by
    have hucauchy : CauchySeq u := hup.cauchySeq
    rw [Metric.cauchySeq_iff] at hucauchy ⊢
    intro eps heps
    obtain ⟨N, hN⟩ := hucauchy (|γ.im| * eps) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : |γ.im| * ‖((x m - x n : Dom) : F)‖ ≤ ‖cshiftMap A γ (x m - x n)‖ :=
      norm_cshiftMap_ge hsym _ _
    rw [map_sub, hx m, hx n] at hb
    have hlt : ‖u m - u n‖ < |γ.im| * eps := by
      have hd := hN m hm n hn
      rwa [dist_eq_norm] at hd
    have hkey : |γ.im| * ‖((x m : F)) - ((x n : F))‖ < |γ.im| * eps := by
      refine lt_of_le_of_lt ?_ hlt
      simpa using hb
    rw [dist_eq_norm]
    exact lt_of_mul_lt_mul_left hkey hpos.le
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hAconv : Tendsto (fun n => A (x n)) atTop (nhds (γ • w - p)) := by
    have hval : ∀ n, A (x n) = γ • ((x n : F)) - u n := by
      intro n
      have hn := hx n
      simp only [cshiftMap_apply] at hn
      rw [← hn]; abel
    simp only [hval]
    exact (hw.const_smul γ).sub hup
  obtain ⟨hwmem, hAw⟩ := closed_of_selfAdjointCriterion hsym hsa hw hAconv
  refine ⟨⟨w, hwmem⟩, ?_⟩
  simp only [cshiftMap_apply, hAw]
  abel

omit [CompleteSpace F] in
/-- **The range of `γ − A` is dense** — a vector orthogonal to it would satisfy
`A w = γ̄ w`, and the expectation of a symmetric operator is real, so `w = 0`
whenever `Im γ ≠ 0`.  Note that *no positivity* is needed; this is what the
non-real shift buys. -/
theorem cshiftRange_orthogonal_eq_bot {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℂ} (hγ : γ.im ≠ 0) : (cshiftRange A γ)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hip : ∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) ((starRingEnd ℂ) γ • w) := by
    intro v
    have hmem : cshiftMap A γ v ∈ cshiftRange A γ := ⟨v, rfl⟩
    have h0 : (inner ℂ (cshiftMap A γ v) w : ℂ) = 0 := hw _ hmem
    rw [cshiftMap_apply, inner_sub_left, inner_smul_left] at h0
    rw [inner_smul_right]
    linear_combination -h0
  obtain ⟨hwmem, hAw⟩ := hsa w ((starRingEnd ℂ) γ • w) hip
  have hq0 : (inner ℂ w (A ⟨w, hwmem⟩) : ℂ).im = 0 := quadForm_im A hsym ⟨w, hwmem⟩
  rw [hAw, inner_smul_right, inner_self_eq_norm_sq_to_K] at hq0
  have hq : -γ.im * ‖w‖ ^ 2 = 0 := by
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im] at hq0
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im] at hq0
    linarith
  have hzero : ‖w‖ = 0 := by
    rcases mul_eq_zero.mp hq with h | h
    · exact absurd (by linarith : γ.im = 0) hγ
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  simpa using hzero

/-- **`γ − A` is surjective** for self-adjoint `A` and non-real `γ`. -/
theorem cshiftMap_surjective {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    (hsa : ∀ w u : F, (∀ v : Dom, (inner ℂ (A v) w : ℂ) = inner ℂ (v : F) u) →
      ∃ h : w ∈ Dom, A ⟨w, h⟩ = u)
    {γ : ℂ} (hγ : γ.im ≠ 0) : Function.Surjective (cshiftMap A γ) := by
  have hclosed : IsClosed ((cshiftRange A γ : Submodule ℂ F) : Set F) :=
    cshiftRange_isClosed hsym hsa hγ
  haveI : CompleteSpace (cshiftRange A γ) := hclosed.completeSpace_coe
  have htop : cshiftRange A γ = ⊤ := by
    have h1 := Submodule.orthogonal_orthogonal (cshiftRange A γ)
    rw [cshiftRange_orthogonal_eq_bot hsym hsa hγ, Submodule.bot_orthogonal_eq_top] at h1
    exact h1.symm
  intro u
  have hmem : u ∈ cshiftRange A γ := by rw [htop]; trivial
  exact hmem

end CSurjective

end BookProof.HashimotoShiftInvert


