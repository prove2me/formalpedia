-- Prove2me | Definitions.Def_ChapterStoneResolvent
-- name    : ChapterStoneResolvent
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:23:11.092722+00:00
-- url     : https://prove2.me/theorems/706252c1-b684-4f09-aedc-a056dc6dc49a
-- title:
--   This module is the first of three that together prove **Stone's theorem in full generality**: every densely defined self ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StoneResolvent`, source chapter `BookProof/ChapterStoneResolvent.lean`).
--
--   This module is the first of three that together prove **Stone's theorem in full generality**: every densely defined self-adjoint operator `A` on a complex Hilbert space generates a strongly continuous one-parameter unitary group `t ↦ e^{-itA}`.
--
--   Here we build the analytic core: the **resolvents** `(A - i l)⁻¹` for real `l ≠ 0`.
--
--   * `UnboundedSelfAdjoint` bundles a dense domain, the operator, symmetry and self-adjointness (in the sense of `BookProof.ChapterUnitaryTransport`). * `UnboundedSelfAdjoint.closed_graph` — a self-adjoint operator is closed. * `UnboundedSelfAdjoint.shift_bijective` — `A - i l` is a bijection from the domain onto the whole space (closed range with trivial orthogonal complement). * `UnboundedSelfAdjoint.res` / `resCLM` — the resolvent as a linear map into the domain and as a bounded operator, with `‖(A - i l)⁻¹‖ ≤ 1/|l|`. * `UnboundedSelfAdjoint.inner_res` — `((A - il)⁻¹)^* = (A + il)⁻¹`. * `UnboundedSelfAdjoint.res_comm` — resolvents at different parameters commute.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneResolvent.lean

import Mathlib
import Definitions.Def_ChapterUnitaryTransport
open BookProof.ChapterUnitaryTransport

/-!
# The general Stone theorem, part I: resolvents of an unbounded self-adjoint operator

This module is the first of three that together prove **Stone's theorem in full
generality**: every densely defined self-adjoint operator `A` on a complex
Hilbert space generates a strongly continuous one-parameter unitary group
`t ↦ e^{-itA}`.

Here we build the analytic core: the **resolvents** `(A - i l)⁻¹` for real
`l ≠ 0`.

* `UnboundedSelfAdjoint` bundles a dense domain, the operator, symmetry and
  self-adjointness (in the sense of `BookProof.ChapterUnitaryTransport`).
* `UnboundedSelfAdjoint.closed_graph` — a self-adjoint operator is closed.
* `UnboundedSelfAdjoint.shift_bijective` — `A - i l` is a bijection from the
  domain onto the whole space (closed range with trivial orthogonal
  complement).
* `UnboundedSelfAdjoint.res` / `resCLM` — the resolvent as a linear map into the
  domain and as a bounded operator, with `‖(A - i l)⁻¹‖ ≤ 1/|l|`.
* `UnboundedSelfAdjoint.inner_res` — `((A - il)⁻¹)^* = (A + il)⁻¹`.
* `UnboundedSelfAdjoint.res_comm` — resolvents at different parameters commute.

Everything is `sorry`-free and `axiom`-free.
-/

open scoped InnerProductSpace
open Filter Topology

namespace BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An **unbounded self-adjoint operator** on a complex Hilbert space: a dense
domain, a linear operator on it, symmetry, and equality of the adjoint domain
with the domain. -/
structure UnboundedSelfAdjoint (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The (dense) domain of definition. -/
  domain : Submodule ℂ H
  /-- The operator itself. -/
  op : domain →ₗ[ℂ] H
  /-- The domain is dense. -/
  denseDomain : Dense ((domain : Submodule ℂ H) : Set H)
  /-- The operator is symmetric. -/
  symmetric : IsSymmetricOn domain op
  /-- The adjoint domain is exactly the domain. -/
  selfAdjoint : IsSelfAdjointOn domain op

namespace UnboundedSelfAdjoint

variable (T : UnboundedSelfAdjoint H)

/-! ## Consequences of self-adjointness -/

/-- If `ψ ↦ ⟪Aψ, φ⟫` is represented by `η`, then `φ` lies in the domain. -/
theorem mem_domain_of_inner {phi eta : H}
    (h : ∀ psi : T.domain, ⟪T.op psi, phi⟫_ℂ = ⟪(psi : H), eta⟫_ℂ) :
    phi ∈ T.domain := by
  have hmem : phi ∈ adjointDomain T.domain T.op := ⟨eta, h⟩
  rw [T.selfAdjoint] at hmem
  exact hmem

/-- ... and then the representing vector is `A φ`. -/
theorem op_eq_of_inner {phi eta : H} (hphi : phi ∈ T.domain)
    (h : ∀ psi : T.domain, ⟪T.op psi, phi⟫_ℂ = ⟪(psi : H), eta⟫_ℂ) :
    T.op ⟨phi, hphi⟩ = eta := by
  have key : ∀ psi : T.domain, ⟪eta - T.op ⟨phi, hphi⟩, (psi : H)⟫_ℂ = 0 := by
    intro psi
    have h1 := h psi
    have h2 := T.symmetric psi ⟨phi, hphi⟩
    have h3 : ⟪(psi : H), eta - T.op ⟨phi, hphi⟩⟫_ℂ = 0 := by
      rw [inner_sub_right, ← h1, h2]
      simp
    rwa [inner_eq_zero_symm] at h3
  have h0 := T.denseDomain.eq_zero_of_inner_left (𝕜 := ℂ)
    (x := eta - T.op ⟨phi, hphi⟩) (fun v hv => key ⟨v, hv⟩)
  exact (sub_eq_zero.mp h0).symm

/-- A self-adjoint operator is **closed**: its graph is closed. -/
theorem closed_graph {xs : ℕ → T.domain} {x y : H}
    (h1 : Tendsto (fun n => ((xs n : H))) atTop (𝓝 x))
    (h2 : Tendsto (fun n => T.op (xs n)) atTop (𝓝 y)) :
    ∃ h : x ∈ T.domain, T.op ⟨x, h⟩ = y := by
  have key : ∀ psi : T.domain, ⟪T.op psi, x⟫_ℂ = ⟪(psi : H), y⟫_ℂ := by
    intro psi
    have ha : Tendsto (fun n => ⟪T.op psi, ((xs n : H))⟫_ℂ) atTop (𝓝 ⟪T.op psi, x⟫_ℂ) :=
      (tendsto_const_nhds.inner h1 : _)
    have hb : Tendsto (fun n => ⟪(psi : H), T.op (xs n)⟫_ℂ) atTop (𝓝 ⟪(psi : H), y⟫_ℂ) :=
      (tendsto_const_nhds.inner h2 : _)
    have hab : (fun n => ⟪T.op psi, ((xs n : H))⟫_ℂ) = fun n => ⟪(psi : H), T.op (xs n)⟫_ℂ := by
      funext n
      exact T.symmetric psi (xs n)
    rw [hab] at ha
    exact tendsto_nhds_unique ha hb
  exact ⟨T.mem_domain_of_inner key, T.op_eq_of_inner _ key⟩

/-! ## The shifted operator `A - i l` -/

/-- The shifted operator `A - i l` on the domain. -/
noncomputable def shift (l : ℝ) : T.domain →ₗ[ℂ] H :=
  T.op - ((l : ℂ) * Complex.I) • T.domain.subtype

theorem shift_apply (l : ℝ) (x : T.domain) :
    T.shift l x = T.op x - ((l : ℂ) * Complex.I) • (x : H) := rfl

/-- `⟪Ax, x⟫` is real for a symmetric operator. -/
theorem inner_op_self_re (x : T.domain) :
    (⟪T.op x, (x : H)⟫_ℂ : ℂ) = ((RCLike.re ⟪T.op x, (x : H)⟫_ℂ : ℝ) : ℂ) := by
  have h := T.symmetric x x
  have h2 : ⟪(x : H), T.op x⟫_ℂ = starRingEnd ℂ ⟪T.op x, (x : H)⟫_ℂ := by
    rw [← inner_conj_symm]
  rw [h2] at h
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

/-- The Pythagoras identity `‖(A - il)x‖² = ‖Ax‖² + l²‖x‖²`. -/
theorem norm_shift_sq (l : ℝ) (x : T.domain) :
    ‖T.shift l x‖ ^ 2 = ‖T.op x‖ ^ 2 + l ^ 2 * ‖(x : H)‖ ^ 2 := by
  have h1 : ‖T.op x - ((l : ℂ) * Complex.I) • (x : H)‖ ^ 2
      = ‖T.op x‖ ^ 2 - 2 * RCLike.re ⟪T.op x, ((l : ℂ) * Complex.I) • (x : H)⟫_ℂ
        + ‖((l : ℂ) * Complex.I) • (x : H)‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) _ _
  have h2 : RCLike.re ⟪T.op x, ((l : ℂ) * Complex.I) • (x : H)⟫_ℂ = 0 := by
    rw [inner_smul_right, T.inner_op_self_re x]
    simp
  have h3 : ‖((l : ℂ) * Complex.I) • (x : H)‖ = |l| * ‖(x : H)‖ := by
    rw [norm_smul]
    simp
  rw [shift_apply, h1, h2, h3]
  rw [mul_pow, sq_abs]
  ring

theorem norm_shift_ge (l : ℝ) (x : T.domain) :
    |l| * ‖(x : H)‖ ≤ ‖T.shift l x‖ := by
  have h := T.norm_shift_sq l x
  nlinarith [norm_nonneg (T.shift l x), abs_nonneg l, norm_nonneg (x : H),
    sq_nonneg ‖T.op x‖, sq_abs l, mul_nonneg (abs_nonneg l) (norm_nonneg (x : H))]

theorem shift_injective {l : ℝ} (hl : l ≠ 0) : Function.Injective (T.shift l) := by
  intro a b hab
  have h : T.shift l (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h2 := T.norm_shift_ge l (a - b)
  rw [h] at h2
  have h3 : ‖((a : H) - (b : H))‖ ≤ 0 := by
    have habs : (0 : ℝ) < |l| := abs_pos.mpr hl
    have hco : ((a - b : T.domain) : H) = (a : H) - (b : H) := rfl
    have h4 : |l| * ‖(a : H) - (b : H)‖ ≤ 0 := by
      rw [← hco]; simpa using h2
    nlinarith [norm_nonneg ((a : H) - (b : H))]
  have : ((a : H)) = (b : H) := by
    have := le_antisymm h3 (norm_nonneg _)
    rwa [norm_sub_eq_zero_iff] at this
  exact Subtype.ext this

end UnboundedSelfAdjoint

variable [CompleteSpace H]

namespace UnboundedSelfAdjoint

variable (T : UnboundedSelfAdjoint H)

theorem shift_range_isClosed {l : ℝ} (hl : l ≠ 0) :
    IsClosed ((LinearMap.range (T.shift l) : Submodule ℂ H) : Set H) := by
  apply IsSeqClosed.isClosed
  intro ys z hys hz
  choose xs hxs using fun n => LinearMap.mem_range.mp (hys n)
  have habs : (0 : ℝ) < |l| := abs_pos.mpr hl
  have hbound : ∀ m n : ℕ, |l| * ‖((xs m : H)) - ((xs n : H))‖ ≤ ‖ys m - ys n‖ := by
    intro m n
    have h := T.norm_shift_ge l (xs m - xs n)
    rw [map_sub, hxs m, hxs n] at h
    simpa using h
  have hCauchy : CauchySeq (fun n => ((xs n : H))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hys' : CauchySeq ys := hz.cauchySeq
    rw [Metric.cauchySeq_iff] at hys'
    obtain ⟨N, hN⟩ := hys' (ε * |l|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hbound m n
    nlinarith [norm_nonneg (((xs m : H)) - ((xs n : H)))]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hop : Tendsto (fun n => T.op (xs n)) atTop (𝓝 (z + ((l : ℂ) * Complex.I) • x)) := by
    have : ∀ n, T.op (xs n) = ys n + ((l : ℂ) * Complex.I) • ((xs n : H)) := by
      intro n
      have := hxs n
      rw [shift_apply] at this
      rw [← this]
      abel
    simp only [this]
    exact hz.add ((tendsto_const_nhds).smul hx)
  obtain ⟨hmem, hval⟩ := T.closed_graph hx hop
  refine LinearMap.mem_range.mpr ⟨⟨x, hmem⟩, ?_⟩
  rw [shift_apply, hval]
  abel

omit [CompleteSpace H] in
theorem shift_range_orthogonal {l : ℝ} (hl : l ≠ 0) :
    (LinearMap.range (T.shift l))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro phi hphi
  rw [Submodule.mem_orthogonal] at hphi
  have key : ∀ psi : T.domain,
      ⟪T.op psi, phi⟫_ℂ = ⟪(psi : H), (-((l : ℂ) * Complex.I)) • phi⟫_ℂ := by
    intro psi
    have h0 := hphi (T.shift l psi) (LinearMap.mem_range_self _ _)
    rw [shift_apply, inner_sub_left, sub_eq_zero] at h0
    rw [h0, inner_smul_left, inner_smul_right]
    simp [Complex.conj_I]
  have hmem := T.mem_domain_of_inner key
  have hop := T.op_eq_of_inner hmem key
  have h1 := T.norm_shift_sq l ⟨phi, hmem⟩
  rw [shift_apply, hop] at h1
  have hlhs : ‖(-((l : ℂ) * Complex.I)) • phi - ((l : ℂ) * Complex.I) • phi‖
      = 2 * |l| * ‖phi‖ := by
    have : (-((l : ℂ) * Complex.I)) • phi - ((l : ℂ) * Complex.I) • phi
        = ((-2 : ℂ) * ((l : ℂ) * Complex.I)) • phi := by
      module
    rw [this, norm_smul]
    simp [mul_assoc]
  have hrhs : ‖(-((l : ℂ) * Complex.I)) • phi‖ = |l| * ‖phi‖ := by
    rw [norm_smul]; simp
  rw [hlhs, hrhs] at h1
  have hco : ‖((⟨phi, hmem⟩ : T.domain) : H)‖ = ‖phi‖ := rfl
  rw [hco] at h1
  have hphi0 : ‖phi‖ = 0 := by
    have habs : (0 : ℝ) < |l| := abs_pos.mpr hl
    have hkey : |l| ^ 2 * ‖phi‖ ^ 2 = l ^ 2 * ‖phi‖ ^ 2 := by rw [sq_abs]
    have hX : l ^ 2 * ‖phi‖ ^ 2 = 0 := by nlinarith [h1, hkey]
    have hl2 : (0 : ℝ) < l ^ 2 := by nlinarith [sq_abs l]
    have hN : ‖phi‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hX with h | h
      · exact absurd h (ne_of_gt hl2)
      · exact h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hN
  simpa using hphi0

theorem shift_surjective {l : ℝ} (hl : l ≠ 0) : Function.Surjective (T.shift l) := by
  have hclosed := T.shift_range_isClosed hl
  haveI : CompleteSpace (LinearMap.range (T.shift l)) := hclosed.completeSpace_coe
  haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace (LinearMap.range (T.shift l))
  have htop : LinearMap.range (T.shift l) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp (T.shift_range_orthogonal hl)
  exact LinearMap.range_eq_top.mp htop

theorem shift_bijective {l : ℝ} (hl : l ≠ 0) : Function.Bijective (T.shift l) :=
  ⟨T.shift_injective hl, T.shift_surjective hl⟩

/-! ## The resolvent -/

/-- `A - i l` as a linear equivalence from the domain onto the space. -/
noncomputable def shiftEquiv {l : ℝ} (hl : l ≠ 0) : T.domain ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (T.shift l) (T.shift_bijective hl)

/-- The **resolvent** `(A - i l)⁻¹`, as a linear map into the domain (zero for
the meaningless value `l = 0`). -/
noncomputable def res (l : ℝ) : H →ₗ[ℂ] T.domain :=
  if h : l = 0 then 0 else ((T.shiftEquiv h).symm : H →ₗ[ℂ] T.domain)

theorem shift_res {l : ℝ} (hl : l ≠ 0) (y : H) : T.shift l (T.res l y) = y := by
  rw [res, dif_neg hl]
  exact (T.shiftEquiv hl).apply_symm_apply y

theorem res_shift {l : ℝ} (hl : l ≠ 0) (x : T.domain) : T.res l (T.shift l x) = x := by
  rw [res, dif_neg hl]
  exact (T.shiftEquiv hl).symm_apply_apply x

/-- The defining property of the resolvent: `A (A - il)⁻¹ y = y + il (A - il)⁻¹ y`. -/
theorem op_res {l : ℝ} (hl : l ≠ 0) (y : H) :
    T.op (T.res l y) = y + ((l : ℂ) * Complex.I) • ((T.res l y : T.domain) : H) := by
  have h := T.shift_res hl y
  rw [shift_apply] at h
  exact sub_eq_iff_eq_add.mp h





theorem norm_res_le (l : ℝ) (y : H) : ‖(T.res l y : H)‖ ≤ (1 / |l|) * ‖y‖ := by
  by_cases hl : l = 0
  · simp [res, hl]
  · have habs : (0 : ℝ) < |l| := abs_pos.mpr hl
    have h := T.norm_shift_ge l (T.res l y)
    rw [T.shift_res hl] at h
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ habs]
    linarith [h]

/-- The resolvent as a bounded operator on the whole space. -/
noncomputable def resCLM (l : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous (T.domain.subtype ∘ₗ T.res l) (1 / |l|) (T.norm_res_le l)

@[simp] theorem resCLM_apply (l : ℝ) (y : H) : T.resCLM l y = (T.res l y : H) := rfl

theorem resCLM_mem (l : ℝ) (y : H) : T.resCLM l y ∈ T.domain := (T.res l y).2

theorem norm_resCLM_apply_le (l : ℝ) (y : H) : ‖T.resCLM l y‖ ≤ (1 / |l|) * ‖y‖ :=
  T.norm_res_le l y

/-- On the domain, the resolvent commutes with the operator. -/
theorem res_op {l : ℝ} (hl : l ≠ 0) (x : T.domain) :
    ((T.res l (T.op x) : T.domain) : H) = T.op (T.res l (x : H)) := by
  set w : T.domain := T.res l (x : H) with hw
  have hAw : T.op w = (x : H) + ((l : ℂ) * Complex.I) • (w : H) := T.op_res hl (x : H)
  have hmem : T.op w ∈ T.domain := by
    rw [hAw]
    exact T.domain.add_mem x.2 (T.domain.smul_mem _ w.2)
  have hsub : (⟨T.op w, hmem⟩ : T.domain) = x + ((l : ℂ) * Complex.I) • w := by
    apply Subtype.ext
    simpa using hAw
  have hshift : T.shift l ⟨T.op w, hmem⟩ = T.op x := by
    rw [shift_apply, hsub, map_add, map_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [hAw]
    module
  have := T.res_shift hl ⟨T.op w, hmem⟩
  rw [hshift] at this
  rw [this]

/-- The adjoint relation `((A - il)⁻¹)^* = (A + il)⁻¹`. -/
theorem inner_res {l : ℝ} (hl : l ≠ 0) (y z : H) :
    ⟪((T.res l y : T.domain) : H), z⟫_ℂ = ⟪y, ((T.res (-l) z : T.domain) : H)⟫_ℂ := by
  have hl' : -l ≠ 0 := neg_ne_zero.mpr hl
  set u : T.domain := T.res l y with hu
  set v : T.domain := T.res (-l) z with hv
  have hy : T.op u - ((l : ℂ) * Complex.I) • (u : H) = y := by
    have := T.shift_res hl y
    rwa [shift_apply] at this
  have hz : T.op v - (((-l : ℝ) : ℂ) * Complex.I) • (v : H) = z := by
    have := T.shift_res hl' z
    rwa [shift_apply] at this
  have hz' : T.op v + ((l : ℂ) * Complex.I) • (v : H) = z := by
    rw [← hz]; push_cast; module
  have hsym := T.symmetric u v
  rw [← hy, ← hz']
  rw [inner_add_right, inner_sub_left, inner_smul_left, inner_smul_right, hsym]
  simp [Complex.conj_I]

/-- Resolvents at different parameters commute. -/
theorem res_comm {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (y : H) :
    ((T.res l ((T.res m y : T.domain) : H) : T.domain) : H)
      = ((T.res m ((T.res l y : T.domain) : H) : T.domain) : H) := by
  set a : T.domain := T.res l ((T.res m y : T.domain) : H) with ha
  set b : T.domain := T.res m ((T.res l y : T.domain) : H) with hb
  have h1 : T.op a = ((T.res l y : T.domain) : H) + ((m : ℂ) * Complex.I) • (a : H) := by
    have hcomm := T.res_op hl (T.res m y)
    have hAres : T.op (T.res m y) = y + ((m : ℂ) * Complex.I) • ((T.res m y : T.domain) : H) :=
      T.op_res hm y
    rw [hAres] at hcomm
    rw [map_add, map_smul] at hcomm
    simp only [Submodule.coe_add, Submodule.coe_smul] at hcomm
    rw [← hcomm, ← ha]
  have h2 : T.op b = ((T.res l y : T.domain) : H) + ((m : ℂ) * Complex.I) • (b : H) :=
    T.op_res hm _
  have hd : T.shift m (a - b) = 0 := by
    rw [map_sub, shift_apply, shift_apply, h1, h2]
    module
  have hzero : a - b = 0 := T.shift_injective hm (by simpa using hd)
  have hab : a = b := sub_eq_zero.mp hzero
  rw [hab]

end UnboundedSelfAdjoint

end BookProof.ChapterStoneResolvent


