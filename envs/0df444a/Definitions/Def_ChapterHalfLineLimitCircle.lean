-- Prove2me | Definitions.Def_ChapterHalfLineLimitCircle
-- name    : ChapterHalfLineLimitCircle
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-03T22:24:37.721643+00:00
-- url     : https://prove2.me/theorems/54f4a931-4f6d-4d5c-a6c9-0e61127ee78c
-- title:
--   The Lean 4 theorem `contDiff_of_mem_testSpace` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHalfLineLimitCircle.lean`): generated def bundle for ChapterHalfLineLimitCircle. See BookProof/ChapterHalfLineLimitCircle.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHalfLineLimitCircle.lean

import Definitions.Def_ChapterFarisLavine
import Mathlib


/-!
# The half-line kinetic operator is **not** essentially self-adjoint

Plan item **QG-2 / 29f Case B** of `CONSOLIDATED_PLAN.md` records that the
densitized conformal direction of the gauge-fixed theory lives on the half line
`y ∈ (0, ∞)` (`y = √e`, `e` the tetrad determinant, `e = 0` being the
degenerate-tetrad endpoint) and carries a **wrong-sign** kinetic term, and that
the densitized d'Alembertian is therefore expected to fail essential
self-adjointness — the limit-circle phenomenon at the endpoint.  Its companion
module `BookProof/ChapterConformalSignFlip.lean` proves the sign bookkeeping
(essential self-adjointness is invariant under `H ↦ −H`) but leaves the
analytic statement itself unformalized.

This module supplies that analytic statement, in the cleanest instance: the
**free** kinetic operator on the half line.

* `testSpace` — the smooth functions with compact support contained in the open
  half line `(0, ∞)`, `hlCore` their image in `L²((0,∞))` and `hlKin` the
  operator `−d²/dy²` on that core (`hlKin_apply`), which is symmetric
  (`hlKin_symmetricOn`);
* `deficiencyFun y = exp(−λy)`, `λ = (√2/2)(1 − i)`, satisfies `λ² = −i`, is
  square integrable on `(0, ∞)` and is **not** the zero element of `L²`
  (`deficiencyVec_ne_zero`);
* `hlKin_deficiency_identity` — it satisfies the adjoint deficiency identity
  `⟪−v'', w⟫ = i⟪v, w⟫` for every `v` in the core, by two integrations by parts
  (the boundary terms vanish because the test functions are supported away from
  the endpoint);
* **`hlKin_not_deficiencyTrivialAt_I`**, **`hlKin_not_essentiallySelfAdjointOn`**
  — hence the deficiency space at `i` is non-trivial and the half-line kinetic
  operator is not essentially self-adjoint on this core;
* **`hlKin_neg_not_essentiallySelfAdjointOn`** — and, by the sign-flip theorem
  of `ChapterConformalSignFlip`, neither is the **wrong-sign** kinetic operator
  `+d²/dy²`, which is the one the densitized conformal direction carries.  This
  is Case B's conclusion for the free densitized kinetic: no choice of sign
  convention rescues it, and the failure is caused by the endpoint, not by any
  potential.
* `hlCore_ne_bot` — and the core is not the zero subspace (an explicit smooth
  bump supported in `(1, 3)` lies in it), so none of this is vacuous.

## Honest boundary

What is proved is non-essential-self-adjointness of the *free* kinetic operator
on the compactly-supported core of the open half line — the endpoint
(limit-circle) mechanism in its purest form.  Nothing here treats a potential
`V(y)` (the limit-circle analysis of the unbounded-below flipped potential
remains unformalized), and nothing here is a statement about the full
multi-dimensional densitized operator.  Failure of essential self-adjointness
on a core means the symmetric operator has more than one self-adjoint
extension, not that no self-adjoint extension exists.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HalfLineLimitCircle

open MeasureTheory Set BookProof.FarisLavine

noncomputable section

local notation "smoothTop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Lebesgue measure on the open half line `(0, ∞)` — the conformal coordinate's
configuration space. -/
abbrev hlMeasure : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-- The half-line Hilbert space `L²((0,∞))`. -/
abbrev HL : Type := Lp ℂ 2 hlMeasure

/-! ## The test-function core -/

/-- Smooth functions with compact support contained in the **open** half line. -/
def testSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ smoothTop f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi (0 : ℝ)}
  add_mem' := by
    rintro f g ⟨hf, hfc, hfs⟩ ⟨hg, hgc, hgs⟩
    exact ⟨hf.add hg, hfc.add hgc, (tsupport_add f g).trans (union_subset hfs hgs)⟩
  zero_mem' := by
    refine ⟨contDiff_const, ?_, ?_⟩
    · simpa using (HasCompactSupport.zero (α := ℝ) (β := ℂ))
    · simp [tsupport]
  smul_mem' := by
    rintro c f ⟨hf, hfc, hfs⟩
    exact ⟨hf.const_smul c, hfc.smul_left,
      (closure_mono (Function.support_const_smul_subset c f)).trans hfs⟩

theorem contDiff_of_mem_testSpace {f : ℝ → ℂ} (hf : f ∈ testSpace) :
    ContDiff ℝ smoothTop f := hf.1

theorem hasCompactSupport_of_mem_testSpace {f : ℝ → ℂ} (hf : f ∈ testSpace) :
    HasCompactSupport f := hf.2.1

theorem tsupport_subset_of_mem_testSpace {f : ℝ → ℂ} (hf : f ∈ testSpace) :
    tsupport f ⊆ Ioi (0 : ℝ) := hf.2.2

/-- A test function vanishes off the open half line. -/
theorem eq_zero_of_notMem_Ioi {f : ℝ → ℂ} (hf : f ∈ testSpace) {x : ℝ} (hx : x ∉ Ioi (0 : ℝ)) :
    f x = 0 := by
  by_contra hne
  exact hx (tsupport_subset_of_mem_testSpace hf (subset_tsupport f hne))

/-- The derivative of a test function is a test function. -/
theorem deriv_mem_testSpace {f : ℝ → ℂ} (hf : f ∈ testSpace) : deriv f ∈ testSpace := by
  refine ⟨(contDiff_infty_iff_deriv.mp (contDiff_of_mem_testSpace hf)).2,
    (hasCompactSupport_of_mem_testSpace hf).deriv, ?_⟩
  refine (closure_mono (support_deriv_subset (f := f))).trans ?_
  rw [(isClosed_tsupport f).closure_eq]
  exact tsupport_subset_of_mem_testSpace hf



theorem deriv_const_smul_fun {f : ℝ → ℂ} (hf : ContDiff ℝ smoothTop f) (c : ℂ) :
    deriv (c • f) = c • deriv f := by
  funext x
  exact (((hf.differentiable (by simp)).differentiableAt.hasDerivAt).const_smul c).deriv

theorem memLp_of_mem_testSpace {f : ℝ → ℂ} (hf : f ∈ testSpace) : MemLp f 2 hlMeasure :=
  (contDiff_of_mem_testSpace hf).continuous.memLp_of_hasCompactSupport
    (μ := hlMeasure) (hasCompactSupport_of_mem_testSpace hf)

/-- The inclusion of the test-function space into `L²((0,∞))`. -/
def testIncl : testSpace →ₗ[ℂ] HL where
  toFun f := (memLp_of_mem_testSpace f.2).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_of_mem_testSpace (f + g).2).coeFn_toLp,
      (memLp_of_mem_testSpace f.2).coeFn_toLp, (memLp_of_mem_testSpace g.2).coeFn_toLp,
      Lp.coeFn_add ((memLp_of_mem_testSpace f.2).toLp _)
        ((memLp_of_mem_testSpace g.2).toLp _)] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    rfl
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_of_mem_testSpace (c • f).2).coeFn_toLp,
      (memLp_of_mem_testSpace f.2).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_of_mem_testSpace f.2).toLp _)] with x h1 h2 h3
    rw [RingHom.id_apply, h1, h3, Pi.smul_apply, h2]
    rfl

theorem testIncl_coeFn (f : testSpace) :
    ((testIncl f : HL) : ℝ → ℂ) =ᵐ[hlMeasure] (f : ℝ → ℂ) :=
  (memLp_of_mem_testSpace f.2).coeFn_toLp

theorem testIncl_injective : Function.Injective testIncl := by
  intro f g hfg
  refine Subtype.ext (funext fun x => ?_)
  have hae : (f : ℝ → ℂ) =ᵐ[hlMeasure] (g : ℝ → ℂ) := by
    have h1 := testIncl_coeFn f
    have h2 := testIncl_coeFn g
    rw [hfg] at h1
    exact h1.symm.trans h2
  have heq : EqOn (f : ℝ → ℂ) (g : ℝ → ℂ) (Ioi (0 : ℝ)) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (contDiff_of_mem_testSpace f.2).continuous.continuousOn
      (contDiff_of_mem_testSpace g.2).continuous.continuousOn
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · exact heq hx
  · rw [eq_zero_of_notMem_Ioi f.2 hx, eq_zero_of_notMem_Ioi g.2 hx]

/-- **The core**: the image of the test functions in `L²((0,∞))`. -/
def hlCore : Submodule ℂ HL := LinearMap.range testIncl

/-- Test functions are in bijection with the core. -/
def hlEquiv : testSpace ≃ₗ[ℂ] hlCore := LinearEquiv.ofInjective testIncl testIncl_injective

@[simp] theorem hlEquiv_coe (f : testSpace) : ((hlEquiv f : hlCore) : HL) = testIncl f := rfl

/-- The second derivative, as a linear map of the test-function space. -/
def deriv2LM : testSpace →ₗ[ℂ] testSpace where
  toFun f := ⟨deriv (deriv (f : ℝ → ℂ)), deriv_mem_testSpace (deriv_mem_testSpace f.2)⟩
  map_add' f g := by
    refine Subtype.ext ?_
    have hf := (contDiff_of_mem_testSpace f.2)
    have hg := (contDiff_of_mem_testSpace g.2)
    have h1 : deriv ((f : ℝ → ℂ) + (g : ℝ → ℂ)) = deriv (f : ℝ → ℂ) + deriv (g : ℝ → ℂ) :=
      funext fun x => deriv_add ((hf.differentiable (by simp)).differentiableAt)
        ((hg.differentiable (by simp)).differentiableAt)
    have hf' := (contDiff_infty_iff_deriv.mp hf).2
    have hg' := (contDiff_infty_iff_deriv.mp hg).2
    change deriv (deriv ((f : ℝ → ℂ) + (g : ℝ → ℂ))) = _
    rw [h1]
    exact funext fun x => deriv_add ((hf'.differentiable (by simp)).differentiableAt)
      ((hg'.differentiable (by simp)).differentiableAt)
  map_smul' c f := by
    refine Subtype.ext ?_
    have hf := contDiff_of_mem_testSpace f.2
    have hf' := (contDiff_infty_iff_deriv.mp hf).2
    change deriv (deriv (c • (f : ℝ → ℂ))) = c • deriv (deriv (f : ℝ → ℂ))
    rw [deriv_const_smul_fun hf c, deriv_const_smul_fun hf' c]

/-- **The half-line kinetic operator** `−d²/dy²` on the compactly supported core
of `L²((0,∞))`. -/
def hlKin : hlCore →ₗ[ℂ] HL := -(testIncl ∘ₗ deriv2LM ∘ₗ hlEquiv.symm.toLinearMap)





/-! ## Integration by parts on the half line -/





/-! ## The deficiency vector -/

/-- `λ = (√2/2)(1 − i)`, a square root of `−i` with positive real part. -/
def lam : ℂ := (Real.sqrt 2 / 2 : ℝ) * (1 - Complex.I)







/-- The deficiency function `w(y) = e^{−λy}`: a square-integrable solution of
`−w'' = i w` on the half line. -/
def deficiencyFun (y : ℝ) : ℂ := Complex.exp (-(lam * y))







theorem deficiencyFun_contDiff : ContDiff ℝ smoothTop deficiencyFun := by
  have h : ContDiff ℝ smoothTop fun y : ℝ => -(lam * (y : ℂ)) := by
    simpa [smul_eq_mul] using
      ((Complex.ofRealCLM.contDiff (n := smoothTop)).const_smul lam).neg
  exact h.cexp

theorem norm_deficiencyFun (y : ℝ) :
    ‖deficiencyFun y‖ = Real.exp (-(Real.sqrt 2 / 2) * y) := by
  rw [deficiencyFun, Complex.norm_exp]
  congr 1
  simp [lam]

theorem deficiencyFun_memLp : MemLp deficiencyFun 2 hlMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    deficiencyFun_contDiff.continuous.aestronglyMeasurable).mpr ?_
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-Real.sqrt 2 * x)) (Ioi (0:ℝ)) volume :=
    exp_neg_integrableOn_Ioi 0 (by positivity)
  have heq : ∀ x : ℝ, ‖deficiencyFun x‖ ^ 2 = Real.exp (-Real.sqrt 2 * x) := by
    intro x
    rw [norm_deficiencyFun, sq, ← Real.exp_add]
    congr 1
    ring
  exact hint.congr (Filter.Eventually.of_forall fun x => (heq x).symm)

/-- The deficiency vector in `L²((0,∞))`. -/
def deficiencyVec : HL := deficiencyFun_memLp.toLp _





/-! ## The inner products, and the failure of essential self-adjointness -/













/-! ## The core is non-trivial

The statements above would be vacuous if the core were the zero subspace, so we
exhibit an explicit element: a smooth bump centred at `2` with support the
interval `(1, 3)`, comfortably inside the open half line.
-/

/-- A smooth bump centred at `2`, equal to `1` on `[3/2, 5/2]` and supported in
`(1, 3)`. -/
def hlBump : ContDiffBump (2 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

/-- The bump, as a complex-valued function on the line. -/
def hlBumpFun : ℝ → ℂ := fun x => ((hlBump x : ℝ) : ℂ)

theorem hlBumpFun_mem_testSpace : hlBumpFun ∈ testSpace := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hlBump.contDiff,
    hlBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp), ?_⟩
  have hts : tsupport hlBumpFun = tsupport (fun x => hlBump x) := by
    unfold hlBumpFun tsupport Function.support
    congr 1
    ext x
    simp
  rw [hts, hlBump.tsupport_eq]
  intro x hx
  simp only [Metric.mem_closedBall, Real.dist_eq] at hx
  have hr : hlBump.rOut = 1 := rfl
  rw [hr] at hx
  have := (abs_le.mp hx).1
  simp only [mem_Ioi]
  linarith

/-- The bump as an element of the test-function space. -/
def hlBumpTest : testSpace := ⟨hlBumpFun, hlBumpFun_mem_testSpace⟩







end

end BookProof.HalfLineLimitCircle


