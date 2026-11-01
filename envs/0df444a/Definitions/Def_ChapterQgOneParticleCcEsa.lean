-- Prove2me | Definitions.Def_ChapterQgOneParticleCcEsa
-- name    : ChapterQgOneParticleCcEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-31T10:57:55.554622+00:00
-- url     : https://prove2.me/theorems/ee5fbaa2-b4cc-4189-a322-2adc1561da4f
-- title:
--   Chapter QgOneParticleCcEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgOneParticleCcEsa.lean`): generated def bundle for ChapterQgOneParticleCcEsa. See BookProof/ChapterQgOneParticleCcEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOneParticleCcEsa.lean

import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_symmetricOn_inclusion
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave
import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_symmetric
import Theorems.Thm_BookProof_StrichartzWave_exists_smooth_cutoff
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric
import Theorems.Thm_BookProof_QgHermiteFriedrichs_coordLine_apply
import Theorems.Thm_BookProof_HermiteQuadraticEsa_confV_essentiallySelfAdjoint
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_confW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_sectorQuadW
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_confW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_of_le_harm
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_sectorQuadW
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_pgLp
import Theorems.Thm_BookProof_HermiteQuadraticEsa_harmonic_add_subquadratic_essentiallySelfAdjoint
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_pgFun_coord
import Theorems.Thm_BookProof_ScalaronEsa_mulCc_apply
import Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_HermiteQuadraticEsa_sectorQuad_essentiallySelfAdjoint
import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
import Mathlib


/-!
# The one-particle `R + αR²` Hamiltonian on the compactly supported smooth core

`CONSOLIDATED_PLAN.md` §10.6.1 asks for essential self-adjointness of the one-particle
gauge-fixed Hamiltonian `−Δ + W` on a dense core of `L²(ℝᵈ)`, and its §10.6.3 "definition of
done" names the Gauss–polynomial (Hermite) core.  For the *physics* the natural core is the
smaller one of **smooth compactly supported** functions: essential self-adjointness there is
strictly stronger (a smaller core means fewer test vectors in the deficiency equation), it
implies the statement on every larger core, and it is the core one uses when second
quantizing, since the finite-particle Fock core is built from it.

This module proves that statement, by transporting the Gauss-core theorems of
`BookProof.ChapterHermiteQuadraticEsa` down to the compactly supported core.

## The mechanism

`deficiencyTrivialAt_of_graphApprox` is the abstract step: if every vector of a domain `D₁`
is approximated, in the graph norm, by vectors of a *possibly unrelated* domain `D₂`, then
triviality of the deficiency spaces on `D₁` implies triviality on `D₂`.  (The corresponding
statement for `D₂ ≤ D₁` is `FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core`;
here neither core contains the other, since a Gauss polynomial is never compactly
supported.)

The analytic input is the cut-off estimate: for `ψ = p(x)e^{−‖x‖²/4}` and `χ_R(x) = χ(x/R)`
a scaled bump,

`(−Δ + W)(χ_R ψ) − (−Δ + W)ψ = (χ_R − 1)(−Δψ + Wψ) − 2∑ⱼ ∂ⱼχ_R ∂ⱼψ − (Δχ_R) ψ`,

whose three terms are `o(1)` in `L²`: the first by dominated convergence, the second and
third because `‖∂χ_R‖ ≤ C/R` and `‖∂²χ_R‖ ≤ C/R²` while `∂ⱼψ, ψ ∈ L²`.

## What is proved

* `ccHam` — the Hamiltonian `−Δ + W` on the compactly supported smooth core `ccDomain`,
  with `ccHam_symmetricOn`;
* `exists_cc_graph_approx` — the cut-off approximation;
* `ccHam_essentiallySelfAdjoint_of_core` — the transfer theorem;
* **`qgOneParticleCc_esa`** — `−Δ + ‖x‖²/4 + V` is essentially self-adjoint on the compactly
  supported smooth core of `L²(ℝᵈ)` for every smooth `V` with `|V| ≤ a‖x‖²/4 + b`, `a < 1`,
  with **`qgOneParticleCc_stone_flow`** its unitary group;
* `confVCc_esa`, `sectorQuadCc_esa` — the conformal-mode (`d = 1`) and reduced
  two-variable-sector (`d = 2`) instances of the gauge-fixed `R + αR²` Hamiltonian;
* `qgFockCc_esa` — the finite-particle statement: the `n`-particle Hamiltonian
  `∑ₖ (−Δ_k + W(x_k))` on `L²((ℝᵈ)ⁿ)` is of the same form, so it too is essentially
  self-adjoint on the compactly supported smooth core.

**Honest boundary.**  The potential class is the quadratic one of
`BookProof.ChapterHermiteQuadraticEsa` (the harmonic conformal-mode parabola plus a
strictly subquadratic perturbation).  The exponentially growing scalaron wall is *not*
covered: what is transported here is exactly what the Gauss core provides.
-/

namespace BookProof.QgOneParticleCc

open MeasureTheory SchwartzMap Complex MvPolynomial
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.HermiteQuadraticEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.DirectSumEsa

noncomputable section


/-! ## 1. The abstract transfer step -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Deficiency transfer by graph approximation.**  If every vector of `D₁` is approximated,
together with its image, by vectors of `D₂`, then a deficiency vector for `T₂` is one for
`T₁`; so triviality of the deficiency space of `T₁` at `z` forces that of `T₂`.  Neither
domain need contain the other. -/
theorem deficiencyTrivialAt_of_graphApprox {D₁ D₂ : Submodule ℂ F}
    (T₁ : D₁ →ₗ[ℂ] F) (T₂ : D₂ →ₗ[ℂ] F) {z : ℂ}
    (happrox : ∀ (x : D₁) (ε : ℝ), 0 < ε →
      ∃ y : D₂, ‖(y : F) - (x : F)‖ < ε ∧ ‖T₂ y - T₁ x‖ < ε)
    (h₁ : DeficiencyTrivialAt D₁ T₁ z) :
    DeficiencyTrivialAt D₂ T₂ z := by
  intro w hw
  refine h₁ w fun x => ?_
  have hzero : ∀ ε : ℝ, 0 < ε →
      ‖(inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w‖ ≤ ε * (1 + ‖z‖) * ‖w‖ := by
    intro ε hε
    obtain ⟨y, hy1, hy2⟩ := happrox x ε hε
    have hwy := hw y
    have hsplit : (inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w
        = (inner ℂ (T₁ x - T₂ y) w : ℂ) + z * inner ℂ ((y : F) - (x : F)) w := by
      rw [inner_sub_left, inner_sub_left, hwy]
      ring
    calc ‖(inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w‖
        ≤ ‖(inner ℂ (T₁ x - T₂ y) w : ℂ)‖ + ‖z * (inner ℂ ((y : F) - (x : F)) w : ℂ)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ ‖T₁ x - T₂ y‖ * ‖w‖ + ‖z‖ * (‖(y : F) - (x : F)‖ * ‖w‖) := by
          gcongr
          · exact norm_inner_le_norm _ _
          · rw [norm_mul]
            gcongr
            exact norm_inner_le_norm _ _
      _ ≤ ε * (1 + ‖z‖) * ‖w‖ := by
          have h1 : ‖T₁ x - T₂ y‖ ≤ ε := by
            rw [← norm_neg]; simpa [neg_sub] using hy2.le
          have hA : ‖T₁ x - T₂ y‖ * ‖w‖ ≤ ε * ‖w‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
          have hB : ‖z‖ * (‖(y : F) - (x : F)‖ * ‖w‖) ≤ ‖z‖ * (ε * ‖w‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy1.le (norm_nonneg w))
              (norm_nonneg z)
          nlinarith [norm_nonneg w, norm_nonneg z]
  have hnn : ‖(inner ℂ (T₁ x) w : ℂ) - z * inner ℂ (x : F) w‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hpos : 0 < δ / ((1 + ‖z‖) * (1 + ‖w‖)) := by positivity
    have hb := hzero _ hpos
    have hbound : δ / ((1 + ‖z‖) * (1 + ‖w‖)) * (1 + ‖z‖) * ‖w‖ ≤ δ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg w, norm_nonneg z, hδ.le]
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnn)

/-- Essential self-adjointness transfers along a graph approximation. -/
theorem essentiallySelfAdjointOn_of_graphApprox {D₁ D₂ : Submodule ℂ F}
    (T₁ : D₁ →ₗ[ℂ] F) (T₂ : D₂ →ₗ[ℂ] F)
    (happrox : ∀ (x : D₁) (ε : ℝ), 0 < ε →
      ∃ y : D₂, ‖(y : F) - (x : F)‖ < ε ∧ ‖T₂ y - T₁ x‖ < ε)
    (h₁ : EssentiallySelfAdjointOn D₁ T₁) :
    EssentiallySelfAdjointOn D₂ T₂ :=
  ⟨deficiencyTrivialAt_of_graphApprox T₁ T₂ happrox h₁.1,
    deficiencyTrivialAt_of_graphApprox T₁ T₂ happrox h₁.2⟩

end Abstract

/-! ## 2. The Hamiltonian on the compactly supported smooth core -/

variable {d : ℕ}

/-- The `j`-th coordinate direction of `ℝᵈ`. -/
def kinDir (d : ℕ) (j : Fin d) : Vd d := EuclideanSpace.single j (1 : ℝ)

/-- The (negative) Laplacian `−Δ = −∑ⱼ ∂ⱼ²` as an operator on Schwartz space. -/
def kinOp (d : ℕ) : 𝓢(Vd d, ℂ) →L[ℂ] 𝓢(Vd d, ℂ) :=
  constCoeffOp (fun _ : Fin d => (-1 : ℝ)) (kinDir d) 0

/-- The kinetic term on the compactly supported smooth core. -/
def kinCc (d : ℕ) : ccDomain (Vd d) →ₗ[ℂ] L2d d :=
  opL2 (kinOp d) ∘ₗ Submodule.inclusion (ccDomain_le_schwartzDomain (E := Vd d))

/-- **The one-particle Hamiltonian `−Δ + W` on the compactly supported smooth core** of
`L²(ℝᵈ)`, for an arbitrary smooth real potential `W`. -/
def ccHam (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ccDomain (Vd d) →ₗ[ℂ] L2d d :=
  kinCc d + opCc W hW

theorem kinCc_symmetricOn : SymmetricOn (ccDomain (Vd d)) (kinCc d) :=
  symmetricOn_inclusion _ _ (constCoeffOp_symmetric _ _ _)

theorem ccHam_symmetricOn (W : Vd d → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain (Vd d)) (ccHam W hW) := by
  intro x y
  have h1 := kinCc_symmetricOn (d := d) x y
  have h2 := smoothPotential_symmetric W hW x y
  simp only [ccHam, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2

/-! ## 3. Pointwise calculus: the Laplacian in coordinates -/

/-- The `j`-th coordinate derivative of a function on `ℝᵈ`. -/
def dcoord (j : Fin d) (u : Vd d → ℂ) (x : Vd d) : ℂ := fderiv ℝ u x (kinDir d j)

/-- The Laplacian in coordinates. -/
def lapC (u : Vd d → ℂ) (x : Vd d) : ℂ := ∑ j : Fin d, dcoord j (dcoord j u) x

theorem secondDeriv_apply_eq (m : Vd d) (f : 𝓢(Vd d, ℂ)) (x : Vd d) :
    (secondDeriv m f) x = fderiv ℝ (fun y => fderiv ℝ (f : Vd d → ℂ) y m) x m := rfl

/-- On a Schwartz map the operator `kinOp` is the pointwise `−Δ`. -/
theorem kinOp_apply_eq (f : 𝓢(Vd d, ℂ)) (x : Vd d) :
    (kinOp d f) x = -lapC (f : Vd d → ℂ) x := by
  have h : (kinOp d f)
      = (∑ i : Fin d, ((-1 : ℝ) : ℂ) • secondDeriv (kinDir d i) f)
        + ((0 : ℝ) : ℂ) • f := by
    simp [kinOp, constCoeffOp]
  rw [h]
  simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero,
    secondDeriv_apply_eq, lapC, dcoord, neg_one_mul, ← Finset.sum_neg_distrib]
  rfl

/-- Smoothness passes to the coordinate derivative. -/
theorem contDiff_dcoord {u : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (j : Fin d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dcoord j u) := by
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ u y) :=
    hu.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  exact (ContinuousLinearMap.apply ℝ ℂ (kinDir d j)).contDiff.comp hfd

theorem differentiableAt_of_contDiffTop {u : Vd d → ℂ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (x : Vd d) : DifferentiableAt ℝ u x :=
  (hu.differentiable (by simp)).differentiableAt

theorem dcoord_add {u v : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d) :
    dcoord j (fun y => u y + v y) = fun x => dcoord j u x + dcoord j v x := by
  funext x
  simp only [dcoord]
  have h := ((differentiableAt_of_contDiffTop hu x).hasFDerivAt.add
    (differentiableAt_of_contDiffTop hv x).hasFDerivAt).fderiv
  change (fderiv ℝ (u + v) x) (kinDir d j) = _
  rw [h]
  simp

theorem dcoord_mul {u v : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (j : Fin d) :
    dcoord j (fun y => u y * v y) = fun x => u x * dcoord j v x + v x * dcoord j u x := by
  funext x
  simp only [dcoord]
  have h := ((differentiableAt_of_contDiffTop hu x).hasFDerivAt.mul
    (differentiableAt_of_contDiffTop hv x).hasFDerivAt).fderiv
  change (fderiv ℝ (u * v) x) (kinDir d j) = _
  rw [h]
  simp

/-- **Leibniz for the Laplacian.** -/
theorem lapC_mul {u v : Vd d → ℂ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) (x : Vd d) :
    lapC (fun y => u y * v y) x
      = u x * lapC v x + v x * lapC u x
        + 2 * ∑ j : Fin d, dcoord j u x * dcoord j v x := by
  have hstep : ∀ j : Fin d, dcoord j (dcoord j (fun y => u y * v y)) x
      = u x * dcoord j (dcoord j v) x + v x * dcoord j (dcoord j u) x
        + 2 * (dcoord j u x * dcoord j v x) := by
    intro j
    rw [dcoord_mul hu hv j]
    rw [dcoord_add (hu.mul (contDiff_dcoord hv j)) (hv.mul (contDiff_dcoord hu j)) j]
    rw [dcoord_mul hu (contDiff_dcoord hv j) j, dcoord_mul hv (contDiff_dcoord hu j) j]
    ring
  simp only [lapC, hstep, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## 4. The Gauss–polynomial core is smooth, with algebraic derivatives -/

theorem contDiff_polyEval (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Vd d => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine hp.mul ?_
      exact Complex.ofRealCLM.contDiff.comp
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

theorem contDiff_gaussD (d : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gaussD (d := d)) := by
  unfold gaussD
  exact Real.contDiff_exp.comp (((contDiff_norm_sq ℝ).neg).div_const 4)

theorem contDiff_pgFun (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pgFun p) :=
  (contDiff_polyEval p).mul (Complex.ofRealCLM.contDiff.comp (contDiff_gaussD d))

/-- Moving along the `j`-th coordinate direction is moving along the coordinate line. -/
theorem coordLine_add_smul (x : Vd d) (j : Fin d) (t : ℝ) :
    x + t • kinDir d j = coordLine x j (x j + t) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [kinDir, coordLine_apply, EuclideanSpace.single_apply]
  · simp only [PiLp.add_apply, PiLp.smul_apply, coordLine_apply, Function.update_of_ne h,
      kinDir, EuclideanSpace.single_apply, smul_eq_mul]
    simp [h]

theorem coordLine_self_eq (x : Vd d) (j : Fin d) : coordLine x j (x j) = x := by
  ext i
  by_cases h : i = j
  · subst h; simp [coordLine_apply]
  · simp [coordLine_apply, Function.update_of_ne h]

/-- Differentiating the core in a coordinate is the twisted derivative `coreD`. -/
theorem dcoord_pgFun (p : MvPolynomial (Fin d) ℂ) (j : Fin d) :
    dcoord j (pgFun p) = pgFun (coreD j p) := by
  funext x
  have h0 := hasDerivAt_pgFun_coord p j x (x j)
  have hshift : HasDerivAt (fun t : ℝ => x j + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x j)
  have h0' : HasDerivAt (fun s : ℝ => pgFun p (coordLine x j s)) (pgFun (coreD j p) x)
      (x j + 0) := by
    simpa [coordLine_self_eq] using h0
  have hcomp := HasDerivAt.scomp (0 : ℝ) h0' hshift
  simp only [Function.comp_def, one_smul] at hcomp
  have hfun : (fun t : ℝ => pgFun p (coordLine x j (x j + t)))
      = fun t : ℝ => pgFun p (x + t • kinDir d j) := by
    funext t
    rw [coordLine_add_smul]
  rw [hfun] at hcomp
  have hld : HasLineDerivAt ℝ (pgFun p) (pgFun (coreD j p) x) x (kinDir d j) := by
    simpa [HasLineDerivAt] using hcomp
  have hdiff : DifferentiableAt ℝ (pgFun p) x :=
    differentiableAt_of_contDiffTop (contDiff_pgFun p) x
  have hfd : fderiv ℝ (pgFun p) x (kinDir d j) = pgFun (coreD j p) x := by
    rw [← hdiff.lineDeriv_eq_fderiv]
    exact hld.lineDeriv
  simpa [dcoord] using hfd

/-- Hence the Laplacian on the core is `−kinPoly`. -/
theorem lapC_pgFun (p : MvPolynomial (Fin d) ℂ) :
    lapC (pgFun p) = fun x => -pgFun (kinPoly p) x := by
  funext x
  simp only [lapC, dcoord_pgFun]
  simp only [pgFun, kinPoly, map_neg, map_sum, Finset.sum_mul, neg_mul, neg_neg]

/-! ## 5. The scaled cut-off family -/

/-- A fixed smooth bump: `1` on the unit ball, `0` outside the ball of radius `2`. -/
def bump (d : ℕ) : Vd d → ℝ := Classical.choose (exists_smooth_cutoff (V := Vd d) 1)

theorem bump_spec (d : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bump d) ∧ HasCompactSupport (bump d) ∧
      (∀ x : Vd d, ‖x‖ ≤ 1 → bump d x = 1) ∧ (∀ x : Vd d, bump d x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x : Vd d, 1 + 1 ≤ ‖x‖ → bump d x = 0) ∧ ∃ C : ℝ, ∀ x, ‖gradient (bump d) x‖ ≤ C :=
  Classical.choose_spec (exists_smooth_cutoff (V := Vd d) 1)

/-- The rescaled cut-off `χ_R(x) = χ(x/R)`. -/
def cut (d : ℕ) (R : ℝ) : Vd d → ℝ := fun x => bump d (R⁻¹ • x)

theorem contDiff_cut (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut d R) :=
  (bump_spec d).1.comp (contDiff_id.const_smul (R⁻¹))

theorem hasCompactSupport_cut {R : ℝ} (hR : 0 < R) : HasCompactSupport (cut d R) := by
  have h := (bump_spec d).2.1
  have hne : (R⁻¹ : ℝ) ≠ 0 := by positivity
  have hc : HasCompactSupport (fun x : Vd d => bump d (R⁻¹ • x)) := h.comp_smul hne
  exact hc

theorem cut_eq_one {R : ℝ} (hR : 0 < R) {x : Vd d} (hx : ‖x‖ ≤ R) : cut d R x = 1 := by
  refine (bump_spec d).2.2.1 _ ?_
  rw [norm_smul]
  have : ‖(R⁻¹ : ℝ)‖ = R⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this]
  rw [inv_mul_le_iff₀ hR]
  simpa using hx

theorem cut_mem_Icc {R : ℝ} (x : Vd d) : cut d R x ∈ Set.Icc (0 : ℝ) 1 := bump_spec d |>.2.2.2.1 _

/-- The scaling `x ↦ x/R`, as a continuous linear map. -/
def scaleCLM (d : ℕ) (R : ℝ) : Vd d →L[ℝ] Vd d := R⁻¹ • ContinuousLinearMap.id ℝ (Vd d)

@[simp] theorem scaleCLM_apply (R : ℝ) (x : Vd d) : scaleCLM d R x = R⁻¹ • x := rfl

theorem norm_scaleCLM_le {R : ℝ} (hR : 0 < R) : ‖scaleCLM d R‖ ≤ R⁻¹ := by
  refine (norm_smul_le (R⁻¹) (ContinuousLinearMap.id ℝ (Vd d))).trans ?_
  have h1 : ‖ContinuousLinearMap.id ℝ (Vd d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h2 : ‖(R⁻¹ : ℝ)‖ = R⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h2]
  nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ (Vd d)), inv_pos.mpr hR]

theorem cut_eq_comp (R : ℝ) : cut d R = fun y => bump d (scaleCLM d R y) := rfl

/-- The derivative of a real function, read through the complexification. -/
theorem dcoord_ofReal {u : Vd d → ℝ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (j : Fin d)
    (x : Vd d) :
    dcoord j (fun y => ((u y : ℝ) : ℂ)) x = ((fderiv ℝ u x (kinDir d j) : ℝ) : ℂ) := by
  have hdiff : DifferentiableAt ℝ u x := (hu.differentiable (by simp)).differentiableAt
  have h : HasFDerivAt (fun y => ((u y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ u x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hdiff.hasFDerivAt
  simp [dcoord, h.fderiv]

/-- The first derivative of the scaled cut-off. -/
theorem fderiv_cut (R : ℝ) (x : Vd d) :
    fderiv ℝ (cut d R) x = (fderiv ℝ (bump d) (scaleCLM d R x)).comp (scaleCLM d R) := by
  have h1 : HasFDerivAt (bump d) (fderiv ℝ (bump d) (scaleCLM d R x)) (scaleCLM d R x) :=
    (((bump_spec d).1.differentiable (by simp)) _).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vd d => scaleCLM d R y) (scaleCLM d R) x :=
    (scaleCLM d R).hasFDerivAt
  have h := h1.comp x h2
  rw [cut_eq_comp]
  exact h.fderiv

/-- The second derivative of the scaled cut-off, as a composition. -/
theorem fderiv_fderiv_cut (R : ℝ) (x : Vd d) :
    fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x
      = (((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R)).comp
          ((fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y) (scaleCLM d R x)).comp
            (scaleCLM d R))) := by
  have hfun : (fun y : Vd d => fderiv ℝ (cut d R) y)
      = fun y : Vd d =>
          ((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R))
            (fderiv ℝ (bump d) (scaleCLM d R y)) := by
    funext y
    rw [fderiv_cut]
    rfl
  rw [hfun]
  have hbd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (bump d) y) :=
    (bump_spec d).1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  have h1 : HasFDerivAt (fun y : Vd d => fderiv ℝ (bump d) y)
      (fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y) (scaleCLM d R x)) (scaleCLM d R x) :=
    ((hbd.differentiable (by simp)) _).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vd d => scaleCLM d R y) (scaleCLM d R) x :=
    (scaleCLM d R).hasFDerivAt
  have h3 := h1.comp x h2
  have h4 := (((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip
    (scaleCLM d R)).hasFDerivAt).comp x h3
  exact h4.fderiv

set_option maxHeartbeats 128000000 in
/-- **The derivative bounds of the scaled cut-off**: `|∂ⱼχ_R| ≤ C/R` and `|Δχ_R| ≤ C/R²`,
with a constant that does not depend on `R`. -/
theorem exists_cut_derivative_bounds (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : Vd d,
      (∀ j : Fin d, ‖dcoord j (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ C / R) ∧
        ‖lapC (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ C / R ^ 2 := by
  classical
  -- bounds on the first and second derivative of the fixed bump
  have hbump := bump_spec d
  have hcs1 : HasCompactSupport (fun y : Vd d => fderiv ℝ (bump d) y) := hbump.2.1.fderiv ℝ
  have hcont1 : Continuous (fun y : Vd d => fderiv ℝ (bump d) y) :=
    hbump.1.continuous_fderiv (by simp)
  obtain ⟨C₁, hC₁⟩ := hcs1.exists_bound_of_continuous hcont1
  have hcs2 : HasCompactSupport (fun y : Vd d => fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) y)
    := hcs1.fderiv ℝ
  have hbd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (bump d) y) :=
    hbump.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
  have hcont2 : Continuous (fun y : Vd d => fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) y) :=
    hbd.continuous_fderiv (by simp)
  -- The direct call `hcs2.exists_bound_of_continuous hcont2` is unusable here:
  -- its `Continuous` argument must carry the *metric-derived* topology of the
  -- nested continuous linear map `Vd d →L[ℝ] Vd d →L[ℝ] ℝ` (that is the
  -- topology the section instance of `exists_bound_of_continuous` fixes), while
  -- `hcont2` has `ContinuousLinearMap.topologicalSpace`.  Checking the two
  -- definitionally never settles (measured 2026-10-27: a type mismatch after
  -- the full `maxHeartbeats 128000000`, 1.7 h of `whnf`).  Bound the R-valued
  -- evaluation on a compact set instead and lift through `opNorm_le_of_unit_norm`.
  have hφ : Continuous (fun p :
      (Vd d →L[ℝ] (Vd d →L[ℝ] ℝ)) × Vd d × Vd d => p.1 p.2.1 p.2.2) := by
    fun_prop
  have hK : IsCompact (Set.range
      (fun y : Vd d => fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) y) ×ˢ
      Metric.closedBall (0 : Vd d) 1 ×ˢ Metric.closedBall (0 : Vd d) 1) :=
    IsCompact.prod (hcs2.isCompact_range hcont2)
      (IsCompact.prod (isCompact_closedBall (0 : Vd d) 1)
        (isCompact_closedBall (0 : Vd d) 1))
  have hCO : ContinuousOn (fun p :
      (Vd d →L[ℝ] (Vd d →L[ℝ] ℝ)) × Vd d × Vd d => p.1 p.2.1 p.2.2)
      (Set.range (fun y : Vd d => fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) y) ×ˢ
      Metric.closedBall (0 : Vd d) 1 ×ˢ Metric.closedBall (0 : Vd d) 1) :=
    hφ.continuousOn
  obtain ⟨C₂, hC₂bound⟩ := hK.exists_bound_of_continuousOn hCO
  have hnnC₂ : 0 ≤ C₂ := le_trans (norm_nonneg _) <|
    hC₂bound (⟨fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) 0, 0, 0⟩ :
      (Vd d →L[ℝ] (Vd d →L[ℝ] ℝ)) × Vd d × Vd d)
      ⟨Set.mem_range_self 0, by simp, by simp⟩
  have hC₂ : ∀ x, ‖fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) x‖ ≤ C₂ := by
    intro x
    refine ContinuousLinearMap.opNorm_le_of_unit_norm
      (f := fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) x) hnnC₂ fun y hy => ?_
    refine ContinuousLinearMap.opNorm_le_of_unit_norm
      (f := fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) x y) hnnC₂ fun z hz => ?_
    have hy' : y ∈ Metric.closedBall (0 : Vd d) 1 := by
      simpa [Metric.mem_closedBall] using hy.le
    have hz' : z ∈ Metric.closedBall (0 : Vd d) 1 := by
      simpa [Metric.mem_closedBall] using hz.le
    exact hC₂bound (⟨fderiv ℝ (fun z : Vd d => fderiv ℝ (bump d) z) x, y, z⟩ :
      (Vd d →L[ℝ] (Vd d →L[ℝ] ℝ)) × Vd d × Vd d)
      ⟨Set.mem_range_self x, hy', hz'⟩
  have hC₁nn : 0 ≤ C₁ := le_trans (norm_nonneg _) (hC₁ 0)
  -- `hnnC₂` (not `le_trans (norm_nonneg _) (hC₂ 0)`): `hC₂` is now stated with
  -- the continuous-linear map's own `Norm` instance, which `norm_nonneg`'s
  -- `SeminormedAddGroup.toNorm` does not unify with syntactically.
  have hC₂nn : 0 ≤ C₂ := hnnC₂
  refine ⟨max C₁ (d * C₂), le_trans hC₁nn (le_max_left _ _), fun R hR x => ?_⟩
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut d R) := contDiff_cut R
  -- the first-derivative bound
  have hfirst : ∀ j : Fin d, ‖dcoord j (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ C₁ / R := by
    intro j
    rw [dcoord_ofReal hcutC j x]
    have hnorm : ‖kinDir d j‖ = 1 := by
      simp [kinDir, EuclideanSpace.norm_single]
    have hle : ‖fderiv ℝ (cut d R) x (kinDir d j)‖ ≤ ‖fderiv ℝ (cut d R) x‖ := by
      simpa [hnorm] using (fderiv ℝ (cut d R) x).le_opNorm (kinDir d j)
    have hcomp : ‖fderiv ℝ (cut d R) x‖ ≤ C₁ * R⁻¹ := by
      rw [fderiv_cut]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      exact mul_le_mul (hC₁ _) (norm_scaleCLM_le hRpos) (norm_nonneg _) hC₁nn
    have : ‖((fderiv ℝ (cut d R) x (kinDir d j) : ℝ) : ℂ)‖
        = ‖fderiv ℝ (cut d R) x (kinDir d j)‖ := by
      simp [Complex.norm_real]
    rw [this]
    calc ‖fderiv ℝ (cut d R) x (kinDir d j)‖ ≤ ‖fderiv ℝ (cut d R) x‖ := hle
      _ ≤ C₁ * R⁻¹ := hcomp
      _ = C₁ / R := by field_simp
  -- the second-derivative (Laplacian) bound
  have hsecond : ∀ j : Fin d,
      ‖dcoord j (dcoord j (fun y => ((cut d R y : ℝ) : ℂ))) x‖ ≤ C₂ / R ^ 2 := by
    intro j
    have hcoe : dcoord j (fun z : Vd d => ((cut d R z : ℝ) : ℂ))
        = fun y : Vd d => ((fderiv ℝ (cut d R) y (kinDir d j) : ℝ) : ℂ) := by
      funext y
      exact dcoord_ofReal hcutC j y
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) := by
      have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (cut d R) y) :=
        hcutC.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
      exact (ContinuousLinearMap.apply ℝ ℝ (kinDir d j)).contDiff.comp hfd
    rw [hcoe, dcoord_ofReal hsm j x]
    have hnorm : ‖kinDir d j‖ = 1 := by
      simp [kinDir, EuclideanSpace.norm_single]
    have hev : fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x
        = (ContinuousLinearMap.apply ℝ ℝ (kinDir d j)).comp
            (fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x) := by
      have hfd : DifferentiableAt ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x := by
        have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => fderiv ℝ (cut d R) y) :=
          hcutC.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_rfl
        exact (h.differentiable (by simp)) x
      exact (((ContinuousLinearMap.apply ℝ ℝ
        (kinDir d j)).hasFDerivAt).comp x hfd.hasFDerivAt).fderiv
    have hb : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x‖ ≤ C₂ * (R⁻¹ * R⁻¹) := by
      rw [fderiv_fderiv_cut]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      have hflip : ‖((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R))‖ ≤ R⁻¹ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun L => ?_
        have h1 : ‖L.comp (scaleCLM d R)‖ ≤ ‖L‖ * ‖scaleCLM d R‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        have h2 : ‖L‖ * ‖scaleCLM d R‖ ≤ ‖L‖ * R⁻¹ :=
          mul_le_mul_of_nonneg_left (norm_scaleCLM_le hRpos) (norm_nonneg _)
        calc ‖((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R)) L‖
            = ‖L.comp (scaleCLM d R)‖ := rfl
          _ ≤ ‖L‖ * R⁻¹ := le_trans h1 h2
          _ = R⁻¹ * ‖L‖ := by ring
      have hinner : ‖(fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y)
          (scaleCLM d R x)).comp (scaleCLM d R)‖ ≤ C₂ * R⁻¹ := by
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        exact mul_le_mul (hC₂ _) (norm_scaleCLM_le hRpos) (norm_nonneg _) hC₂nn
      -- `opNorm_nonneg` (not `norm_nonneg _`): the bound is on a *nested* CLM
      -- norm, whose `Norm` instance is `ContinuousLinearMap.hasOpNorm`, not a
      -- `SeminormedAddGroup.toNorm` projection.
      have := mul_le_mul hflip hinner (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      calc ‖((ContinuousLinearMap.compL ℝ (Vd d) (Vd d) ℝ).flip (scaleCLM d R))‖ *
            ‖(fderiv ℝ (fun y : Vd d => fderiv ℝ (bump d) y)
              (scaleCLM d R x)).comp (scaleCLM d R)‖
          ≤ R⁻¹ * (C₂ * R⁻¹) := this
        _ = C₂ * (R⁻¹ * R⁻¹) := by ring
    have hfin : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖
        ≤ C₂ * (R⁻¹ * R⁻¹) := by
      have h1 : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖
          ≤ ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x‖ := by
        simpa [hnorm] using
          (fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x).le_opNorm (kinDir d j)
      have h2 : ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x‖
          ≤ ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x‖ := by
        rw [hev]
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        have : ‖ContinuousLinearMap.apply ℝ ℝ (kinDir d j)‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
          simpa [hnorm] using L.le_opNorm (kinDir d j)
        nlinarith [norm_nonneg (fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y) x),
          norm_nonneg (ContinuousLinearMap.apply ℝ ℝ (kinDir d j))]
      linarith
    have hcast : ‖((fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)
        : ℝ) : ℂ)‖
        = ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖ := by
      simp [Complex.norm_real]
    rw [hcast]
    calc ‖fderiv ℝ (fun y : Vd d => fderiv ℝ (cut d R) y (kinDir d j)) x (kinDir d j)‖
        ≤ C₂ * (R⁻¹ * R⁻¹) := hfin
      _ = C₂ / R ^ 2 := by field_simp
  refine ⟨fun j => le_trans (hfirst j) (by gcongr; exact le_max_left _ _), ?_⟩
  have hsum : ‖lapC (fun y => ((cut d R y : ℝ) : ℂ)) x‖ ≤ ∑ _j : Fin d, C₂ / R ^ 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun j _ => hsecond j
  have hsimp : ∑ _j : Fin d, C₂ / R ^ 2 = (d : ℝ) * C₂ / R ^ 2 := by
    simp [Finset.sum_const, mul_div_assoc]
  rw [hsimp] at hsum
  refine le_trans hsum ?_
  gcongr
  exact le_max_right _ _

/-! ## 6. The cut-off approximation of a Gauss-core vector -/

/-- The cut-off of a core vector. -/
def cutFun (R : ℝ) (p : MvPolynomial (Fin d) ℂ) : Vd d → ℂ :=
  fun x => ((cut d R x : ℝ) : ℂ) * pgFun p x

theorem contDiff_cutFun (R : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutFun R p) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_cut R)).mul (contDiff_pgFun p)

theorem hasCompactSupport_cutFun {R : ℝ} (hR : 0 < R) (p : MvPolynomial (Fin d) ℂ) :
    HasCompactSupport (cutFun R p) := by
  have h : HasCompactSupport (fun x : Vd d => ((cut d R x : ℝ) : ℂ)) :=
    (hasCompactSupport_cut hR).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact h.mul_right

/-- The cut-off of a core vector, as an element of the compactly supported smooth core. -/
def cutCore (R : ℝ) (hR : 0 < R) (p : MvPolynomial (Fin d) ℂ) : ccSchwartz (Vd d) :=
  ⟨(hasCompactSupport_cutFun hR p).toSchwartzMap (contDiff_cutFun R p),
    hasCompactSupport_cutFun hR p⟩

@[simp] theorem cutCore_apply (R : ℝ) (hR : 0 < R) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    ((cutCore R hR p : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)) x
      = ((cut d R x : ℝ) : ℂ) * pgFun p x := rfl

/-! ### `L²` tails -/

/-- **The `L²` tail of a square-integrable function vanishes**: `∫_{‖x‖ > n} |g|² → 0`. -/
theorem tendsto_tailNorm {g : Vd d → ℝ} (hg : MemLp g 2 (volume : Measure (Vd d))) :
    Filter.Tendsto
      (fun n : ℕ => (eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2
        (volume : Measure (Vd d))).toReal) Filter.atTop (nhds 0) := by
  set μ : Measure (Vd d) := volume with hμ
  have hmeasS : ∀ n : ℕ, MeasurableSet ({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ) :=
    fun n => (measurableSet_le (by fun_prop) measurable_const).compl
  have hrw : ∀ n : ℕ, eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2 μ
      = (∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num]
  have hlim : Filter.Tendsto
      (fun n : ℕ => ∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ)
      Filter.atTop (nhds 0) := by
    have hdom : ∀ n : ℕ,
        (fun z => ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ))
          ≤ᵐ[μ] fun z => ‖g z‖ₑ ^ (2 : ℝ) := by
      intro n
      filter_upwards with z
      by_cases h : z ∈ ({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ)
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]; simp
    have hbdd : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
      intro hcon
      have h := hg.2
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
      rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, hcon] at h
      simp [ENNReal.top_rpow_of_pos] at h
    have hae : ∀ᵐ z ∂μ, Filter.Tendsto
        (fun n : ℕ => ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      filter_upwards with z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ENNReal))
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hz : z ∈ {z : Vd d | ‖z‖ ≤ (n : ℝ)} := le_trans hN (by exact_mod_cast hn)
      rw [Set.indicator_of_notMem (by simpa using hz)]
      simp
    have hdct := tendsto_lintegral_of_dominated_convergence' (μ := μ) (f := fun _ => (0 : ENNReal))
      (fun z => ‖g z‖ₑ ^ (2 : ℝ))
      (fun n => ((hg.1.indicator (hmeasS n)).enorm).pow_const _)
      hdom hbdd hae
    simpa using hdct
  have h2 : Filter.Tendsto
      (fun n : ℕ => eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2 μ)
      Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2 μ)
      = fun n : ℕ =>
          (∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      funext n
      exact hrw n
    have hlim' : Filter.Tendsto
        (fun n : ℕ => (∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ)
          ^ (1 / (2 : ℝ)))
        Filter.atTop (nhds 0) := by
      have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
      show Filter.Tendsto
          ((fun a : ENNReal => a ^ (1 / 2)) ∘ fun n : ℕ =>
            ∫⁻ z, ‖(({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) z‖ₑ ^ (2 : ℝ) ∂μ)
          Filter.atTop (nhds 0)
      simpa using h
    rw [heq]
    exact hlim'
  have ht2 : Filter.Tendsto ENNReal.toReal (nhds 0) (nhds 0) :=
    ENNReal.tendsto_toReal (by simp)
  have h3 := ht2.comp h2
  show Filter.Tendsto
      (ENNReal.toReal ∘ fun n : ℕ => eLpNorm (({z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ).indicator g) 2 μ)
      Filter.atTop (nhds 0)
  simpa using h3

/-- A vector dominated by the tail of a square-integrable majorant has small norm. -/
theorem norm_le_tailNorm {u : L2d d} {S : Set (Vd d)} {g : Vd d → ℝ}
    (hg : MemLp g 2 (volume : Measure (Vd d)))
    (h : ∀ᵐ z ∂(volume : Measure (Vd d)), ‖(u : Vd d → ℂ) z‖ ≤ ‖S.indicator g z‖) :
    ‖u‖ ≤ (eLpNorm (S.indicator g) 2 (volume : Measure (Vd d))).toReal := by
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono ((eLpNorm_indicator_le g).trans_lt hg.2).ne (eLpNorm_mono_ae h)

/-! ### The cut-off is locally constant inside the ball -/

theorem cut_eventuallyEq_one {R : ℝ} {x : Vd d} (hx : ‖x‖ < R) :
    (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (1 : ℂ) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg x) hx
  have hopen : IsOpen {y : Vd d | ‖y‖ < R} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  rw [cut_eq_one hRpos (le_of_lt hy)]
  norm_num

theorem dcoord_cut_eq_zero {R : ℝ} {x : Vd d} (hx : ‖x‖ < R) (j : Fin d) :
    dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) x = 0 := by
  simp only [dcoord]
  rw [(cut_eventuallyEq_one hx).fderiv_eq]
  simp

theorem lapC_cut_eq_zero {R : ℝ} {x : Vd d} (hx : ‖x‖ < R) :
    lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) x = 0 := by
  have hopen : IsOpen {y : Vd d | ‖y‖ < R} := isOpen_lt (by fun_prop) continuous_const
  refine Finset.sum_eq_zero fun j _ => ?_
  have hev : dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact dcoord_cut_eq_zero hy j
  simp only [dcoord]
  rw [hev.fderiv_eq]
  simp

/-! ### Representatives of the two Hamiltonians -/

theorem kinCc_apply (f : ccSchwartz (Vd d)) :
    kinCc d (ccEquiv (Vd d) f)
      = (kinOp d (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d)) := by
  have hincl : Submodule.inclusion (ccDomain_le_schwartzDomain (E := Vd d)) (ccEquiv (Vd d) f)
      = schwartzEquiv (Vd d) ((f : 𝓢(Vd d, ℂ))) := Subtype.ext rfl
  simp only [kinCc, LinearMap.coe_comp, Function.comp_apply, hincl, opL2_apply]

theorem ccHam_coeFn (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz (Vd d)) :
    ((ccHam W hWs (ccEquiv (Vd d) f) : L2d d) : Vd d → ℂ)
      =ᵐ[volume] fun z => -lapC (fun y : Vd d => (f : 𝓢(Vd d, ℂ)) y) z
        + ((W z : ℝ) : ℂ) * (f : 𝓢(Vd d, ℂ)) z := by
  have h1 : ccHam W hWs (ccEquiv (Vd d) f)
      = (kinOp d (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d))
        + (mulCc W hWs f).toLp 2 (volume : Measure (Vd d)) := by
    simp only [ccHam, LinearMap.add_apply, kinCc_apply, opCc_apply]
  rw [h1]
  filter_upwards [Lp.coeFn_add ((kinOp d (f : 𝓢(Vd d, ℂ))).toLp 2 (volume : Measure (Vd d)))
      ((mulCc W hWs f).toLp 2 (volume : Measure (Vd d))),
    (kinOp d (f : 𝓢(Vd d, ℂ))).coeFn_toLp 2 (volume : Measure (Vd d)),
    (mulCc W hWs f).coeFn_toLp 2 (volume : Measure (Vd d))] with z hz h2 h3
  rw [hz, Pi.add_apply, h2, h3, kinOp_apply_eq, mulCc_apply]

theorem hamCore_coeFn (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W)
    (p : MvPolynomial (Fin d) ℂ) :
    ((hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ : L2d d) : Vd d → ℂ)
      =ᵐ[volume] fun z => pgFun (kinPoly p) z + ((W z : ℝ) : ℂ) * pgFun p z := by
  rw [hamCore_pgLp]
  simp only [hamPoly]
  filter_upwards [Lp.coeFn_add (pgLp (kinPoly p)) (potLp W hWc hWb p), pgLp_coeFn (kinPoly p),
    potLp_coeFn W hWc hWb p] with z hz h2 h3
  rw [hz, Pi.add_apply, h2, h3]

/-! ### The pointwise error of the cut-off -/

/-- The square-integrable majorant of all the cut-off error terms. -/
def majorant (W : Vd d → ℝ) (K : ℝ) (p : MvPolynomial (Fin d) ℂ) (z : Vd d) : ℝ :=
  ‖pgFun (kinPoly p) z‖ + K * ‖pgFun p z‖
    + 2 * K * (∑ j : Fin d, ‖pgFun (coreD j p) z‖) + ‖((W z : ℝ) : ℂ) * pgFun p z‖

theorem sum_norm_coreD_nonneg (p : MvPolynomial (Fin d) ℂ) (z : Vd d) :
    0 ≤ ∑ j : Fin d, ‖pgFun (coreD j p) z‖ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem majorant_nonneg (W : Vd d → ℝ) {K : ℝ} (hK : 0 ≤ K) (p : MvPolynomial (Fin d) ℂ)
    (z : Vd d) : 0 ≤ majorant W K p z :=
  add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)))
    (mul_nonneg (by linarith) (sum_norm_coreD_nonneg p z))) (norm_nonneg _)

theorem memLp_majorant (W : Vd d → ℝ) (hWc : Continuous W) (hWb : ExpBounded W) (K : ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    MemLp (majorant W K p) 2 (volume : Measure (Vd d)) := by
  have h1 : MemLp (fun z : Vd d => ‖pgFun (kinPoly p) z‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun (kinPoly p)).norm
  have h2 : MemLp (fun z : Vd d => K * ‖pgFun p z‖) 2 (volume : Measure (Vd d)) :=
    (memLp_pgFun p).norm.const_mul K
  have h3 : MemLp (fun z : Vd d => ∑ j : Fin d, ‖pgFun (coreD j p) z‖) 2
      (volume : Measure (Vd d)) := by
    have h := memLp_finset_sum' (μ := (volume : Measure (Vd d))) (p := 2)
      (Finset.univ : Finset (Fin d))
      (f := fun (j : Fin d) (z : Vd d) => ‖pgFun (coreD j p) z‖)
      (fun j _ => (memLp_pgFun (coreD j p)).norm)
    have heq : (fun z : Vd d => ∑ j : Fin d, ‖pgFun (coreD j p) z‖)
        = ∑ j : Fin d, (fun z : Vd d => ‖pgFun (coreD j p) z‖) := by
      funext z
      simp
    rw [heq]
    exact h
  have h4 : MemLp (fun z : Vd d => ‖((W z : ℝ) : ℂ) * pgFun p z‖) 2
      (volume : Measure (Vd d)) := (memLp_mul_pgFun_of_expBounded hWc hWb p).norm
  exact ((h1.add h2).add (h3.const_mul (2 * K))).add h4

/-- The pointwise graph error made by cutting a Gauss-core vector off at radius `R`. -/
def cutErr (W : Vd d → ℝ) (R : ℝ) (p : MvPolynomial (Fin d) ℂ) (z : Vd d) : ℂ :=
  (((cut d R z : ℝ) : ℂ) - 1) * pgFun (kinPoly p) z
    - pgFun p z * lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z
    - 2 * ∑ j : Fin d,
        dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z
    + (((cut d R z : ℝ) : ℂ) - 1) * (((W z : ℝ) : ℂ) * pgFun p z)

/-- The pointwise commutator identity for the cut-off. -/
theorem cut_error_eq (W : Vd d → ℝ) {R : ℝ} (p : MvPolynomial (Fin d) ℂ) (z : Vd d) :
    -lapC (cutFun R p) z + ((W z : ℝ) : ℂ) * cutFun R p z
        - (pgFun (kinPoly p) z + ((W z : ℝ) : ℂ) * pgFun p z)
      = cutErr W R p z := by
  have hcutC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_cut R)
  have hlap := lapC_mul hcutC (contDiff_pgFun p) z
  have hpsi : lapC (pgFun p) z = -pgFun (kinPoly p) z := congrFun (lapC_pgFun p) z
  have hcutFun : cutFun R p = fun y : Vd d => ((cut d R y : ℝ) : ℂ) * pgFun p y := rfl
  rw [hcutFun, hlap, hpsi]
  simp only [dcoord_pgFun, cutErr]
  ring

/-- Inside the ball of radius `R` the cut-off does nothing at all. -/
theorem cutErr_eq_zero (W : Vd d → ℝ) {R : ℝ} (p : MvPolynomial (Fin d) ℂ) {z : Vd d}
    (hz : ‖z‖ < R) : cutErr W R p z = 0 := by
  have h1 : ((cut d R z : ℝ) : ℂ) = 1 := by
    rw [cut_eq_one (lt_of_le_of_lt (norm_nonneg z) hz) (le_of_lt hz)]
    norm_num
  have h2 : lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z = 0 := lapC_cut_eq_zero hz
  have h3 : ∑ j : Fin d,
      dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [dcoord_cut_eq_zero hz j, zero_mul]
  simp only [cutErr, h1, h2, h3]
  ring

/-- **The pointwise error estimate.** -/
theorem norm_cutErr_le (W : Vd d → ℝ) {C K R : ℝ} (hC0 : 0 ≤ C) (hCK : C ≤ K) (hR1 : 1 ≤ R)
    (p : MvPolynomial (Fin d) ℂ) (z : Vd d)
    (hd1 : ∀ j : Fin d, ‖dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z‖ ≤ C / R)
    (hd2 : ‖lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z‖ ≤ C / R ^ 2) :
    ‖cutErr W R p z‖ ≤ majorant W K p z := by
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hCRK : C / R ≤ K := by
    have h : C / R ≤ C := by
      rw [div_le_iff₀ hRpos]
      nlinarith
    linarith
  have hCR2K : C / R ^ 2 ≤ K := by
    have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
    have h : C / R ^ 2 ≤ C := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨hc0, hc1⟩ := cut_mem_Icc (d := d) (R := R) z
  have habs : |cut d R z - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hcoe : ((cut d R z : ℝ) : ℂ) - 1 = (((cut d R z - 1 : ℝ)) : ℂ) := by push_cast; ring
  set e1 : ℂ := (((cut d R z : ℝ) : ℂ) - 1) * pgFun (kinPoly p) z with he1
  set e2 : ℂ := pgFun p z * lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z with he2
  set e3 : ℂ := 2 * ∑ j : Fin d,
      dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z with he3
  set e4 : ℂ := (((cut d R z : ℝ) : ℂ) - 1) * (((W z : ℝ) : ℂ) * pgFun p z) with he4
  have hsplit : ‖e1 - e2 - e3 + e4‖ ≤ ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ := by
    have s1 := norm_add_le (e1 - e2 - e3) e4
    have s2 := norm_sub_le (e1 - e2) e3
    have s3 := norm_sub_le e1 e2
    linarith
  have hb1 : ‖e1‖ ≤ ‖pgFun (kinPoly p) z‖ := by
    rw [he1, hcoe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (pgFun (kinPoly p) z)]
  have hb2 : ‖e2‖ ≤ K * ‖pgFun p z‖ := by
    rw [he2, norm_mul]
    have h := mul_le_mul_of_nonneg_left (le_trans hd2 hCR2K) (norm_nonneg (pgFun p z))
    calc ‖pgFun p z‖ * ‖lapC (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z‖
        ≤ ‖pgFun p z‖ * K := h
      _ = K * ‖pgFun p z‖ := by ring
  have hb3 : ‖e3‖ ≤ 2 * K * (∑ j : Fin d, ‖pgFun (coreD j p) z‖) := by
    have hinner : ‖∑ j : Fin d,
        dcoord j (fun y : Vd d => ((cut d R y : ℝ) : ℂ)) z * pgFun (coreD j p) z‖
          ≤ ∑ j : Fin d, K * ‖pgFun (coreD j p) z‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (le_trans (hd1 j) hCRK) (norm_nonneg _)
    rw [← Finset.mul_sum] at hinner
    rw [he3, norm_mul]
    have h2c : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2c]
    nlinarith [sum_norm_coreD_nonneg p z]
  have hb4 : ‖e4‖ ≤ ‖((W z : ℝ) : ℂ) * pgFun p z‖ := by
    rw [he4, hcoe, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg (((W z : ℝ) : ℂ) * pgFun p z)]
  have hgoal : cutErr W R p z = e1 - e2 - e3 + e4 := rfl
  rw [hgoal, majorant]
  linarith

/-- The vector itself moves by at most the majorant. -/
theorem norm_cutFun_sub_le (W : Vd d → ℝ) {K R : ℝ} (hK1 : 1 ≤ K)
    (p : MvPolynomial (Fin d) ℂ) (z : Vd d) :
    ‖cutFun R p z - pgFun p z‖ ≤ majorant W K p z := by
  obtain ⟨hc0, hc1⟩ := cut_mem_Icc (d := d) (R := R) z
  have hfac : cutFun R p z - pgFun p z = (((cut d R z - 1 : ℝ)) : ℂ) * pgFun p z := by
    simp only [cutFun]
    push_cast
    ring
  have hle : ‖cutFun R p z - pgFun p z‖ ≤ ‖pgFun p z‖ := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs : |cut d R z - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    nlinarith [norm_nonneg (pgFun p z)]
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hrest : 0 ≤ 2 * K * (∑ j : Fin d, ‖pgFun (coreD j p) z‖) :=
    mul_nonneg (by linarith) (sum_norm_coreD_nonneg p z)
  have hKmul : ‖pgFun p z‖ ≤ K * ‖pgFun p z‖ := by nlinarith [norm_nonneg (pgFun p z)]
  rw [majorant]
  have hn1 : 0 ≤ ‖pgFun (kinPoly p) z‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖((W z : ℝ) : ℂ) * pgFun p z‖ := norm_nonneg _
  linarith

/-- **The cut-off approximation.**  Every Gauss–polynomial core vector is approximated, in
the graph norm of `−Δ + W`, by compactly supported smooth functions. -/
theorem exists_cc_graph_approx (W : Vd d → ℝ) (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hWc : Continuous W) (hWb : ExpBounded W)
    (x : polyGaussCore (d := d)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ccDomain (Vd d), ‖(y : L2d d) - (x : L2d d)‖ < ε ∧
      ‖ccHam W hWs y - hamCore W hWc hWb x‖ < ε := by
  classical
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  obtain ⟨C, hC0, hCbound⟩ := exists_cut_derivative_bounds d
  have hK1 : (1 : ℝ) ≤ C + 1 := by linarith
  have hGmem := memLp_majorant W hWc hWb (C + 1) p
  have hGnn := majorant_nonneg W (K := C + 1) (by linarith) p
  -- choose a radius beyond which the tail of the majorant is small
  obtain ⟨n, hnlt, hn1⟩ :=
    (((tendsto_tailNorm hGmem).eventually (gt_mem_nhds hε)).and
      (Filter.eventually_ge_atTop 1)).exists
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hRpos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hR1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hball : ∀ z : Vd d, ‖z‖ ≤ (n : ℝ) → ‖z‖ < 2 * (n : ℝ) := by
    intro z hz
    linarith
  refine ⟨ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p), ?_, ?_⟩
  · -- the vectors themselves are close
    refine lt_of_le_of_lt
      (norm_le_tailNorm (S := {z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ) hGmem ?_) hnlt
    filter_upwards [Lp.coeFn_sub
        ((ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p) : ccDomain (Vd d)) : L2d d) (pgLp p),
      ((cutCore (2 * (n : ℝ)) hRpos p : ccSchwartz (Vd d)) : 𝓢(Vd d, ℂ)).coeFn_toLp 2
        (volume : Measure (Vd d)),
      pgLp_coeFn p] with z h1 h2 h3
    have hstep : ((((ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p) : ccDomain (Vd d)) : L2d d)
        - (pgLp p) : L2d d) : Vd d → ℂ) z = cutFun (2 * (n : ℝ)) p z - pgFun p z := by
      rw [h1, Pi.sub_apply, h3]
      rw [show (((ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p) : ccDomain (Vd d)) : L2d d) :
          Vd d → ℂ) z = cutFun (2 * (n : ℝ)) p z from h2]
    rw [hstep]
    by_cases hz : ‖z‖ ≤ (n : ℝ)
    · have hzero : cutFun (2 * (n : ℝ)) p z - pgFun p z = 0 := by
        simp only [cutFun]
        rw [cut_eq_one hRpos (le_of_lt (hball z hz))]
        push_cast
        ring
      rw [hzero, Set.indicator_of_notMem (by simpa using hz)]
      simp
    · rw [Set.indicator_of_mem (by simpa using hz), Real.norm_eq_abs, abs_of_nonneg (hGnn z)]
      exact norm_cutFun_sub_le W hK1 p z
  · -- the images are close
    refine lt_of_le_of_lt
      (norm_le_tailNorm (S := {z : Vd d | ‖z‖ ≤ (n : ℝ)}ᶜ) hGmem ?_) hnlt
    filter_upwards [Lp.coeFn_sub
        (ccHam W hWs (ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p)))
        (hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩),
      ccHam_coeFn W hWs (cutCore (2 * (n : ℝ)) hRpos p),
      hamCore_coeFn W hWc hWb p] with z h1 h2 h3
    have hstep : ((ccHam W hWs (ccEquiv (Vd d) (cutCore (2 * (n : ℝ)) hRpos p))
        - hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ : L2d d) : Vd d → ℂ) z
        = cutErr W (2 * (n : ℝ)) p z := by
      rw [h1, Pi.sub_apply, h2, h3]
      exact cut_error_eq W p z
    rw [hstep]
    by_cases hz : ‖z‖ ≤ (n : ℝ)
    · rw [cutErr_eq_zero W p (hball z hz), Set.indicator_of_notMem (by simpa using hz)]
      simp
    · rw [Set.indicator_of_mem (by simpa using hz), Real.norm_eq_abs, abs_of_nonneg (hGnn z)]
      obtain ⟨hd1, hd2⟩ := hCbound (2 * (n : ℝ)) hR1 z
      exact norm_cutErr_le W hC0 (by linarith) hR1 p z hd1 hd2

/-! ## 7. The transfer theorem and the `R + αR²` instances -/

/-- **Transfer.**  Essential self-adjointness on the Gauss–polynomial core implies it on the
compactly supported smooth core. -/
theorem ccHam_essentiallySelfAdjoint_of_core (W : Vd d → ℝ)
    (hWs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWc : Continuous W) (hWb : ExpBounded W)
    (hcore : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (hamCore W hWc hWb)) :
    EssentiallySelfAdjointOn (ccDomain (Vd d)) (ccHam W hWs) :=
  essentiallySelfAdjointOn_of_graphApprox _ _
    (fun x _ hε => exists_cc_graph_approx W hWs hWc hWb x hε) hcore

theorem contDiff_harmW (d : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (harmW (d := d)) := by
  unfold harmW
  exact (contDiff_norm_sq ℝ).div_const 4

/-- **The one-particle `R + αR²` Hamiltonian on the compactly supported smooth core.**
`−Δ + ‖x‖²/4 + V` is essentially self-adjoint there for every smooth `V` dominated by
`a‖x‖²/4 + b` with `a < 1`. -/
theorem qgOneParticleCc_esa {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) :
    EssentiallySelfAdjointOn (ccDomain (Vd d))
      (ccHam (fun x => harmW x + V x) ((contDiff_harmW d).add hVs)) := by
  have hVc : Continuous V := hVs.continuous
  have hsc : Continuous fun x : Vd d => harmW x + V x := continuous_harmW.add hVc
  have hsb : ExpBounded fun x : Vd d => harmW x + V x := by
    refine expBounded_of_le_harm (a := 1 + a) (b := b) (by linarith) hb fun x => ?_
    have hharm : (0 : ℝ) ≤ harmW x := by unfold harmW; positivity
    have h := hV x
    have h2 := abs_add_le (harmW x) (V x)
    have h3 : |harmW x| = harmW x := abs_of_nonneg hharm
    rw [h3] at h2
    nlinarith
  exact ccHam_essentiallySelfAdjoint_of_core _ _ hsc hsb
    (harmonic_add_subquadratic_essentiallySelfAdjoint hVc ha ha1 hb hV hsc hsb)

/-- The unitary group of the one-particle Hamiltonian, on the compactly supported core. -/
theorem qgOneParticleCc_stone_flow {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ x, |V x| ≤ a * harmW x + b) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (ccHam (fun x => harmW x + V x) ((contDiff_harmW d).add hVs)) T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (ccHam_symmetricOn _ _)
    (qgOneParticleCc_esa hVs ha ha1 hb hV)

/-! ## 8. The gauge-fixed `R + αR²` instances on the compactly supported core -/

/-- Equal potentials give the same Hamiltonian on the compactly supported core. -/
theorem ccHam_congr {W W' : Vd d → ℝ} (h : W = W')
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hW' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W') :
    ccHam W hW = ccHam W' hW' := by
  subst h; rfl

theorem contDiff_coord (d : ℕ) (i : Fin d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Vd d => x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem contDiff_confW (M alpha : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (confW M alpha) := by
  have h : confW M alpha
      = fun x : Vd 1 => -(M ^ 2 / 2) * (x 0) + alpha * (x 0) ^ 2 := rfl
  rw [h]
  exact ((contDiff_coord 1 0).const_smul (-(M ^ 2 / 2))).add
    (((contDiff_coord 1 0).pow 2).const_smul alpha)

/-- **The regularized conformal mode of the `R + αR²` Hamiltonian is essentially
self-adjoint on the compactly supported smooth core of `L²(ℝ)`**, for `0 < α < 1/2`. -/
theorem confVCc_esa (M alpha : ℝ) (h0 : 0 < alpha) (h2 : alpha < 1 / 2) :
    EssentiallySelfAdjointOn (ccDomain (Vd 1)) (ccHam (confW M alpha) (contDiff_confW M alpha)) :=
  ccHam_essentiallySelfAdjoint_of_core _ _ (continuous_confW M alpha) (expBounded_confW M alpha)
    (confV_essentiallySelfAdjoint M alpha h0 h2)

/-- The unitary group of the conformal mode on the compactly supported core. -/
theorem confVCc_stone_flow (M alpha : ℝ) (h0 : 0 < alpha) (h2 : alpha < 1 / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d 1)) (U : ℝ → (L2d 1 →L[ℂ] L2d 1)),
      IsSelfAdjointExtension (ccHam (confW M alpha) (contDiff_confW M alpha)) T.op ∧
        IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (ccHam_symmetricOn _ _) (confVCc_esa M alpha h0 h2)

theorem contDiff_sectorQuadW (M alpha mu : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sectorQuadW M alpha mu) := by
  have h : sectorQuadW M alpha mu
      = fun x : Vd 2 => (-(M ^ 2 / 2) * (x 0) + alpha * (x 0) ^ 2) + mu * (x 1) ^ 2 := rfl
  rw [h]
  exact (((contDiff_coord 2 0).const_smul (-(M ^ 2 / 2))).add
    (((contDiff_coord 2 0).pow 2).const_smul alpha)).add
      (((contDiff_coord 2 1).pow 2).const_smul mu)

/-- **The reduced `(R_c, φ)` sector with a quadratic scalaron term is essentially
self-adjoint on the compactly supported smooth core of `L²(ℝ²)`**, for `0 < α < 1/2` and
`0 < μ < 1/2`. -/
theorem sectorQuadCc_esa (M alpha mu : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2)
    (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    EssentiallySelfAdjointOn (ccDomain (Vd 2))
      (ccHam (sectorQuadW M alpha mu) (contDiff_sectorQuadW M alpha mu)) :=
  ccHam_essentiallySelfAdjoint_of_core _ _ (continuous_sectorQuadW M alpha mu)
    (expBounded_sectorQuadW M alpha mu)
    (sectorQuad_essentiallySelfAdjoint M alpha mu ha0 ha2 hm0 hm2)

/-- The unitary group of the reduced sector on the compactly supported core. -/
theorem sectorQuadCc_stone_flow (M alpha mu : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2)
    (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d 2)) (U : ℝ → (L2d 2 →L[ℂ] L2d 2)),
      IsSelfAdjointExtension (ccHam (sectorQuadW M alpha mu) (contDiff_sectorQuadW M alpha mu))
        T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ ccDomain_dense (ccHam_symmetricOn _ _)
    (sectorQuadCc_esa M alpha mu ha0 ha2 hm0 hm2)

/-! ## 9. The `n`-particle sector and the finite-particle Fock space

The `n`-particle configuration space is `(ℝᵈ)ⁿ = ℝ^{n·d}`, and the `n`-particle Hamiltonian
is `∑ₖ (−Δ_k + U(x_k))`.  Its kinetic part is the full Laplacian of `ℝ^{n·d}` and, when
`U = ‖·‖²/4 + V`, its potential is again `‖x‖²/4 + (a subquadratic perturbation)` — with the
*same* constant `a` — so the one-particle theorem applies verbatim in dimension `n·d`.  The
finite-particle Fock space is the `ℓ²`-direct sum of the sectors, and essential
self-adjointness is fibrewise (`BookProof.DirectSumEsa`). -/

/-- The `k`-th particle's coordinates, as a linear map `ℝ^{n·d} → ℝᵈ`. -/
def partLM (n d : ℕ) (k : Fin n) : Vd (n * d) →ₗ[ℝ] Vd d where
  toFun x := (WithLp.toLp 2 (fun i : Fin d => x (finProdFinEquiv (k, i))) : Vd d)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] theorem partLM_apply (n d : ℕ) (k : Fin n) (x : Vd (n * d)) (i : Fin d) :
    (partLM n d k x) i = x (finProdFinEquiv (k, i)) := rfl

theorem contDiff_partLM (n d : ℕ) (k : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (partLM n d k) :=
  (LinearMap.toContinuousLinearMap (partLM n d k)).contDiff

/-- **The harmonic term is exactly additive over the particles.** -/
theorem sum_harmW_partLM (n d : ℕ) (x : Vd (n * d)) :
    ∑ k : Fin n, harmW (partLM n d k x) = harmW x := by
  have hsq : ∑ k : Fin n, ‖partLM n d k x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [norm_sq_eq_sum, partLM_apply]
    have h : ∑ ki : Fin n × Fin d, (x (finProdFinEquiv ki)) ^ 2
        = ∑ k : Fin n, ∑ i : Fin d, (x (finProdFinEquiv (k, i))) ^ 2 :=
      Fintype.sum_prod_type _
    rw [← h]
    exact Fintype.sum_equiv finProdFinEquiv _ _ (fun a => rfl)
  simp only [harmW, ← Finset.sum_div, hsq]

/-- The `n`-particle potential built from a one-particle potential `U`. -/
def nParticleW (U : Vd d → ℝ) (n : ℕ) : Vd (n * d) → ℝ :=
  fun x => ∑ k : Fin n, U (partLM n d k x)

theorem contDiff_nParticleW {U : Vd d → ℝ} (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (nParticleW U n) := by
  exact ContDiff.sum fun k _ => hU.comp (contDiff_partLM n d k)

/-- The `n`-particle potential of `‖·‖²/4 + V` is the `n·d`-dimensional harmonic potential
plus the sum of the one-particle perturbations. -/
theorem nParticleW_harm_add (V : Vd d → ℝ) (n : ℕ) :
    nParticleW (fun y => harmW y + V y) n
      = fun x : Vd (n * d) => harmW x + nParticleW V n x := by
  funext x
  simp only [nParticleW, Finset.sum_add_distrib, sum_harmW_partLM]

/-- The perturbation stays subquadratic, with the *same* coefficient `a`. -/
theorem abs_nParticleW_le {V : Vd d → ℝ} {a b : ℝ}
    (hV : ∀ y, |V y| ≤ a * harmW y + b) (n : ℕ) (x : Vd (n * d)) :
    |nParticleW V n x| ≤ a * harmW x + n * b := by
  have hstep : |∑ k : Fin n, V (partLM n d k x)| ≤ ∑ k : Fin n, |V (partLM n d k x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbound : ∑ k : Fin n, |V (partLM n d k x)|
      ≤ ∑ k : Fin n, (a * harmW (partLM n d k x) + b) :=
    Finset.sum_le_sum fun k _ => hV _
  have hsum : ∑ k : Fin n, (a * harmW (partLM n d k x) + b)
      = a * harmW x + n * b := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_harmW_partLM]
    simp [mul_comm]
  rw [nParticleW]
  linarith [hstep, hbound, hsum.le, hsum.ge]

/-- **The `n`-particle `R + αR²` Hamiltonian on the compactly supported smooth core.**
`∑ₖ (−Δ_k + ‖x_k‖²/4 + V(x_k))` is essentially self-adjoint on the compactly supported
smooth core of `L²((ℝᵈ)ⁿ)` for every smooth `V` dominated by `a‖x‖²/4 + b` with `a < 1`. -/
theorem qgNParticleCc_esa {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ y, |V y| ≤ a * harmW y + b) (n : ℕ) :
    EssentiallySelfAdjointOn (ccDomain (Vd (n * d)))
      (ccHam (nParticleW (fun y => harmW y + V y) n)
        (contDiff_nParticleW ((contDiff_harmW d).add hVs) n)) := by
  have hfun := nParticleW_harm_add V n
  have hone := qgOneParticleCc_esa (d := n * d) (V := nParticleW V n) (a := a) (b := n * b)
    (contDiff_nParticleW hVs n) ha ha1 (by positivity) (abs_nParticleW_le hV n)
  rw [ccHam_congr hfun (contDiff_nParticleW ((contDiff_harmW d).add hVs) n)
    ((contDiff_harmW (n * d)).add (contDiff_nParticleW hVs n))]
  exact hone

/-- **The finite-particle Fock space** over the `d`-dimensional one-particle sector. -/
abbrev qgFock (d : ℕ) := lp (fun n : ℕ => L2d (n * d)) 2

/-- The Fock core: the algebraic direct sum of the compactly supported smooth sector
cores. -/
def qgFockCore (d : ℕ) : Submodule ℂ (qgFock d) :=
  dsCore (fun n : ℕ => ccDomain (Vd (n * d)))

theorem qgFockCore_dense : Dense ((qgFockCore d : Submodule ℂ (qgFock d)) : Set (qgFock d)) :=
  dsCore_dense fun _ => ccDomain_dense

/-- **The second-quantised `R + αR²` Hamiltonian** on the finite-particle Fock space: on the
`n`-particle sector it is `∑ₖ (−Δ_k + ‖x_k‖²/4 + V(x_k))`. -/
def qgFockHam {V : Vd d → ℝ} (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    qgFockCore d →ₗ[ℂ] qgFock d :=
  dsOp fun n : ℕ => ccHam (nParticleW (fun y => harmW y + V y) n)
    (contDiff_nParticleW ((contDiff_harmW d).add hVs) n)

theorem qgFockHam_symmetricOn {V : Vd d → ℝ} (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    SymmetricOn (qgFockCore d) (qgFockHam hVs) :=
  dsOp_symmetricOn _ fun _ => ccHam_symmetricOn _ _

/-- **The finite-particle Fock statement.**  The second-quantised `R + αR²` Hamiltonian is
essentially self-adjoint on the algebraic direct sum of the compactly supported smooth
sector cores — the finite-particle core built from the one-particle core. -/
theorem qgFockCc_esa {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ y, |V y| ≤ a * harmW y + b) :
    EssentiallySelfAdjointOn (qgFockCore d) (qgFockHam hVs) :=
  dsOp_essentiallySelfAdjointOn _ fun n => qgNParticleCc_esa hVs ha ha1 hb hV n

/-- The unitary group of the second-quantised Hamiltonian. -/
theorem qgFockCc_stone_flow {V : Vd d → ℝ} {a b : ℝ}
    (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hV : ∀ y, |V y| ≤ a * harmW y + b) :
    ∃ (T : UnboundedSelfAdjoint (qgFock d)) (U : ℝ → (qgFock d →L[ℂ] qgFock d)),
      IsSelfAdjointExtension (qgFockHam hVs) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ qgFockCore_dense (qgFockHam_symmetricOn hVs)
    (qgFockCc_esa hVs ha ha1 hb hV)

end

end BookProof.QgOneParticleCc


