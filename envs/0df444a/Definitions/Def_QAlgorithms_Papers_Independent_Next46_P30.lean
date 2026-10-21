-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30
-- name    : QAlgorithms_Papers_Independent_Next46_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:18:18.797733+00:00
-- url     : https://prove2.me/theorems/525d622e-e381-43b0-8f55-03b4df1cd9a1
-- title:
--   Definitions for A non-smooth continuous unitary representation of a Banach-Lie group
-- statement:
--   The objects the formalized statements of *A non-smooth continuous unitary representation of a Banach-Lie group* (arXiv:0811.4234) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `intervalMeasure`: Lebesgue measure on the closed unit interval (PDF pp. 2-3). Values of representatives outside the interval are ignored by this measure.
--   - `GroupSpace`: The additive real Hilbert space G = L²([0,1],ℝ), PDF pp. 2-3.
--   - `HilbertSpace`: The complex Hilbert space H = L²([0,1],ℂ), PDF pp. 2-3.
--   - `phaseProduct`: A representative of the concrete phase product exp(i f) ξ, PDF pp. 2-3. The Lp coercions choose measurable representatives; the output is used only modulo a.e. equality.
--   - `phaseAction`: The paper's particular phase-multiplication action, not an arbitrary representation with assumed properties (PDF pp. 2-3). Unit modulus proves the product belongs to L².
--   - `smoothVectors`: The actual smooth-vector set from Definition 1.1, PDF p. 2. Every finite natural differentiability order is required over ℝ; no analytic order is used.
--   - `singularWeight`: The singular function f_lambda(t) = |t-lambda|^(-1/4), PDF p. 3. Its chosen value at t=lambda is zero, which changes no a.e. equivalence class.
-- source:
--   A non-smooth continuous unitary representation of a Banach-Lie group, arXiv:0811.4234v1, https://arxiv.org/abs/0811.4234v1

import Mathlib

/-!
Statements from Beltita and Neeb, "A non-smooth continuous unitary representation of a
Banach-Lie group", arXiv:0811.4234v1, PDF pp. 1-4.
The local substrate uses real Lebesgue measure restricted to [0,1], so that Lp equality
is equality almost everywhere on that interval. All differentiability is over the reals.
-/

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Next46.P30

/-- Lebesgue measure on the closed unit interval (PDF pp. 2-3).
Values of representatives outside the interval are ignored by this measure. -/
def intervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The additive real Hilbert space G = L²([0,1],ℝ), PDF pp. 2-3. -/
abbrev GroupSpace := Lp ℝ 2 intervalMeasure

/-- The complex Hilbert space H = L²([0,1],ℂ), PDF pp. 2-3. -/
abbrev HilbertSpace := Lp ℂ 2 intervalMeasure

/-- A representative of the concrete phase product exp(i f) ξ, PDF pp. 2-3.
The Lp coercions choose measurable representatives; the output is used only modulo a.e. equality. -/
def phaseProduct (f : GroupSpace) (xi : HilbertSpace) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (f t : ℂ)) * xi t

/-- The paper's particular phase-multiplication action, not an arbitrary representation
with assumed properties (PDF pp. 2-3). Unit modulus proves the product belongs to L². -/
def phaseAction (f : GroupSpace) (xi : HilbertSpace) : HilbertSpace :=
  MemLp.toLp (phaseProduct f xi) (by
    apply (Lp.memLp xi).of_le
    · have hc : Continuous (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) := by
        fun_prop
      exact (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul
        (Lp.aestronglyMeasurable xi)
    · exact Filter.Eventually.of_forall (fun t => by
        simp [phaseProduct, norm_mul, Complex.norm_exp_I_mul_ofReal]))

/-- Sanity check: the class constructed by phaseAction has exactly the intended a.e. formula. -/
example (f : GroupSpace) (xi : HilbertSpace) :
    (phaseAction f xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct f xi := by
  exact MemLp.coeFn_toLp _

/-- Sanity check: the zero group element acts as the identity, for every Hilbert vector. -/
example (xi : HilbertSpace) : phaseAction 0 xi = xi := by
  apply Lp.ext
  have ha : (phaseAction 0 xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct 0 xi :=
    MemLp.coeFn_toLp _
  filter_upwards [ha, Lp.coeFn_zero ℝ 2 intervalMeasure] with t ht hzero
  change (0 : GroupSpace) t = 0 at hzero
  change (phaseAction 0 xi) t =
    Complex.exp (Complex.I * ((0 : GroupSpace) t : ℂ)) * xi t at ht
  rw [hzero] at ht
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using ht

/-- Sanity check: phase multiplication preserves the Hilbert norm, without normalizing xi. -/
example (f : GroupSpace) (xi : HilbertSpace) : ‖phaseAction f xi‖ = ‖xi‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  have ha : (phaseAction f xi : ℝ → ℂ) =ᵐ[intervalMeasure] phaseProduct f xi :=
    MemLp.coeFn_toLp _
  filter_upwards [ha] with t ht
  rw [ht]
  simp [phaseProduct, norm_mul, Complex.norm_exp_I_mul_ofReal]

/-- The actual smooth-vector set from Definition 1.1, PDF p. 2.
Every finite natural differentiability order is required over ℝ; no analytic order is used. -/
def smoothVectors : Set HilbertSpace :=
  {xi | ∀ n : ℕ, ContDiff ℝ n (fun f : GroupSpace => phaseAction f xi)}

/-- The singular function f_lambda(t) = |t-lambda|^(-1/4), PDF p. 3.
Its chosen value at t=lambda is zero, which changes no a.e. equivalence class. -/
def singularWeight (lam t : ℝ) : ℝ :=
  if t = lam then 0 else Real.rpow |t - lam| (-(1 / 4 : ℝ))

/-- Sanity check: the chosen diagonal value is zero. -/
example (lam : ℝ) : singularWeight lam lam = 0 := by
  simp [singularWeight]

/-- Sanity check: at distance one from the singularity the weight equals one. -/
example : singularWeight 0 1 = 1 := by
  norm_num [singularWeight]

end QAlgorithms.Papers.Independent.Next46.P30


