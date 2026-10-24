-- Prove2me | Definitions.Def_OAIQWQC003
-- name    : OAIQWQC003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T15:58:43.625384+00:00
-- url     : https://prove2.me/theorems/2f3608a2-5475-46e9-a3bb-5c11e1f7c185
-- title:
--   OpenAI quadric-surface split: root traces and homogeneous local metrics (definitions bundle 4 of 5)
-- statement:
--   The fourth definitions bundle of the split of OpenAI's proof of the counterexample to Griffiths' positivity conjecture on the quadric surface (`OAI.QuadricCounterexample.main_theorem`). It holds OpenAI's definitions from the modules listed below of `lean/OAI/Geometry/QuadricBundles` (OpenAI, *Ample rank-two bundles on the quadric surface without Griffiths-positive metrics*, OpenAI Math Release, September 24, 2026, result family 050, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them:
--   - complex and Hermitian quadratic forms on matrices, matrix entries as continuous linear maps, Wirtinger derivatives and mixed Hessians (`complexQuadratic`, `hermitianQuadratic`, `entryCLM`, `wirtingerDerivative`, `mixedHessian`);
--   - the root traces of Section 4 of the paper (`chosenRoot`, `rootOrbitAverage`, `rootTrace`, `secondRootTrace`, `doubleRootTrace`);
--   - the hyperbolic dynamics and homogeneous local plurisubharmonic metrics of Section 5 (`expandingRoot`, `contractingRoot`, `hyperbolicBasis`, `HomogeneousLocalPshMetric24`).
--
--   It also contains the 33 lemmas those definitions use in their bodies. It imports the definitions bundle `OAIQWQC001` and no statement.
--
--   Modules: `Compactness.lean`, `Curvature.lean`, `DualForms.lean`, `HomogeneousClassification.lean`, `MatrixDynamics.lean`, `MatrixRepresentative.lean`, `RootTrace.lean`, `TraceMetrics.lean`, `WeakLimits.lean`.
-- source:
--   OpenAI, Ample rank-two bundles on the quadric surface without Griffiths-positive metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 050; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf, Sections 4–5; Apache License 2.0); definitions carved from lean/OAI/Geometry/QuadricBundles at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWQC001

section
-- module Solutions.OAIQW_QuadricCounterexample.Curvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
noncomputable section

lemma fderiv_apply_const {X : Type u1} {Y : Type u2} {Z : Type u3} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : X → Y →L[ℝ] Z} {x : X} (hF : DifferentiableAt ℝ F x) (v : Y) :
    fderiv ℝ (fun y ↦ F y v) x =
      (ContinuousLinearMap.apply ℝ Z v).comp (fderiv ℝ F x) := by
  exact ((ContinuousLinearMap.apply ℝ Z v).hasFDerivAt.comp x hF.hasFDerivAt).fderiv

lemma hessian_mul {X : Type u4} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℂ} {x : X} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f y*g y)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w*g x + fderiv ℝ f x w*fderiv ℝ g x v +
      fderiv ℝ f x v*fderiv ℝ g x w + f x*fderiv ℝ (fderiv ℝ g) x v w := by
  have hf1 := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hg1 := hg.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hg2 := (hg.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hf' := hf2.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hg' := hg2.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hfg2 := ((hf.mul hg).fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : (fun y ↦ fderiv ℝ (fun z ↦ f z*g z) y w) =ᶠ[𝓝 x]
      fun y ↦ f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hy hy'
    change (fderiv ℝ (f*g) y) w = _
    rw [fderiv_mul (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))]
    simp
  have hh := (hf1.hasFDerivAt.mul hg').add (hg1.hasFDerivAt.mul hf')
  have hx := congrArg (fun T : X →L[ℝ] ℂ ↦ T v) (he.fderiv_eq.trans hh.fderiv)
  rw [fderiv_apply_const hfg2] at hx
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    add_apply,smul_apply,
    ContinuousLinearMap.comp_zero,zero_add,smul_eq_mul,
    ContinuousLinearMap.flip_apply] at hx
  convert hx using 1; ring

lemma hessian_re {X : Type u5} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} {x : X} (hf : ContDiffAt ℝ 2 f x) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ (f y).re)) x v w =
      (fderiv ℝ (fderiv ℝ f) x v w).re := by
  have hf1 := hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : (fun y ↦ fderiv ℝ (fun z ↦ (f z).re) y w) =ᶠ[𝓝 x]
      fun y ↦ (fderiv ℝ f y w).re := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact congrArg (fun T : X →L[ℝ] ℝ ↦ T w)
      (Complex.reCLM.hasFDerivAt.comp y
        (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hh := Complex.reCLM.hasFDerivAt.comp x
    (hf2.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hx := congrArg (fun T : X →L[ℝ] ℝ ↦ T v) (he.fderiv_eq.trans hh.fderiv)
  have hq2 : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ (f y).re)) x := ((Complex.reCLM.contDiff.contDiffAt.comp x hf).fderiv_right
    (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [fderiv_apply_const hq2] at hx
  simpa using hx

lemma hessian_clm {X : Type u6} {Y : Type u7} {Z : Type u8}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : X → Y} {x : X} (hf : ContDiffAt ℝ 2 f x) (L : Y →L[ℝ] Z) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ L (f y))) x v w =
      L (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hf2 := (hf.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : (fun y ↦ fderiv ℝ (fun z ↦ L (f z)) y w) =ᶠ[𝓝 x]
      fun y ↦ L (fderiv ℝ f y w) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact congrArg (fun T : X →L[ℝ] Z ↦ T w)
      (L.hasFDerivAt.comp y (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hh := L.hasFDerivAt.comp x
    (hf2.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hx := congrArg (fun T : X →L[ℝ] Z ↦ T v) (he.fderiv_eq.trans hh.fderiv)
  have hq2 : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ L (f y))) x :=
    ((L.contDiff.contDiffAt.comp x hf).fderiv_right
      (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [fderiv_apply_const hq2] at hx
  simpa using hx

lemma hessian_sum {X : Type u9} {Y : Type u10} {ι : Type u11}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ι → X → Y} {x : X} {s : Finset ι}
    (hf : ∀ i∈s, ContDiffAt ℝ 2 (f i) x) (v w : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ∑ i∈s, f i y)) x v w =
      ∑ i∈s, fderiv ℝ (fderiv ℝ (f i)) x v w := by
  have hf1 i hi := (hf i hi).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hf2 i hi := ((hf i hi).fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have he : fderiv ℝ (fun y ↦ ∑ i∈s, f i y) =ᶠ[𝓝 x]
      fun y ↦ ∑ i∈s, fderiv ℝ (f i) y := by
    have hen : ∀ᶠ y in 𝓝 x, ∀ i∈s, ContDiffAt ℝ 2 (f i) y := by
      simpa only [Filter.eventually_all_finset] using
        (show ∀ i∈s, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 (f i) y from
          fun i hi ↦ (hf i hi).eventually (by norm_num))
    filter_upwards [hen] with y hy
    exact fderiv_fun_sum fun i hi ↦ (hy i hi).differentiableAt (by norm_num)
  have hh := fderiv_fun_sum hf2
  rw [he.fderiv_eq, hh]
  simp

lemma hessian_linear_zero {X : Type u15} {Y : Type u16} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) (x v w : X) :
    fderiv ℝ (fderiv ℝ L) x v w = 0 := by
  have he : fderiv ℝ L = fun _ ↦ L := funext fun y ↦ L.fderiv
  simp [he]

lemma hessian_linear_mul_linear {X : Type u17} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} {x : X} (hf : ContDiffAt ℝ 2 f x)
    (L M : X →L[ℝ] ℂ) (v : X) :
    fderiv ℝ (fderiv ℝ (fun y ↦ L y * f y * M y)) x v v =
      L x * (fderiv ℝ (fderiv ℝ f) x v v) * M x +
      2 * L v * fderiv ℝ f x v * M x +
      2 * L x * fderiv ℝ f x v * M v + 2 * L v * f x * M v := by
  rw [hessian_mul (L.contDiff.contDiffAt.mul hf) M.contDiff.contDiffAt,
    hessian_mul L.contDiff.contDiffAt hf,hessian_linear_zero,hessian_linear_zero]
  have hd := fderiv_fun_mul L.differentiableAt
    (hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hd' : fderiv ℝ (fun y ↦ L y * f y) x =
      L x • fderiv ℝ f x + f x • L := by simpa only [L.fderiv] using hd
  rw [hd']
  simp only [L.fderiv,M.fderiv,add_apply,smul_apply,smul_eq_mul]
  ring

section Quadratic
variable {X : Type u18} {ι : Type u19} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

def entryCLM (i j : ι) : Matrix ι ι ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : Matrix ι ι ℂ →L[ℝ] (ι → ℂ))

def fiberEntryCLM (i : ι) : (X × (ι → ℂ)) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ X (ι → ℂ))

def starFiberEntryCLM (i : ι) : (X × (ι → ℂ)) →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (fiberEntryCLM i)

lemma base_entry_C2 {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (i j : ι) :
    ContDiffAt ℝ 2 (fun p : X × (ι → ℂ) ↦ H p.1 i j) (z,v) :=
  (entryCLM i j).contDiff.contDiffAt.comp (z,v) (hH.comp (z,v) contDiff_fst.contDiffAt)

lemma base_entry_fderiv {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) (i j : ι) (u : X) (w : ι → ℂ) :
    fderiv ℝ (fun p : X × (ι → ℂ) ↦ H p.1 i j) (z,v) (u,w) =
      fderiv ℝ H z u i j := by
  have hh := (entryCLM i j).hasFDerivAt.comp (z,v)
    ((hH.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt.comp (z,v)
      (ContinuousLinearMap.fst ℝ X (ι → ℂ)).hasFDerivAt)
  convert congrArg (fun T ↦ T (u,w)) hh.fderiv using 1 <;> rfl

def complexQuadratic (H : X → Matrix ι ι ℂ) (p : X × (ι → ℂ)) : ℂ :=
  star p.2 ⬝ᵥ ((H p.1).mulVec p.2)

def hermitianQuadratic (H : X → Matrix ι ι ℂ) (p : X × (ι → ℂ)) : ℝ :=
  (complexQuadratic H p).re

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma complexQuadratic_eq_sum (H : X → Matrix ι ι ℂ) :
    complexQuadratic H = fun p ↦ ∑ i, ∑ j, star (p.2 i)*H p.1 i j*p.2 j := by
  funext p
  simp only [complexQuadratic,dotProduct,Matrix.mulVec,Pi.star_apply,
    Finset.mul_sum,mul_assoc]

lemma complexQuadratic_C2 {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) :
    ContDiffAt ℝ 2 (complexQuadratic H) (z,v) := by
  rw [complexQuadratic_eq_sum]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((starFiberEntryCLM i).contDiff.contDiffAt.mul
    (base_entry_C2 hH v i j)).mul (fiberEntryCLM j).contDiff.contDiffAt

end Quadratic

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology
open scoped Matrix.Norms.Elementwise ComplexOrder
noncomputable section

def matrixAdjointCLM {ι : Type u20} [Fintype ι] :
    Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ where
  toFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' r M := by ext i j; simp [Matrix.conjTranspose_apply]
  cont := continuous_id.matrix_conjTranspose

lemma hermitian_fderiv {X : Type u21} {ι : Type u22} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype ι] {H : X → Matrix ι ι ℂ} {z : X}
    (hH : DifferentiableAt ℝ H z) (hh : ∀ᶠ y in 𝓝 z, (H y).IsHermitian) (u : X) :
    (fderiv ℝ H z u).IsHermitian := by
  have he : (fun y ↦ matrixAdjointCLM (H y)) =ᶠ[𝓝 z] H := hh
  have hd := matrixAdjointCLM.hasFDerivAt.comp z hH.hasFDerivAt
  have heq := hd.fderiv.symm.trans he.fderiv_eq
  exact congrArg (fun T ↦ T u) heq

end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix
open scoped ComplexOrder
noncomputable section

lemma matrix_completed_square {n : Type u25} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.PosDef) (A T : Matrix n n ℂ) (v w : n → ℂ) :
    star v ⬝ᵥ (T.mulVec v) + star w ⬝ᵥ (A.mulVec v) +
      star v ⬝ᵥ (A.conjTranspose.mulVec w) + star w ⬝ᵥ (H.mulVec w) =
    star v ⬝ᵥ ((T-A.conjTranspose*H⁻¹*A).mulVec v) +
      star (w+H⁻¹.mulVec (A.mulVec v)) ⬝ᵥ (H.mulVec (w+H⁻¹.mulVec (A.mulVec v))) := by
  have hi : H*H⁻¹=1 := H.mul_nonsing_inv (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have hi' : H⁻¹*H=1 := H.nonsing_inv_mul (H.isUnit_iff_isUnit_det.mp hH.isUnit)
  have hs : H⁻¹.conjTranspose = H⁻¹ := hH.inv.isHermitian
  have hb : H.mulVec (H⁻¹.mulVec (A.mulVec v)) = A.mulVec v := by
    rw [mulVec_mulVec,hi,one_mulVec]
  have hc (y : n → ℂ) : star (H⁻¹.mulVec (A.mulVec v)) ⬝ᵥ (H.mulVec y) =
      star v ⬝ᵥ (A.conjTranspose.mulVec y) := by
    simp only [star_mulVec,hs,dotProduct_mulVec,vecMul_vecMul,mul_assoc,hi',mul_one]
  simp only [mulVec_add,star_add,dotProduct_add,add_dotProduct,hb,hc,
    sub_mulVec,dotProduct_sub]
  have hh := hc (H⁻¹.mulVec (A.mulVec v))
  rw [hb] at hh
  rw [hh]
  simp only [mulVec_mulVec,mul_assoc]
  ring

lemma matrix_completed_square_nonneg {n : Type u26} [Fintype n] [DecidableEq n]
    {H A T : Matrix n n ℂ} (hH : H.PosDef)
    (hT : (T-A.conjTranspose*H⁻¹*A).PosSemidef) (v w : n → ℂ) :
    0 ≤ (star v ⬝ᵥ (T.mulVec v) + star w ⬝ᵥ (A.mulVec v) +
      star v ⬝ᵥ (A.conjTranspose.mulVec w) + star w ⬝ᵥ (H.mulVec w)).re := by
  rw [matrix_completed_square hH]
  exact (Complex.nonneg_iff.mp (add_nonneg
    (hT.dotProduct_mulVec_nonneg v)
    (hH.posSemidef.dotProduct_mulVec_nonneg _))).1

end
end QuadricCounterexample

namespace QuadricCounterexample
open Matrix
noncomputable section

lemma quadratic_levi_expansion {ι : Type u27} [Fintype ι]
    (H D E U V : Matrix ι ι ℂ) (hD : D.IsHermitian) (hE : E.IsHermitian)
    (v w : ι → ℂ) :
    (star v ⬝ᵥ U.mulVec v + 2 * (star w ⬝ᵥ D.mulVec v) +
      2 * (star v ⬝ᵥ D.mulVec w) + 2 * (star w ⬝ᵥ H.mulVec w)) +
    (star v ⬝ᵥ V.mulVec v + 2 * (star (Complex.I • w) ⬝ᵥ E.mulVec v) +
      2 * (star v ⬝ᵥ E.mulVec (Complex.I • w)) +
      2 * (star (Complex.I • w) ⬝ᵥ H.mulVec (Complex.I • w))) =
    4 * (star v ⬝ᵥ ((1/4 : ℂ) • (U+V)).mulVec v +
      star w ⬝ᵥ ((1/2 : ℂ) • (D-Complex.I • E)).mulVec v +
      star v ⬝ᵥ (((1/2 : ℂ) • (D-Complex.I • E)).conjTranspose).mulVec w +
      star w ⬝ᵥ H.mulVec w) := by
  have hs : ((1/2 : ℂ) • (D-Complex.I • E)).conjTranspose =
      (1/2 : ℂ) • (D+Complex.I • E) := by
    simp only [conjTranspose_smul,conjTranspose_sub, hD.eq,hE.eq]
    simp
  rw [hs]
  simp only [star_smul,Complex.star_def,Complex.conj_I,
    mulVec_smul,smul_mulVec,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    add_mulVec,sub_mulVec,dotProduct_add,dotProduct_sub]
  ring_nf
  simp only [Complex.I_sq, mul_neg, mul_one]
  ring

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ComplexOrder
noncomputable section
variable {X : Type u28} {ι : Type u29} [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι]

def wirtingerDerivative (H : X → Matrix ι ι ℂ) (z u : X) : Matrix ι ι ℂ :=
  (1/2 : ℂ) • (fderiv ℝ H z u - Complex.I • fderiv ℝ H z (Complex.I • u))

def mixedHessian (H : X → Matrix ι ι ℂ) (z u : X) : Matrix ι ι ℂ :=
  (1/4 : ℂ) • (fderiv ℝ (fderiv ℝ H) z u u +
    fderiv ℝ (fderiv ℝ H) z (Complex.I • u) (Complex.I • u))

lemma hermitianQuadratic_C2 {H : X → Matrix ι ι ℂ} {z : X}
    (hH : ContDiffAt ℝ 2 H z) (v : ι → ℂ) :
    ContDiffAt ℝ 2 (hermitianQuadratic H) (z,v) :=
  Complex.reCLM.contDiff.contDiffAt.comp (z,v) (complexQuadratic_C2 hH v)

lemma curvature_nonneg_of_strict [DecidableEq ι]
    {H : X → Matrix ι ι ℂ} {z : X}
    (hcurv : ∀ u : X, u ≠ 0 → (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosDef)
    (u : X) : (mixedHessian H z u -
      (wirtingerDerivative H z u).conjTranspose*(H z)⁻¹*wirtingerDerivative H z u).PosSemidef := by
  by_cases hu : u=0
  · subst u
    simpa [mixedHessian,wirtingerDerivative] using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  · exact (hcurv u hu).posSemidef

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.RootTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

namespace QuadricCounterexample
open Complex Topology BigOperators

noncomputable section
variable (m : ℕ) [NeZero m]
local instance instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

noncomputable def chosenRoot (x : ℂ) : ℂ :=
  Classical.choose ((Complex.isOpenQuotientMap_pow m).surjective x)

lemma chosenRoot_pow (x : ℂ) : chosenRoot m x ^ m = x :=
  Classical.choose_spec ((Complex.isOpenQuotientMap_pow m).surjective x)

lemma same_power_orbit {x y : ℂ} (h : x^m=y^m) :
    ∃ ζ : rootsOfUnity m ℂ, x = (ζ.val : ℂ)*y := by
  by_cases hy : y=0
  · have hx : x=0 := (pow_eq_zero_iff (NeZero.ne m)).mp (by simpa [hy, zero_pow (NeZero.ne m)] using h)
    exact ⟨1, by simp [hx,hy]⟩
  · have hp : (x/y)^m=1 := by rw [div_pow,h,div_self (pow_ne_zero m hy)]
    exact ⟨rootsOfUnity.mkOfPowEq (x/y) hp, by simp [div_mul_cancel₀ _ hy]⟩

def rootOrbitAverage {V : Type u1} (F : ℂ × V → ℝ) (p : ℂ × V) : ℝ :=
  (m : ℝ)⁻¹ * ∑ ζ : rootsOfUnity m ℂ, F ((ζ.val : ℂ)*p.1,p.2)

def rootTrace {V : Type u2} (F : ℂ × V → ℝ) (p : ℂ × V) : ℝ :=
  rootOrbitAverage m F (chosenRoot m p.1,p.2)

lemma rootOrbitAverage_orbit {V : Type u3} (F : ℂ × V → ℝ) (x : ℂ) (v : V)
    (η : rootsOfUnity m ℂ) :
    rootOrbitAverage m F ((η.val : ℂ)*x,v) = rootOrbitAverage m F (x,v) := by
  unfold rootOrbitAverage
  congr 1
  have he := Equiv.sum_comp (Equiv.mulRight η)
    (fun ζ : rootsOfUnity m ℂ ↦ F ((ζ.val : ℂ)*x,v))
  change (∑ ζ : rootsOfUnity m ℂ, F ((((ζ * η).val : ℂ))*x,v)) = _ at he
  simpa only [Subgroup.coe_mul, Units.val_mul, mul_assoc] using he

lemma rootTrace_pow {V : Type u4} (F : ℂ × V → ℝ) (x : ℂ) (v : V) :
    rootTrace m F (x^m,v) = rootOrbitAverage m F (x,v) := by
  obtain ⟨ζ,hζ⟩ := same_power_orbit m (chosenRoot_pow m (x^m))
  change rootOrbitAverage m F (chosenRoot m (x^m),v) = _
  rw [hζ,rootOrbitAverage_orbit]

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section

variable (m : ℕ) [NeZero m]
local instance instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_1 : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

lemma rootTrace_eq_of_pow {W : Type u11} (F : ℂ × W → ℝ) {z x : ℂ} (hz : z^m=x)
    (v : W) : rootTrace m F (x,v) = rootOrbitAverage m F (z,v) := by
  rw [← hz, rootTrace_pow]

theorem continuousOn_rootTrace {W : Type u12} [TopologicalSpace W]
    {U : Set (ℂ × W)} {F : ℂ × W → ℝ} (hU : IsOpen U)
    (hF : ContinuousOn F ((fun p : ℂ × W ↦ (p.1^m,p.2)) ⁻¹' U)) :
    ContinuousOn (rootTrace m F) U := by
  let π : ℂ × W → ℂ × W := fun p ↦ (p.1^m,p.2)
  have hav : ContinuousOn (rootOrbitAverage m F) (π ⁻¹' U) := by
    apply ContinuousOn.const_mul
    apply continuousOn_finsetSum
    intro ζ _
    apply hF.comp (by fun_prop : ContinuousOn
      (fun p : ℂ × W ↦ ((ζ.val : ℂ)*p.1,p.2)) (π ⁻¹' U))
    intro p hp
    change (((ζ.val : ℂ)*p.1)^m,p.2) ∈ U
    rw [mul_pow, (mem_rootsOfUnity' m ζ.val).mp ζ.property, one_mul]
    exact hp
  have hπ := ((Complex.isOpenQuotientMap_pow m).prodMap
    (IsOpenQuotientMap.id (X := W)))
  apply (hπ.isQuotientMap.continuousOn_isOpen_iff hU).mpr
  apply hav.congr
  intro p _
  exact rootTrace_pow m F p.1 p.2

def centeredRoot (x : ℂ) (z : ℂ) : ℂ :=
  chosenRoot m x * (z/x) ^ ((m : ℂ)⁻¹)

lemma centeredRoot_pow {x : ℂ} (hx : x ≠ 0) (z : ℂ) : centeredRoot m x z ^ m = z := by
  rw [centeredRoot, mul_pow, chosenRoot_pow,
    Complex.cpow_nat_inv_pow _ (NeZero.ne m)]
  exact mul_div_cancel₀ z hx

lemma centeredRoot_differentiableOn {x : ℂ} :
    DifferentiableOn ℂ (centeredRoot m x) {z | z/x ∈ Complex.slitPlane} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact ((analyticAt_const.mul ((analyticAt_id.div_const (c := x)).cpow analyticAt_const hz)).differentiableAt)

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Complex BigOperators
noncomputable section
variable {W : Type u14} [NormedAddCommGroup W] [NormedSpace ℂ W]

def swapBase (p : ℂ × (ℂ × W)) : ℂ × (ℂ × W) := (p.2.1,(p.1,p.2.2))

omit [NormedAddCommGroup W] [NormedSpace ℂ W] in
@[simp] lemma swapBase_swapBase (p : ℂ × (ℂ × W)) : swapBase (swapBase p) = p := rfl

lemma differentiable_swapBase : Differentiable ℂ (swapBase (W := W)) := by
  exact (differentiable_snd.fst).prodMk
    (differentiable_fst.prodMk (differentiable_snd.snd))

variable (m : ℕ) [NeZero m]
local instance instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_2 : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

def secondRootTrace (F : ℂ × (ℂ × W) → ℝ) (p : ℂ × (ℂ × W)) : ℝ :=
  rootTrace m (F ∘ swapBase) (swapBase p)

lemma continuousOn_secondRootTrace {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1,(p.2.1^m,p.2.2))) ⁻¹' U)) :
    ContinuousOn (secondRootTrace m F) U := by
  have hT := differentiable_swapBase (W := W)
  have hc : ContinuousOn (F ∘ swapBase)
      ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,p.2)) ⁻¹' (swapBase ⁻¹' U)) :=
    hF.comp hT.continuous.continuousOn (fun _ h ↦ h)
  exact (continuousOn_rootTrace m (hU.preimage hT.continuous) hc).comp
    hT.continuous.continuousOn (fun _ h ↦ h)

variable [LocallyCompactSpace W]

def doubleRootTrace (F : ℂ × (ℂ × W) → ℝ) : ℂ × (ℂ × W) → ℝ :=
  rootTrace m (secondRootTrace m F)

omit [LocallyCompactSpace W] [NormedAddCommGroup W] [NormedSpace ℂ W] in
lemma doubleRootTrace_formula (F : ℂ × (ℂ × W) → ℝ) (p : ℂ × (ℂ × W)) :
    doubleRootTrace m F p = (m : ℝ)⁻¹ ^ 2 *
      ∑ ζ : rootsOfUnity m ℂ, ∑ η : rootsOfUnity m ℂ,
        F ((ζ.val : ℂ) * chosenRoot m p.1,
          ((η.val : ℂ) * chosenRoot m p.2.1,p.2.2)) := by
  simp only [doubleRootTrace, secondRootTrace, rootTrace, rootOrbitAverage,
    Function.comp_apply, swapBase]
  rw [← Finset.mul_sum, ← mul_assoc, pow_two]

omit [LocallyCompactSpace W] in
lemma continuousOn_doubleRootTrace {U : Set (ℂ × (ℂ × W))} (hU : IsOpen U)
    {F : ℂ × (ℂ × W) → ℝ}
    (hF : ContinuousOn F ((fun p : ℂ × (ℂ × W) ↦ (p.1^m,(p.2.1^m,p.2.2))) ⁻¹' U)) :
    ContinuousOn (doubleRootTrace m F) U := by
  apply continuousOn_rootTrace m hU
  apply continuousOn_secondRootTrace m (hU.preimage (by fun_prop))
  exact hF

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38

noncomputable section

namespace QuadricCounterexample
open Set Metric MeasureTheory Topology Filter Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
open Matrix
open scoped ComplexOrder

local instance matrixContinuousENorm {n : Type u12} [Fintype n] :
    ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
local instance instContinuousENormMatrixComplexOfFintype_solutions {n : Type u34} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31

noncomputable section

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory
open scoped ENNReal

noncomputable def setAverageL2Functional {α : Type u10} {E : Type u11} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (ℓ : E →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : Lp E 2 μ →L[ℝ] ℝ :=
  (μ s).toReal⁻¹ • Complex.reCLM.comp
    ((innerSL ℂ (indicatorConstLp 2 hs hμs
      ((InnerProductSpace.toDual ℂ E).symm (StrongDual.extendRCLike ℓ)))).restrictScalars ℝ)

end QuadricCounterexample

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

local instance instContinuousENormMatrixComplexOfFintype_solutions_1 {n : Type u28} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

local instance instIsAddHaarMeasureProdComplexVolume_solutions_3_r74168d_1 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
local instance instContinuousENormMatrixComplexOfFintype_solutions_3 {n : Type u24} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TraceMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

section Trace
variable (m : ℕ) [NeZero m]
local instance instFintypeSubtypeUnitsComplexMemSubgroupRootsOfUnity_solutions_3 : Fintype (rootsOfUnity m ℂ) := Fintype.ofFinite _

omit [NeZero m] in
lemma root_pow (ζ : rootsOfUnity m ℂ) (x : ℂ) : ((ζ.val : ℂ)*x)^m=x^m := by
  rw [mul_pow,(mem_rootsOfUnity' m ζ.val).mp ζ.property,one_mul]

lemma root_norm (ζ : rootsOfUnity m ℂ) (x : ℂ) : ‖(ζ.val : ℂ)*x‖=‖x‖ := by
  rw [norm_mul,Complex.norm_eq_one_of_mem_rootsOfUnity ζ.property,one_mul]

def rootSwitchEquiv (i j : Fin 2) : Equiv.Perm (rootsOfUnity m ℂ) :=
  if i=j then Equiv.refl _ else Equiv.inv _

end Trace
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section

namespace QuadricCounterexample
open Matrix

noncomputable def expandingRoot (t : ℝ) : ℝ := (t + Real.sqrt (t^2 - 4)) / 2
noncomputable def contractingRoot (t : ℝ) : ℝ := (t - Real.sqrt (t^2 - 4)) / 2

lemma hyperbolic_roots {t : ℝ} (ht : 2 < t) :
    1 < expandingRoot t ∧ 0 < contractingRoot t ∧
    contractingRoot t < 1 ∧
    expandingRoot t + contractingRoot t = t ∧
    expandingRoot t * contractingRoot t = 1 := by
  have hs0 : 0 < t ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hs0.le
  have hp := Real.sqrt_pos.mpr hs0
  dsimp [expandingRoot, contractingRoot]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · ring
  · nlinarith

noncomputable def hyperbolicBasis (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(expandingRoot t : ℂ) - M 1 1, (contractingRoot t : ℂ) - M 1 1;
    M 1 0, M 1 0]

lemma hyperbolicBasis_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ}
    (ht : 2 < t) (hc : M 1 0 ≠ 0) : (hyperbolicBasis M t).det ≠ 0 := by
  have hd : expandingRoot t - contractingRoot t ≠ 0 := by
    obtain ⟨hl, _, hm, _, _⟩ := hyperbolic_roots ht
    linarith
  have hdC : (expandingRoot t : ℂ) - (contractingRoot t : ℂ) ≠ 0 := by exact_mod_cast hd
  have hdet : (hyperbolicBasis M t).det =
      M 1 0 * ((expandingRoot t : ℂ) - (contractingRoot t : ℂ)) := by
    simp [hyperbolicBasis, Matrix.det_fin_two]
    ring
  rw [hdet]
  exact mul_ne_zero hc hdC

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.HomogeneousClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Matrix

structure HomogeneousLocalPshMetric24 (ψ : (Fin 2 → ℂ) → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ ψ v
  homogeneity : ∀ (c : ℂ) v, ψ (c • v) = ‖c‖ ^ 48 * ψ v
  upperSemicontinuous : UpperSemicontinuousOn ψ ({0}ᶜ : Set (Fin 2 → ℂ))
  disk : ∀ (U : Set ℂ), IsOpen U → ∀ (f : ℂ → Fin 2 → ℂ) (t : ℂ → ℂ),
    AnalyticOnNhd ℂ f U → AnalyticOnNhd ℂ t U → (∀ z ∈ U, f z ≠ 0) →
    LocalDiskSubmeanOn U (fun z ↦ ‖t z‖ ^ 2 * ψ (f z))

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.DualForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
open scoped ComplexOrder

def otherIndex (i : Fin 2) : Fin 2 := if i=0 then 1 else 0

end
end QuadricCounterexample

end

end OAI
end


