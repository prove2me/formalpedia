-- Prove2me | Definitions.Def_K24GlobalGeometry
-- name    : K24GlobalGeometry
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T08:53:27.937331+00:00
-- url     : https://prove2.me/theorems/307243a3-0dec-4e35-a891-6249f62e8aee
-- title:
--   K24: genuine geometric operators and common circle action
-- statement:
--   Actual four-dimensional tangent, covector and symmetric tensor sections, positive metrics, chart reconstruction, Christoffel/Bianchi/symmetrized gradient/Ricci/Lie operators, the true tensor and two-term vector defects, a genuine smooth circle action and normalized pointwise Haar projections. The literal partial-gauged Einstein map and its variation are defined. Raw operations are totalized; geometric regularity and analytic properties are guarded or required in the full target. No desired PDE estimate or inverse is assumed, and no unproved lemma is imported.
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — full §§1–7; inherited conventions in K16/K21/K23. Explicit norm choices and still-open organizer recorded in natural-language statement.

import Mathlib

/- Original source module: K24Work.Global.Sections -/

/-!
# Global geometric sections for the full K24 target

These are sections of the actual tangent and cotangent bundles of a real
four-manifold. Every declaration is fully checked without admitted proofs.
Further compatibility obligations are recorded in `GeometryTargets.lean`.
No Einstein condition or infinite differentiability is built into `Metric`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
abbrev I4 := 𝓘(ℝ, FourSpace)
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

variable (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]

abbrev RawVector := ∀ p : M, TangentSpace I4 p
abbrev RawCovector := ∀ p : M, TangentSpace I4 p →L[ℝ] ℝ
abbrev RawCov2 := ∀ p : M,
  TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ)
abbrev RawCov3 := ∀ p : M,
  TangentSpace I4 p →L[ℝ]
    (TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ))

variable {M}

def IsSymmetricCov2 (u : RawCov2 M) : Prop :=
  ∀ p (v w : TangentSpace I4 p), u p v w = u p w v

def IsPositiveDefiniteCov2 (g : RawCov2 M) : Prop :=
  ∀ p (v : TangentSpace I4 p), v ≠ 0 → 0 < g p v v

def IsMetric (g : RawCov2 M) : Prop :=
  IsSymmetricCov2 g ∧ IsPositiveDefiniteCov2 g

abbrev SymmetricCov2 (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  {u : RawCov2 M // IsSymmetricCov2 u}

/-- Positivity and symmetry only; regularity belongs to the chosen section space. -/
abbrev Metric (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  {g : RawCov2 M // IsMetric g}

def basisVector (i : Fin 4) : FourSpace := EuclideanSpace.single i 1

def coordProj (i : Fin 4) : FourSpace →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 4 => ℝ) i

/-- The covariant bilinear form with the specified coordinate matrix. -/
def matrixToBilinear (a : Mat4) : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ) :=
  ∑ i : Fin 4, ∑ j : Fin 4, (coordProj i).smulRight (a i j • coordProj j)

def coefficientsToCovector (a : Fin 4 → ℝ) : FourSpace →L[ℝ] ℝ :=
  ∑ i : Fin 4, a i • coordProj i

def coefficientsToCov3 (a : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    FourSpace →L[ℝ] (FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)) :=
  ∑ i : Fin 4, (coordProj i).smulRight
    (∑ j : Fin 4, (coordProj j).smulRight
      (∑ k : Fin 4, a i j k • coordProj k))

theorem sum_basisVector (v : FourSpace) :
    ∑ i : Fin 4, v i • basisVector i = v := by
  ext j
  simp [basisVector, Pi.single_apply]

theorem coefficientsToCovector_recover (a : FourSpace →L[ℝ] ℝ) :
    coefficientsToCovector (fun i => a (basisVector i)) = a := by
  ext v
  calc
    coefficientsToCovector (fun i => a (basisVector i)) v =
        a (∑ i : Fin 4, v i • basisVector i) := by
      simp [coefficientsToCovector, coordProj, map_sum, mul_comm]
    _ = a v := by rw [sum_basisVector]

theorem matrixToBilinear_recover (a : FourSpace →L[ℝ] (FourSpace →L[ℝ] ℝ)) :
    matrixToBilinear (fun i j => a (basisVector i) (basisVector j)) = a := by
  ext v w
  calc
    matrixToBilinear (fun i j => a (basisVector i) (basisVector j)) v w =
        a (∑ i : Fin 4, v i • basisVector i) (∑ j : Fin 4, w j • basisVector j) := by
      simp [matrixToBilinear, coordProj, map_sum, Finset.mul_sum, mul_comm,
        mul_left_comm]
      rw [Finset.sum_comm]
    _ = a v w := by rw [sum_basisVector, sum_basisVector]

/-- Pull back both covariant arguments by the actual differential. -/
def bilinearPullback {V W : Type*}
    [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    (a : V →L[ℝ] (V →L[ℝ] ℝ)) (d : W →L[ℝ] V) :
    W →L[ℝ] (W →L[ℝ] ℝ) :=
  (ContinuousLinearMap.precomp ℝ d).comp (a.comp d)

@[simp] theorem bilinearPullback_apply {V W : Type*}
    [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    (a : V →L[ℝ] (V →L[ℝ] ℝ)) (d : W →L[ℝ] V) (v w : W) :
    bilinearPullback a d v w = a (d v) (d w) := rfl

variable {N : Type*} [TopologicalSpace N] [ChartedSpace FourSpace N]

def pullbackCovector (f : N → M) (u : RawCovector M) : RawCovector N :=
  fun p => (u (f p)).comp (mfderiv I4 I4 f p)

def pullbackCov2 (f : N → M) (u : RawCov2 M) : RawCov2 N :=
  fun p => bilinearPullback (u (f p)) (mfderiv I4 I4 f p)

def cov2InChart (u : RawCov2 M) (c : M) (x : FourSpace) : Mat4 :=
  let e := chartAt FourSpace c
  let d := mfderiv I4 I4 e.symm x
  fun i j => u (e.symm x) (d (basisVector i)) (d (basisVector j))

def covectorInChart (u : RawCovector M) (c : M) (x : FourSpace) : Fin 4 → ℝ :=
  let e := chartAt FourSpace c
  let d := mfderiv I4 I4 e.symm x
  fun i => u (e.symm x) (d (basisVector i))

def vectorInChart (Y : RawVector M) (c : M) (x : FourSpace) : FourSpace :=
  let e := chartAt FourSpace c
  mfderiv I4 I4 e (e.symm x) (Y (e.symm x))

/-- Coordinate regularity on every canonical chart. This is a property of the
actual section, rather than data replacing the section by an operator. -/
def Cov2ContDiff (k : ℕ∞ω) (u : RawCov2 M) : Prop :=
  ∀ c : M, ContDiffOn ℝ k (cov2InChart u c) (chartAt FourSpace c).target

def CovectorContDiff (k : ℕ∞ω) (u : RawCovector M) : Prop :=
  ∀ c : M, ContDiffOn ℝ k (covectorInChart u c) (chartAt FourSpace c).target

def VectorContDiff (k : ℕ∞ω) (Y : RawVector M) : Prop :=
  ∀ c : M, ContDiffOn ℝ k (vectorInChart Y c) (chartAt FourSpace c).target

/-- Rebuild a covector using the specified chart at an arbitrary base point.
This is used only on that chart's source in compatibility statements. -/
def covectorFromChartAt (c p : M) (a : Fin 4 → ℝ) : TangentSpace I4 p →L[ℝ] ℝ :=
  (coefficientsToCovector a).comp (mfderiv I4 I4 (chartAt FourSpace c) p)

/-- Rebuild a bilinear tensor using the differential of the specified chart. -/
def cov2FromChartAt (c p : M) (a : Mat4) :
    TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ) :=
  bilinearPullback (matrixToBilinear a) (mfderiv I4 I4 (chartAt FourSpace c) p)

def cov3FromChartAt (c p : M) (a : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    TangentSpace I4 p →L[ℝ]
      (TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ)) :=
  let d := mfderiv I4 I4 (chartAt FourSpace c) p
  ∑ i : Fin 4, ((coordProj i).comp d).smulRight
    (∑ j : Fin 4, ((coordProj j).comp d).smulRight
      (∑ k : Fin 4, a i j k • (coordProj k).comp d))

/-- Choose `chartAt p` only to evaluate a geometric coordinate formula at `p`.
Independence from this choice is a separate theorem obligation. -/
def cov2FromCoordinates (a : M → FourSpace → Mat4) : RawCov2 M :=
  fun p => cov2FromChartAt p p (a p (chartAt FourSpace p p))

def covectorFromCoordinates (a : M → FourSpace → Fin 4 → ℝ) : RawCovector M :=
  fun p => covectorFromChartAt p p (a p (chartAt FourSpace p p))

def cov3FromCoordinates
    (a : M → FourSpace → Fin 4 → Fin 4 → Fin 4 → ℝ) : RawCov3 M :=
  fun p => cov3FromChartAt p p (a p (chartAt FourSpace p p))

section ChartRecovery

variable [IsManifold I4 ∞ M]

theorem cov2_chart_recovery
    (u : RawCov2 M) (c p : M) (hp : p ∈ (chartAt FourSpace c).source) :
    cov2FromChartAt c p (cov2InChart u c (chartAt FourSpace c p)) = u p := by
  let e := chartAt FourSpace c
  let d : TangentSpace I4 p →L[ℝ] FourSpace := mfderiv I4 I4 e p
  let di : FourSpace →L[ℝ] TangentSpace I4 p := mfderiv I4 I4 e.symm (e p)
  have hdi : ∀ v : TangentSpace I4 p, di (d v) = v := by
    intro v
    have h := (mdifferentiable_chart (I := I4) c).symm_comp_deriv hp
    exact congrArg (fun A => A v) h
  change bilinearPullback (matrixToBilinear
    (fun i j => u (e.symm (e p)) (di (basisVector i)) (di (basisVector j)))) d = u p
  have hrec := matrixToBilinear_recover (bilinearPullback (u (e.symm (e p))) di)
  erw [hrec]
  ext v w
  change u (e.symm (e p)) (di (d v)) (di (d w)) = u p v w
  rw [hdi, hdi, e.left_inv hp]

theorem covector_chart_recovery
    (u : RawCovector M) (c p : M) (hp : p ∈ (chartAt FourSpace c).source) :
    covectorFromChartAt c p (covectorInChart u c (chartAt FourSpace c p)) = u p := by
  let e := chartAt FourSpace c
  let d : TangentSpace I4 p →L[ℝ] FourSpace := mfderiv I4 I4 e p
  let di : FourSpace →L[ℝ] TangentSpace I4 p := mfderiv I4 I4 e.symm (e p)
  have hdi : ∀ v : TangentSpace I4 p, di (d v) = v := by
    intro v
    have h := (mdifferentiable_chart (I := I4) c).symm_comp_deriv hp
    exact congrArg (fun A => A v) h
  change (coefficientsToCovector
    (fun i => u (e.symm (e p)) (di (basisVector i)))).comp d = u p
  have hrec := coefficientsToCovector_recover ((u (e.symm (e p))).comp di)
  erw [hrec]
  ext v
  change u (e.symm (e p)) (di (d v)) = u p v
  rw [hdi, e.left_inv hp]

end ChartRecovery

end K24.Global


/- Original source module: K24Work.Global.Operators -/

/-!
# Actual global differential expressions for K24

All coefficients come from actual global tensor sections. Derivatives are
Mathlib `fderiv`/`deriv` and metric inverses are matrix inverses. The canonical
chart merely selects a representative coordinate formula at each point.
Coordinate independence is an explicit, still unproved obligation recorded in
`GeometryTargets.lean`, and is not assumed as arbitrary operator data.
This definition file has no axioms or admitted proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def coordDeriv (f : FourSpace → ℝ) (i : Fin 4) (x : FourSpace) : ℝ :=
  fderiv ℝ f x (basisVector i)

def inverseMetricInChart (g : RawCov2 M) (c : M) (x : FourSpace) : Mat4 :=
  (cov2InChart g c x)⁻¹

def christoffelInChart (g : RawCov2 M) (c : M) (x : FourSpace)
    (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, inverseMetricInChart g c x k l *
    (coordDeriv (fun y => cov2InChart g c y j l) i x +
     coordDeriv (fun y => cov2InChart g c y i l) j x -
     coordDeriv (fun y => cov2InChart g c y i j) l x)

/-- Covariant derivative, with the differentiation index first. -/
def nablaTensorInChart (g u : RawCov2 M) (c : M) (x : FourSpace)
    (a b d : Fin 4) : ℝ :=
  coordDeriv (fun y => cov2InChart u c y b d) a x -
    (∑ p : Fin 4, christoffelInChart g c x p a b * cov2InChart u c x p d) -
    (∑ p : Fin 4, christoffelInChart g c x p a d * cov2InChart u c x b p)

def nablaCovectorInChart (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (a b : Fin 4) : ℝ :=
  coordDeriv (fun y => covectorInChart eta c y b) a x -
    ∑ p : Fin 4, christoffelInChart g c x p a b * covectorInChart eta c x p

def nablaContravariantInChart (g : RawCov2 M) (v : M → FourSpace → Mat4)
    (c : M) (x : FourSpace) (a b d : Fin 4) : ℝ :=
  coordDeriv (fun y => v c y b d) a x +
    (∑ p : Fin 4, christoffelInChart g c x b a p * v c x p d) +
    (∑ p : Fin 4, christoffelInChart g c x d a p * v c x b p)

def metricTraceInChart (g u : RawCov2 M) (c : M) (x : FourSpace) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, inverseMetricInChart g c x a b * cov2InChart u c x a b

def bianchiInChart (g u : RawCov2 M) (c : M) (x : FourSpace) (j : Fin 4) : ℝ :=
  -(∑ a : Fin 4, ∑ b : Fin 4,
    inverseMetricInChart g c x a b * nablaTensorInChart g u c x a b j) +
    (1 / 2 : ℝ) * coordDeriv (metricTraceInChart g u c) j x

def deltaStarInChart (g : RawCov2 M) (eta : RawCovector M)
    (c : M) (x : FourSpace) (i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (nablaCovectorInChart g eta c x i j +
    nablaCovectorInChart g eta c x j i)

def lieTensorInChart (Y : RawVector M) (u : RawCov2 M)
    (c : M) (x : FourSpace) (i j : Fin 4) : ℝ :=
  ∑ p : Fin 4,
    (vectorInChart Y c x p * coordDeriv (fun y => cov2InChart u c y i j) p x +
     coordDeriv (fun y => vectorInChart Y c y p) i x * cov2InChart u c x p j +
     coordDeriv (fun y => vectorInChart Y c y p) j x * cov2InChart u c x i p)

def curvatureInChart (g : RawCov2 M) (c : M) (x : FourSpace)
    (l i j k : Fin 4) : ℝ :=
  coordDeriv (fun y => christoffelInChart g c y l j k) i x -
  coordDeriv (fun y => christoffelInChart g c y l i k) j x +
    ∑ p : Fin 4,
      (christoffelInChart g c x l i p * christoffelInChart g c x p j k -
       christoffelInChart g c x l j p * christoffelInChart g c x p i k)

def ricciInChart (g : RawCov2 M) (c : M) (x : FourSpace) (i j : Fin 4) : ℝ :=
  ∑ k : Fin 4, curvatureInChart g c x k k i j

def einsteinResidualInChart (lam : ℝ) (g : RawCov2 M)
    (c : M) (x : FourSpace) (i j : Fin 4) : ℝ :=
  ricciInChart g c x i j - lam * cov2InChart g c x i j

def nablaTensor (g u : RawCov2 M) : RawCov3 M :=
  cov3FromCoordinates (nablaTensorInChart g u)

def nablaCovector (g : RawCov2 M) (eta : RawCovector M) : RawCov2 M :=
  cov2FromCoordinates (nablaCovectorInChart g eta)

def bianchi (g u : RawCov2 M) : RawCovector M :=
  covectorFromCoordinates (bianchiInChart g u)

def deltaStar (g : RawCov2 M) (eta : RawCovector M) : RawCov2 M :=
  cov2FromCoordinates (deltaStarInChart g eta)

def lieTensor (Y : RawVector M) (u : RawCov2 M) : RawCov2 M :=
  cov2FromCoordinates (lieTensorInChart Y u)

/-- K24 convention: `K_g Y = L_Y g`, with no extra factor. -/
def killing (g : RawCov2 M) (Y : RawVector M) : RawCov2 M :=
  lieTensor Y g

def ricci (g : RawCov2 M) : RawCov2 M :=
  cov2FromCoordinates (ricciInChart g)

def einsteinResidual (lam : ℝ) (g : RawCov2 M) : RawCov2 M :=
  ricci g - lam • g

/-- The unprojected geometric tensor defect. -/
def tensorDefect (ghat z u : RawCov2 M) : RawCov2 M :=
  deltaStar z (bianchi ghat u - bianchi z u)

/-- The vector operator before the common circle Haar projection. -/
def vectorOperator (ghat g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  bianchi ghat (lieTensor Y g)

/-- Both terms of K24 (5.4), retaining the actual-metric Lie derivative. -/
def actualMetricVectorDefect (ghat z g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  (bianchi ghat (killing z Y) - bianchi z (killing z Y)) +
    bianchi ghat (lieTensor Y (g - z))

def inverseDifferenceInChart (ghat z : RawCov2 M)
    (c : M) (x : FourSpace) : Mat4 :=
  inverseMetricInChart ghat c x - inverseMetricInChart z c x

def connectionDifferenceInChart (ghat z : RawCov2 M)
    (c : M) (x : FourSpace) (k i j : Fin 4) : ℝ :=
  christoffelInChart ghat c x k i j - christoffelInChart z c x k i j

/-- Right hand side of K24 (3.1), in terms of the actual metric difference. -/
def connectionDifferenceExpansion (ghat z : RawCov2 M)
    (c : M) (x : FourSpace) (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, inverseMetricInChart ghat c x k l *
    (nablaTensorInChart z (ghat - z) c x i j l +
     nablaTensorInChart z (ghat - z) c x j i l -
     nablaTensorInChart z (ghat - z) c x l i j)

/-- Full K24 (3.4), including the derivative of inverse metric difference. -/
def bianchiDifferenceExpansion (ghat z u : RawCov2 M)
    (c : M) (x : FourSpace) (j : Fin 4) : ℝ :=
  -(∑ a : Fin 4, ∑ b : Fin 4,
    inverseDifferenceInChart ghat z c x a b * nablaTensorInChart z u c x a b j) +
  (1 / 2 : ℝ) * (∑ a : Fin 4, ∑ b : Fin 4,
    inverseDifferenceInChart ghat z c x a b * nablaTensorInChart z u c x j a b) +
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ p : Fin 4,
    inverseMetricInChart ghat c x a b * connectionDifferenceInChart ghat z c x p a b *
      cov2InChart u c x p j) +
  (∑ a : Fin 4, ∑ b : Fin 4, ∑ p : Fin 4,
    inverseMetricInChart ghat c x a b * connectionDifferenceInChart ghat z c x p a j *
      cov2InChart u c x b p) +
  (1 / 2 : ℝ) * (∑ a : Fin 4, ∑ b : Fin 4,
    nablaContravariantInChart z (inverseDifferenceInChart ghat z) c x j a b *
      cov2InChart u c x a b)

def bianchiDifferenceSymbol (ghat z : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (u : Mat4) (j : Fin 4) : ℝ :=
  -(∑ a : Fin 4, ∑ b : Fin 4,
    inverseDifferenceInChart ghat z c x a b * xi a * u b j) +
  (1 / 2 : ℝ) * ∑ a : Fin 4, ∑ b : Fin 4,
    inverseDifferenceInChart ghat z c x a b * xi j * u a b

/-- The polynomial of K24 (3.7). A symbol-identification theorem is still required. -/
def tensorDefectSymbolFormula (ghat z : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (u : Mat4) (i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) *
    (xi i * bianchiDifferenceSymbol ghat z c x xi u j +
     xi j * bianchiDifferenceSymbol ghat z c x xi u i)

/-- A genuine tensor with value and first jet zero at the chosen chart point,
and second jet `xi ⊗ xi ⊗ u`. Its global extension need only be regular near
that point, which is sufficient to test the local differential expression. -/
def quadraticJetTensor (c : M) (x : FourSpace) (xi : Fin 4 → ℝ)
    (u : Mat4) : RawCov2 M :=
  fun p => cov2FromChartAt c p (fun i j =>
    (1 / 2 : ℝ) * (∑ a : Fin 4, xi a * (chartAt FourSpace c p a - x a)) ^ 2 * u i j)

/-- The actual second-jet test of the differential operator, as opposed to
the polynomial expected to equal it. The identification is still unproved. -/
def tensorDefectPrincipalSymbol (ghat z : RawCov2 M) (c : M) (x : FourSpace)
    (xi : Fin 4 → ℝ) (u : Mat4) : Mat4 :=
  cov2InChart (tensorDefect ghat z (quadraticJetTensor c x xi u)) c x

def flat (g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  fun p => g p (Y p)

def nablaVectorInChart (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace) (a b : Fin 4) : ℝ :=
  coordDeriv (fun y => vectorInChart Y c y b) a x +
    ∑ p : Fin 4, christoffelInChart g c x b a p * vectorInChart Y c x p

/-- `∇_a ∇_b Y^d`, including the correction for its covariant `b` index. -/
def secondNablaVectorInChart (g : RawCov2 M) (Y : RawVector M)
    (c : M) (x : FourSpace) (a b d : Fin 4) : ℝ :=
  coordDeriv (fun y => nablaVectorInChart g Y c y b d) a x +
    (∑ p : Fin 4, christoffelInChart g c x d a p * nablaVectorInChart g Y c x b p) -
    (∑ p : Fin 4, christoffelInChart g c x p a b * nablaVectorInChart g Y c x p d)

/-- Covector realization of `∇*∇Y`, with the negative trace convention. -/
def roughVectorLaplacianFlat (g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  covectorFromCoordinates (fun c x j =>
    -(∑ a : Fin 4, ∑ b : Fin 4, ∑ d : Fin 4,
      inverseMetricInChart g c x a b * cov2InChart g c x j d *
        secondNablaVectorInChart g Y c x a b d))

def ricciVectorFlat (g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  fun p => ricci g p (Y p)

/-- Differentiate an actual one-parameter tensor family in each scalar
coefficient. Equality to any Banach derivative is a theorem obligation. -/
def cov2VariationDerivative (F : ℝ → RawCov2 M) (t : ℝ) : RawCov2 M :=
  cov2FromCoordinates (fun c x i j => deriv (fun s => cov2InChart (F s) c x i j) t)

def einsteinLinearization (lam : ℝ) (z u : RawCov2 M) : RawCov2 M :=
  cov2VariationDerivative (fun t => einsteinResidual lam (z + t • u)) 0

/-- Candidate invariant-center linearization, tied to actual Ricci and Bianchi.
The theorem identifying it with `D Ψ` is not baked into this definition. -/
def gaugedLinearization (lam : ℝ) (ghat z u : RawCov2 M) : RawCov2 M :=
  einsteinLinearization lam z u + deltaStar z (bianchi ghat u)

end K24.Global


/- Original source module: K24Work.Global.Action -/

/-!
# The actual common circle action for K24

`CircleAction` contains a genuine smooth group action on the manifold. Pullbacks
below are computed using its actual manifold differential. It contains no
projection operator, geometric PDE operator, or requested analytic estimate.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace K24.Global

variable (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- A smooth action of the actual unit circle, with the same action used for
reference, center, tensor, covector, and vector sections. -/
structure CircleAction where
  act : Circle → M → M
  one_act : ∀ p, act 1 p = p
  mul_act : ∀ s t p, act (s * t) p = act s (act t p)
  smooth : ContMDiff ((𝓡 1).prod I4) I4 ∞
    (fun q : Circle × M => act q.1 q.2)

variable {M}

def actionPullbackCov2 (rho : CircleAction M) (t : Circle)
    (u : RawCov2 M) : RawCov2 M :=
  pullbackCov2 (rho.act t) u

def actionPullbackCovector (rho : CircleAction M) (t : Circle)
    (u : RawCovector M) : RawCovector M :=
  pullbackCovector (rho.act t) u

/-- Vector pullback uses the differential of the inverse action, evaluated
at the image point. It is not the covector pullback. -/
def actionPullbackVector (rho : CircleAction M) (t : Circle)
    (Y : RawVector M) : RawVector M :=
  fun p => mfderiv I4 I4 (rho.act t⁻¹) (rho.act t p) (Y (rho.act t p))

def IsInvariantCov2 (rho : CircleAction M) (u : RawCov2 M) : Prop :=
  ∀ t : Circle, actionPullbackCov2 rho t u = u

def IsInvariantCovector (rho : CircleAction M) (u : RawCovector M) : Prop :=
  ∀ t : Circle, actionPullbackCovector rho t u = u

def IsInvariantVector (rho : CircleAction M) (Y : RawVector M) : Prop :=
  ∀ t : Circle, actionPullbackVector rho t Y = Y

end K24.Global


/- Original source module: K24Work.Global.Haar -/

/-!
# Genuine pointwise Haar projections for K24

The averages are scalar Bochner integrals of the coordinates in each fixed
finite-dimensional fiber, followed by reconstruction of the actual tensor.
They are not Bochner integrals in a big-Holder section norm, where norm
continuity of pullback must not be presumed. Separate explicit predicates below
record fiberwise integrability; the full target must establish them for its
admissible sections and cannot exploit the integral's nonintegrable default.

The canonical chart selects a fiber basis only for this finite-dimensional
integration. It does not replace the adapted cover norms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Manifold ContDiff BigOperators

namespace K24.Global

instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Haar measure normalized on the compact circle itself, hence total mass 1. -/
def circleHaar : Measure Circle :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts Circle)

instance circleHaar_isProbabilityMeasure : IsProbabilityMeasure circleHaar := by
  constructor
  exact Measure.haarMeasure_self

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

def Cov2HaarIntegrable (rho : CircleAction M) (u : RawCov2 M) : Prop :=
  ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
    ∀ i j : Fin 4, Integrable
      (fun t : Circle => cov2InChart (actionPullbackCov2 rho t u) c x i j) circleHaar

def CovectorHaarIntegrable (rho : CircleAction M) (u : RawCovector M) : Prop :=
  ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
    ∀ i : Fin 4, Integrable
      (fun t : Circle => covectorInChart (actionPullbackCovector rho t u) c x i) circleHaar

def VectorHaarIntegrable (rho : CircleAction M) (Y : RawVector M) : Prop :=
  ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
    ∀ i : Fin 4, Integrable
      (fun t : Circle => vectorInChart (actionPullbackVector rho t Y) c x i) circleHaar

def cov2Pi0 (rho : CircleAction M) (u : RawCov2 M) : RawCov2 M :=
  cov2FromCoordinates (fun c x i j =>
    ∫ t : Circle, cov2InChart (actionPullbackCov2 rho t u) c x i j ∂circleHaar)

def covectorPi0 (rho : CircleAction M) (u : RawCovector M) : RawCovector M :=
  covectorFromCoordinates (fun c x i =>
    ∫ t : Circle, covectorInChart (actionPullbackCovector rho t u) c x i ∂circleHaar)

def vectorPi0 (rho : CircleAction M) (Y : RawVector M) : RawVector M :=
  fun p =>
    let e := chartAt FourSpace p
    mfderiv I4 I4 e.symm (e p)
      (∑ i : Fin 4, (∫ t : Circle,
        vectorInChart (actionPullbackVector rho t Y) p (e p) i ∂circleHaar) • basisVector i)

def cov2PiPerp (rho : CircleAction M) (u : RawCov2 M) : RawCov2 M :=
  u - cov2Pi0 rho u

def covectorPiPerp (rho : CircleAction M) (u : RawCovector M) : RawCovector M :=
  u - covectorPi0 rho u

def vectorPiPerp (rho : CircleAction M) (Y : RawVector M) : RawVector M :=
  Y - vectorPi0 rho Y

def IsNonzeroCov2 (rho : CircleAction M) (u : RawCov2 M) : Prop :=
  cov2Pi0 rho u = 0

def IsNonzeroCovector (rho : CircleAction M) (u : RawCovector M) : Prop :=
  covectorPi0 rho u = 0

def IsNonzeroVector (rho : CircleAction M) (Y : RawVector M) : Prop :=
  vectorPi0 rho Y = 0

end K24.Global


/- Original source module: K24Work.Global.Gauge -/

/-!
# The literal partial-gauged map and its actual variation derivatives

Every operator here is computed from genuine tensor sections and the same
circle action. `partialGaugeVariation` is a coefficientwise variation
derivative. Its status as the Frechet derivative in the specified cover norms
is a conclusion of the full unproved target, never assumed by definition.
-/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace K24.Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- K24 (1.1), including the metric-dependent `deltaStar q` factor. -/
def partialGauge (rho : CircleAction M) (lam : ℝ) (ghat q : RawCov2 M) : RawCov2 M :=
  einsteinResidual lam q + deltaStar q (covectorPiPerp rho (bianchi ghat (q - ghat)))

/-- The actual coefficient variation of the literal nonlinear map. -/
def partialGaugeVariation (rho : CircleAction M) (lam : ℝ)
    (ghat z u : RawCov2 M) : RawCov2 M :=
  cov2VariationDerivative (fun t => partialGauge rho lam ghat (z + t • u)) 0

/-- The derivative of the metric-dependent symmetrized gradient. This term
must occur in the product rule before invariant-center cancellation. -/
def deltaStarMetricVariation (z u : RawCov2 M) (eta : RawCovector M) : RawCov2 M :=
  cov2VariationDerivative (fun t => deltaStar (z + t • u) eta) 0

/-- The full product-rule expression in K24 (2.1). -/
def partialGaugeProductRule (rho : CircleAction M) (lam : ℝ)
    (ghat z u : RawCov2 M) : RawCov2 M :=
  einsteinLinearization lam z u +
    deltaStarMetricVariation z u (covectorPiPerp rho (bianchi ghat (z - ghat))) +
    deltaStar z (covectorPiPerp rho (bianchi ghat u))

/-- The actual projected tensor linearization, not a free operator input. -/
def projectedTensorOperator (rho : CircleAction M) (lam : ℝ)
    (ghat z u : RawCov2 M) : RawCov2 M :=
  cov2PiPerp rho (partialGaugeVariation rho lam ghat z u)

/-- The actual projected vector-to-covector map at a nearby metric. -/
def projectedVectorOperator (rho : CircleAction M)
    (ghat g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  covectorPiPerp rho (vectorOperator ghat g Y)

/-- Both terms in the actual-metric vector defect, under the genuine common
one-form Haar projection. -/
def projectedActualVectorDefect (rho : CircleAction M)
    (ghat z g : RawCov2 M) (Y : RawVector M) : RawCovector M :=
  covectorPiPerp rho (actualMetricVectorDefect ghat z g Y)

end K24.Global


