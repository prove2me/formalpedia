-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_Inversion
-- name    : QMatVecLB_ConvexOpt_Inversion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:58.273442+00:00
-- url     : https://prove2.me/theorems/0a585473-1323-4b6d-8479-a65741538098
-- title:
--   Bordered Gaussian matrices and inverse-entry witnesses
-- statement:
--   The bordered matrix has scalar corner $a$, upper border $u^T$, left border $v$ and interior block $B$. Paper index 1 is index 0; the interior is embedded by the successor map. The inverse-entry indicator is explicitly zero on singular matrices. The witness density is the squared scaled interior-minor Cayley operator applied to the Gaussian density. The border probability is computed from independent standard normal border variables and is zero for singular $B$. Standard normal cumulative and density functions, $\Psi_\theta$, $g_\theta$, the independent scalar-expectation law, the Loewner promise and inverse first column are defined from these data. Gaussian matrix laws and singular-value notions reuse GaussianMatrix_basic.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, definitions in Sections 2–3, 5–6; anchor PDF p. 17 (printed p. 16).

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_QMatVecLB_ConvexOpt_Calculus

noncomputable section

namespace QMatVecLB.ConvexOpt
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

/-- Independent standard normal vector, in coordinate (not norm) representation. -/
def standardVector (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
def vectorEuclidean {n : ℕ} (v : Fin n → ℝ) : RVec n := WithLp.toLp 2 v

/-- Paper index 1 is Lean index 0; the remaining indices are Fin.succ. -/
def bordered {n : ℕ} (a : ℝ) (u v : Fin n → ℝ) (B : RMat n) : RMat (n+1) :=
  fun i j => Fin.cases (Fin.cases a u j) (fun i' => Fin.cases (v i') (B i') j) i

/-- Equation (88), with the source's explicit singular-matrix convention. -/
def inverseDecision {n : ℕ} (θ : ℝ) (A : RMat (n+1)) : ℝ := by
  classical
  exact if A.det = 0 then 0 else if θ ≤ |A⁻¹ 0 0| then 1 else 0

/-- Equation (89), as the squared minor differential operator, not its evaluated form. -/
def betaBorder (n : ℕ) : RMat (n+1) → ℂ :=
  let op := minorCayley (n := n+1) (r := n) Fin.succ Fin.succ (-(1 / (2 * Real.pi * Complex.I)))
  op (op (fun A => (gamma A : ℂ)))

def schurScalar {n : ℕ} (u v : Fin n → ℝ) (B : RMat n) : ℝ :=
  u ⬝ᵥ (B⁻¹ *ᵥ v)

/-- Equation (92): probability over the border, zero for singular B. -/
def borderProbability {n : ℕ} (θ : ℝ) (B : RMat n) : ℝ := by
  classical
  exact if B.det = 0 then 0 else
    (((gaussianReal 0 1).prod ((standardVector n).prod (standardVector n)))
      {auv | inverseDecision θ (bordered auv.1 auv.2.1 auv.2.2 B) = 1}).toReal

/-- Equations (119)--(120). -/
def normalCDF (x : ℝ) : ℝ := ((gaussianReal 0 1) (Set.Iic x)).toReal
def normalDensity (x : ℝ) : ℝ := Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)
def psi (θ x : ℝ) : ℝ := normalCDF (x + 1 / θ) - normalCDF (x - 1 / θ)
def g (θ x : ℝ) : ℝ := -x * deriv (psi θ) x

/-- Independent u,v,B in the order used for the scalar expectation. -/
def scalarLaw (n : ℕ) :=
  (standardVector n).prod ((standardVector n).prod (GaussianMatrix.gaussianMatrix n n))
def scalarIntegrand {n : ℕ} (θ : ℝ) (uvB : (Fin n → ℝ) × (Fin n → ℝ) × RMat n) : ℝ :=
  g θ (schurScalar uvB.1 uvB.2.1 uvB.2.2)

/-- Lower and upper Loewner bounds (174), including symmetry explicitly. -/
def positivePromise {n : ℕ} (M : RMat n) : Prop :=
  M.IsSymm ∧ (M - (1 / (n : ℝ)^13) • (1 : RMat n)).PosSemidef ∧
    ((9 * (n : ℝ)) • (1 : RMat n) - M).PosSemidef

def firstColumn {n : ℕ} (M : RMat (n+1)) : RVec (n+1) :=
  WithLp.toLp 2 (fun i => M⁻¹ i 0)
/-- Works for every positive dimension without selecting a fictitious index of Fin 0. -/
def firstColumnN {n : ℕ} (M : RMat n) : RVec n :=
  WithLp.toLp 2 (fun i => ∑ j : Fin n, if j.val = 0 then M⁻¹ i j else 0)

end QMatVecLB.ConvexOpt
end


