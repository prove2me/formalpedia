-- Prove2me | Definitions.Def_GaussPolyReg_Approx_Supplement_Noise
-- name    : GaussPolyReg_Approx_Supplement_Noise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:26:35.83195+00:00
-- url     : https://prove2.me/theorems/434d3aef-70d4-4c79-8d8c-9b9ff38d71da
-- title:
--   Graded noise stability, event indicators and Gaussian halfspaces
-- statement:
--   For independent standard Gaussian product vectors $X,G$ and grades $g_i\ge1$, set
--
--   $$Y_i=s^{g_i}X_i+\sqrt{1-s^{2g_i}}\,G_i,\qquad T_s f(X)=\mathbb E_G f(Y),\qquad \operatorname{Stab}_s(f)=\mathbb E_{X,G}[f(X)f(Y)].$$
--
--   The operator is the actual conditional expectation realized in $L^2$, and stability is the Bochner integral against the independent product pair. For $|s|\le1$, both marginals are standard Gaussian products, and the stability integrand is integrable for every $L^2$ input by Cauchy–Schwarz. The spectral identity $\operatorname{Stab}_s(f)=\sum_{d\ge0}s^d\|\Pi_df\|_2^2$ is the source's Eq. (2.2), not a defining assumption. In particular, grade-$r$ coordinates have correlation $s^r$; ordinary finite-dimensional inputs have all grades one.
--
--   Events may be measurable for the completed Gaussian measure; $\mathbf1_A$ is their $L^2$ class, $\gamma_n(A)$ their Gaussian measure, and $\operatorname{Stab}_s(A)=\operatorname{Stab}_s(\mathbf1_A)$. The comparison halfspace is $H_a=(-\infty,\Phi^{-1}(a))$ in one coordinate. The real quantile is imported from `Cohen2019_Robust_Phi` and used only for $0<a<1$.
--
--   Finite halfspaces are $\{x:\sum_i c_ix_i\ge t\}$. A countable grade-one normal uses the Hilbert-space sum $L_c=\sum_i c_iZ_{1,i}$ in $L^2$, and its halfspace is $\{L_c\ge t\}$. Under $\sum_i c_i^2=1$ this orthogonal series converges and permits infinitely many nonzero coefficients.
--
--   These constructions provide the setting for Lemmas 4.2–4.3 and Theorem 4.1 without assuming any source theorem. The raw-function conversion returns zero outside $L^2$, but every allowed event indicator, Gaussian coordinate and conditional expectation here belongs to $L^2$. Parameters outside $|s|\le1$ and non-square-summable normals are not used.
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), §2, p.3, (2.2); §4, pp.13–14. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Supplement_Graded
import Definitions.Def_Cohen2019_Robust_Phi

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
noncomputable section

namespace GaussPolyReg.Approx.Supplement

/-- L² realization. Zero is used only outside L²; every theorem input is L².
In particular null-measurable indicators and Gaussian coordinates belong to L². -/
def asGaussianL2 {I : Type*} (f : (I → ℝ) → ℝ) : GaussianL2 I := by
  classical
  exact if h : MemLp f 2 (gaussianProduct I) then h.toLp f else 0

/-- Indicator as an a.e. class; theorem events are measurable for the completion. -/
def indicatorL2 {I : Type*} (A : Set (I → ℝ)) : GaussianL2 I :=
  asGaussianL2 (A.indicator (fun _ => (1 : ℝ)))

/-- Concrete graded Gaussian coupling (§2, (2.2)). On grade r the correlation
is s^r. For |s|≤1 both marginals are standard product Gaussians. -/
def noiseSample {I : Type*} (g : I → ℕ) (s : ℝ) (x w : I → ℝ) : I → ℝ :=
  fun i => s ^ (g i) * x i + Real.sqrt (1 - (s ^ (g i)) ^ 2) * w i

/-- The actual conditional-expectation OU operator, using fresh independent
Gaussian w. For |s|≤1 and L² input it belongs to L² by conditional Jensen. -/
def noiseOperator {I : Type*} (g : I → ℕ) (s : ℝ)
    (f : GaussianL2 I) : GaussianL2 I :=
  asGaussianL2 (fun x => ∫ w, f (noiseSample g s x w) ∂gaussianProduct I)

/-- Stability under the concrete correlated joint law, not an assumed spectral
identity. For L² f and |s|≤1 the integrand is integrable by Cauchy–Schwarz
and the two Gaussian marginals. Its spectral formula is (2.2), to be proved. -/
def noiseStability {I : Type*} (g : I → ℕ) (s : ℝ) (f : GaussianL2 I) : ℝ :=
  ∫ z, f z.1 * f (noiseSample g s z.1 z.2)
    ∂((gaussianProduct I).prod (gaussianProduct I))

/-- Standard Gaussian measure of a finite-dimensional event. -/
def gaussianMass {n : ℕ} (A : Set (Fin n → ℝ)) : ℝ :=
  (gaussianProduct (Fin n)).real A

def setStability {n : ℕ} (s : ℝ) (A : Set (Fin n → ℝ)) : ℝ :=
  noiseStability (fun _ => 1) s (indicatorL2 A)

/-- H_a=(-∞,Φ⁻¹(a)), represented in one coordinate; only 0<a<1 is used.
The Gaussian quantile itself is the published Cohen2019.Robust.PhiInvReal. -/
def modelHalfspace (a : ℝ) : Set (Fin 1 → ℝ) :=
  {x | x 0 < Cohen2019.Robust.PhiInvReal a}

/-- The paper's affine halfspace. Normalization is imposed in the theorem. -/
def finiteHalfspace {n : ℕ} (c : Fin n → ℝ) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | t ≤ ∑ i, c i * x i}

/-- An infinite square-summable normal is synthesized in L², not by an
unordered scalar sum at every sample point (which would demand absolute convergence).
For ∑ c_i²=1 the orthogonal L² series converges and is standard normal. -/
def gradeOneLinear (c : ℕ → ℝ) : GradedL2 :=
  ∑' i : ℕ, (c i) • asGaussianL2 (fun x : GradedPoint => x (1, i))

def gradeOneHalfspace (c : ℕ → ℝ) (t : ℝ) : Set GradedPoint :=
  {x | t ≤ gradeOneLinear c x}

end GaussPolyReg.Approx.Supplement


