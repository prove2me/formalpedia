-- Prove2me | Definitions.Def_UnconditionalKLS_Dunkl_Model
-- name    : UnconditionalKLS_Dunkl_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T20:06:52.688782+00:00
-- url     : https://prove2.me/theorems/cf1a4363-2bed-4eed-9b80-a6a567cc0834
-- title:
--   Unconditional potentials, coordinate stretch, and Dunkl expression
-- statement:
--   Work in real Euclidean space $\mathbb R^n$, with coordinate reflections $r_j$ negating exactly one coordinate. An unconditional function is invariant under every $r_j$. The model includes convex extended potentials $V:\mathbb R^n\to\mathbb R\cup\{+\infty\}$, with measurable, normalized density $e^{-V}$ and $e^{-\infty}=0$. Convexity is expressed by convexity of the epigraph. Isotropy requires finite second moments, zero mean, and $\mathbb E[X_iX_j]=\delta_{ij}$.
--
--   For $S>0$, define
--   $$q_S(r)=\sqrt{r/\sqrt{S^2+r^2}},\quad g_S(r)=\int_0^r q_S(t)\,dt,\quad (T_Sy)_j=\operatorname{sgn}(y_j)g_S(|y_j|),\quad c_j(x)=\frac{S^2}{2(S^2+x_j^2)}.$$
--   The transported law is $(T_S^{-1})_\#\mu$, using the specified map's inverse. For a real potential $W$, the auxiliary law is the density $e^{-W}\prod_jq_S(|x_j|)$ divided by its actual integral. `Admissible` is precisely unconditional $C^2$ regularity and (2.4), with existential positive upper Hessian and coercivity constants and a nonnegative defect. `Regular` is precisely the temporary condition (2.5), including normalization and the coordinate second-moment bounds; it does not require isotropy.
--
--   The optimal Poincaré constant is an extended nonnegative infimum of finite constants satisfying the published ambient local-slope inequality. If no constant works the value is $+\infty$. Covariance uses the published centered operator. Weak derivatives use the published distributional definition on the open union of orthants. The differential expression is
--   $$Af=-\Delta f+\langle\nabla W,\nabla f\rangle-\sum_j\frac{c_j}{x_j}\partial_jf+\sum_j\frac{c_j}{2x_j^2}(f-f\circ r_j).$$
--   The last two terms are defined together by the Taylor integral (A.3), including on hyperplanes. This model supplies data and formulas only; it contains no spectral bound or eigenfunction certificate.
--
--   **Formalization Note** Coordinates are indexed by `Fin n`. Quotients used only almost everywhere may take their total-function value on the null hyperplanes. Smooth derivatives are Fréchet derivatives; nonsmooth domain derivatives are distributional.
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), pp. 1, 8–10, 14–15, 31–32; (1.1), (2.1)–(2.5), (3.1)–(3.3), (A.3). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Fn (n : ℕ) := Space n → ℝ
variable {n : ℕ}
def reflect (i : Fin n) (x : Space n) : Space n :=
  WithLp.toLp 2 (Function.update (fun j => x j) i (-x i))
def Unconditional {α : Type*} (f : Space n → α) : Prop :=
  ∀ i x, f (reflect i x) = f x
def d (f : Fn n) (i : Fin n) : Fn n := HunterPDE.Shared.partialDeriv f i
def grad (f : Fn n) (x : Space n) : Space n := WithLp.toLp 2 (fun i => d f i x)
def hess (f : Fn n) (x u v : Space n) : ℝ :=
  ∑ i, ∑ j, d (d f j) i x * u i * v j
/-- The optimum in the ambient local-metric-slope convention. An empty infimum is infinity. -/
def poincare (μ : Measure (Space n)) : ℝ≥0∞ :=
  ⨅ (ν : ProbabilityMeasure (Space n)) (_ : (ν : Measure (Space n)) = μ),
    ⨅ C : {C : NNReal // FunctionalInequalities.Poincare.LocalSlope.Holds ν C}, (C.1 : ℝ≥0∞)
def covNorm (μ : Measure (Space n)) : ℝ := ‖FunctionalInequalities.Covariance.operator μ‖
def q (S r : ℝ) : ℝ := Real.sqrt (r / Real.sqrt (S^2 + r^2))
def g (S r : ℝ) : ℝ := ∫ t in (0 : ℝ)..r, q S t
def transport (S : ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun j => SignType.sign (x j) * g S |x j|)
def inverseTransport (S : ℝ) : Space n → Space n := Function.invFun (transport S)
def sourceLaw (S : ℝ) (μ : Measure (Space n)) : Measure (Space n) :=
  Measure.map (inverseTransport S) μ
def densityLaw (V : Fn n) : Measure (Space n) := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))
def c (S r : ℝ) : ℝ := S^2 / (2 * (S^2 + r^2))
def cj (S : ℝ) (i : Fin n) (x : Space n) : ℝ := c S (x i)
def dc (S : ℝ) (i : Fin n) (x : Space n) : ℝ := -S^2 * x i / (S^2 + (x i)^2)^2
def weight (S : ℝ) (W : Fn n) (x : Space n) : ℝ :=
  Real.exp (-W x) * ∏ j, q S |x j|
def normalizer (S : ℝ) (W : Fn n) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (weight S W x)
def eta (S : ℝ) (W : Fn n) : Measure (Space n) :=
  (normalizer S W)⁻¹ • volume.withDensity (fun x => ENNReal.ofReal (weight S W x))
/-- Exactly (2.4), with its constants existential; no spectral or domain assumptions. -/
def Admissible (W : Fn n) : Prop :=
  ContDiff ℝ 2 W ∧ Unconditional W ∧ ∃ K κ B : ℝ,
    0 < K ∧ 0 < κ ∧ 0 ≤ B ∧
    (∀ x u, 0 ≤ hess W x u u ∧ hess W x u u ≤ K * ‖u‖^2) ∧
    ∀ x, κ * ‖x‖^2 - B ≤ inner ℝ x (grad W x)
/-- Exactly the temporary assumptions (2.5), including unconditionality from the section. -/
def Regular (V : Fn n) (κ K : ℝ) : Prop :=
  ContDiff ℝ ∞ V ∧ Unconditional V ∧ 0 < κ ∧ κ ≤ K ∧
  IsProbabilityMeasure (densityLaw V) ∧
  (∀ x u, κ * ‖u‖^2 ≤ hess V x u u ∧ hess V x u u ≤ K * ‖u‖^2) ∧
  (∀ j : Fin n, Integrable (fun x => (x j)^2) (densityLaw V) ∧
    ∫ x, (x j)^2 ∂densityLaw V ≤ 2)
/-- The nonsmooth, possibly bounded-support density model of §1. -/
structure Potential (n : ℕ) where
  value : Space n → WithTop ℝ
  convex_epigraph : Convex ℝ {p : Space n × ℝ | value p.1 ≤ (p.2 : WithTop ℝ)}
  unconditional : Unconditional value
  normalized : (∫⁻ x, ENNReal.ofReal (if value x = ⊤ then 0 else Real.exp (-(value x).untopD 0))) = 1

def Potential.law (V : Potential n) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (if V.value x = ⊤ then 0 else Real.exp (-(V.value x).untopD 0)))
def Isotropic (μ : Measure (Space n)) : Prop :=
  MemLp id 2 μ ∧ (∫ x, x ∂μ) = 0 ∧
    ∀ i j : Fin n, (∫ x, x i * x j ∂μ) = if i = j then 1 else 0
/-- The open union of orthants; the omitted hyperplanes are eta-null. -/
def orthants : Set (Space n) := {x | ∀ j, x j ≠ 0}
def weakPartial (f : Fn n) (j : Fin n) : Fn n :=
  HunterPDE.Shared.weakDeriv orthants (Pi.single j 1) f
def WeaklyDifferentiable (f : Fn n) : Prop :=
  ∀ j : Fin n, ∃ v, HunterPDE.Shared.HasWeakDeriv orthants (Pi.single j 1) f v
def weakGrad (f : Fn n) (x : Space n) : Space n := WithLp.toLp 2 (fun j => weakPartial f j x)
def difference (f : Fn n) (j : Fin n) (x : Space n) : ℝ :=
  (f x - f (reflect j x)) / (2 * x j)
def quotient (f : Fn n) (i : Fin n) (x : Space n) : ℝ := f x / x i
/-- (3.3), with the paired Taylor extension (A.3) at every hyperplane. -/
def expression (S : ℝ) (W f : Fn n) (x : Space n) : ℝ :=
  -(∑ j, d (d f j) j x) + inner ℝ (grad W x) (grad f x) -
    ∑ j, cj S j x / 2 * ∫ t in (-1 : ℝ)..1,
      (1+t) * d (d f j) j (WithLp.toLp 2 (Function.update (fun k => x k) j (t*x j)))
def polynomialGrowth (f : Fn n) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ m : ℕ, ∀ x, |f x| + ‖grad f x‖ + ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C * (1 + ‖x‖)^m
end UnconditionalKLS.Dunkl


