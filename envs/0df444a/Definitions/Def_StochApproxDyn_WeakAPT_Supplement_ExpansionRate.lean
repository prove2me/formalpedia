-- Prove2me | Definitions.Def_StochApproxDyn_WeakAPT_Supplement_ExpansionRate
-- name    : StochApproxDyn_WeakAPT_Supplement_ExpansionRate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:12:35.748798+00:00
-- url     : https://prove2.me/theorems/a9e91b02-72bd-4667-8873-cb59b560c1bb
-- title:
--   §8.2–8.3 — expansion constant $EC(\Phi_t,K)$, ergodic measures of a flow, and the smallest Lyapounov exponent $\lambda_1(\mu)$
-- statement:
--   These definitions set up §8.2–8.3 of the paper. Let $M$ be a manifold whose tangent spaces carry a Riemannian norm $\|v\|$, and let $\Phi=\{\Phi_t\}_{t\in\mathbb R}$ be a flow on $M$ with tangent maps $D\Phi_t(x):T_xM\to T_{\Phi_t(x)}M$.
--
--   1. The **forward semiflow** of $\Phi$ is $\{\Phi_t\}_{t\ge 0}$. A Borel probability measure $\mu$ is **$\Phi$-invariant** if $(\Phi_t)_*\mu=\mu$ for all $t\ge0$; for a flow this is the same as $\mu(A)=\mu(\Phi_t(A))$ for every Borel set $A$ and every $t\in\mathbb R$.
--   2. An invariant measure $\mu$ is **ergodic** if every $\Phi$-invariant Borel set $A$ (that is, $\Phi_t(A)=A$ for all $t\in\mathbb R$) has $\mu(A)\in\{0,1\}$. It has **support in $K$** if $\mu(M\setminus K)=0$.
--   3. The **minimal norm** of a linear map $L$ is $m(L)=\inf\{\|Lv\|:\|v\|=1\}$, and the **expansion constant** of $\Phi_t$ at $K\subseteq M$ is
--   $$EC(\Phi_t,K)=\inf_{x\in K} m(D\Phi_t(x)).$$
--   4. A number $\lambda$ is the **smallest Lyapounov exponent** $\lambda_1(\mu)$ of an ergodic $\mu$ if, for $\mu$-almost every $x$,
--   $$\lambda=\lim_{t\to\infty}\frac1t\log m(D\Phi_t(x)).$$
--
--   The expansion rate $\mathcal E(\Phi,K)=\lim_{t\to\infty}\frac1t\log EC(\Phi_t,K)$ and Schreiber's characterization of it (Theorem 8.12) are stated with these objects.
--
--   **Formalization Note** The manifold structure is Mathlib's (`ChartedSpace`, `mfderiv`), the Riemannian norm is a `RiemannianBundle` on the tangent bundle, and invariance reuses the published `StochApproxDyn.WeakAPT.invariantMeasures` applied to the forward semiflow. The minimal norm and the expansion constant take values in $[0,\infty]$, so that an infimum over an empty set is $+\infty$, and exponents take values in the extended reals. The paper defines $\lambda_1(\mu)$ through the Oseledec splitting $T_xM=E_1(x)\oplus\dots\oplus E_{r(x)}(x)$ as the smallest of the exponents $\lambda_i(x)$; by Oseledec's theorem it is the almost sure limit of $\frac1t\log m(D\Phi_t(x))$, which is the form used here.
--
--   Differences from the source:
--   - encoding: real infima and the Oseledec splitting → extended-real infima and the almost sure conorm-growth limit; reason: the latter equals the smallest exponent on the theorem’s compactly supported ergodic measures; empty infima and zero tangent spaces use $+\infty$.
--   - generalization: finite-dimensional tangent maps → arbitrary continuous linear maps for the auxiliary `minNorm`; reason: every source tangent map specializes to the identical unit-sphere infimum.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 40, §8.2 (minimal norm, expansion constant, expansion rate); pp. 43–44, §8.3 (invariant and ergodic measures, Lyapounov exponents)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_InvariantMeasures

open scoped NNReal ENNReal Manifold
open Bundle
open MeasureTheory

namespace StochApproxDyn.WeakAPT.Supplement

/-- The forward semiflow `{Φ_t}_{t ≥ 0}` of a flow `Φ : ℝ × M → M`: the same map, restricted to
nonnegative times. It is used to apply the published notion of invariant measure (stated for
semiflows) to a flow. -/
def toSemiflow {M : Type*} [TopologicalSpace M] (Φ : Flow ℝ M) : Flow ℝ≥0 M where
  toFun t x := Φ (t : ℝ) x
  cont' := Φ.cont'.comp (NNReal.continuous_coe.prodMap continuous_id)
  map_add' t s x := by simp [Φ.map_add]
  map_zero' x := by simp [Φ.map_zero_apply]

/-- Ergodicity of an invariant Borel probability measure `μ` for a flow `Φ` (Benaïm 1999, §8.3,
p. 43): every `Φ`-invariant Borel set `A` (`Φ_t(A) = A` for every `t ∈ ℝ`) has measure `0` or `1`.
Invariance of `μ` itself is required separately (through `invariantMeasures`). -/
def IsErgodicFlow {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (Φ : Flow ℝ M)
    (μ : ProbabilityMeasure M) : Prop :=
  ∀ A : Set M, MeasurableSet A → (∀ t : ℝ, Φ t '' A = A) →
    (μ : Measure M) A = 0 ∨ (μ : Measure M) A = 1

/-- The minimal norm `m(L) = inf {‖L v‖ : ‖v‖ = 1}` of a linear map between normed spaces
(Benaïm 1999, §8.2, p. 40), valued in `[0, ∞]`; on a zero space the infimum over the empty set
is `∞`. -/
noncomputable def minNorm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) : ℝ≥0∞ :=
  ⨅ (v : V) (_ : ‖v‖ = 1), ‖L v‖ₑ

/-- The expansion constant `EC(Φ_t, K) = inf_{x ∈ K} m(DΦ_t(x))` of a flow on a Riemannian
manifold at a set `K` (Benaïm 1999, §8.2, p. 40), where `DΦ_t(x) : T_x M → T_{Φ_t x} M` is the
tangent map and tangent vectors are measured in the Riemannian norm. Valued in `[0, ∞]`
(`∞` when `K = ∅`). -/
noncomputable def expansionConstant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (Φ : Flow ℝ M) (K : Set M) (t : ℝ) : ℝ≥0∞ :=
  ⨅ x ∈ K, minNorm (mfderiv I I (Φ t) x)

/-- `μ` is an ergodic invariant probability measure of the flow `Φ` whose support is contained in
`K` (Benaïm 1999, §8.3, pp. 43–44): `μ` is `Φ`-invariant (`(Φ_t)_* μ = μ` for all `t ≥ 0`, which
for a flow is the same as for all `t ∈ ℝ`), ergodic, and `μ(M \ K) = 0`. -/
def IsErgodicSupportedIn {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (Φ : Flow ℝ M)
    (K : Set M) (μ : ProbabilityMeasure M) : Prop :=
  μ ∈ StochApproxDyn.WeakAPT.invariantMeasures (toSemiflow Φ) ∧ IsErgodicFlow Φ μ ∧
    (μ : Measure M) Kᶜ = 0

/-- `λ` is the smallest Lyapounov exponent `λ₁(μ)` of the ergodic measure `μ` (Benaïm 1999,
§8.3, p. 44): for `μ`-almost every `x`,
`λ = lim_{t → ∞} (1/t) log m(DΦ_t(x))`, where `m` is the minimal norm. By Oseledec's theorem
the smallest exponent `λ₁(x) = min_i λ_i(x)` of the splitting `T_x M = ⊕ E_i(x)` is this limit,
and for ergodic `μ` it is `μ`-a.e. equal to the constant `λ₁(μ)`. The value is taken in `EReal`
(`log ∞ = ∞` on a zero-dimensional manifold). -/
def IsSmallestLyapunovExponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [MeasurableSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (Φ : Flow ℝ M) (μ : ProbabilityMeasure M) (lam : EReal) : Prop :=
  ∀ᵐ x ∂(μ : Measure M), Filter.Tendsto
    (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ENNReal.log (minNorm (mfderiv I I (Φ t) x)))
    Filter.atTop (nhds lam)

end StochApproxDyn.WeakAPT.Supplement


