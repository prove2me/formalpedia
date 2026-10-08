-- Prove2me | Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM_v2
-- name    : SupportVectorMachines_Classification_RKHSAndSVM_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:42.09318+00:00
-- url     : https://prove2.me/theorems/5d4ffd9d-e3f7-4e1c-9867-2e9bbcfffe96
-- title:
--   RKHS of a measurable kernel, restricted Bayes risk, approximation error $A_2$, empirical risk, SVM solution, density in $L^1$ — $[0,\infty]$-valued risks
-- statement:
--   $H$ (with evaluation map $f \mapsto f(\cdot)$) is the **RKHS of the measurable kernel $k$** (Definition 4.18 with Lemma 4.24's measurability: $k(\cdot,x)$ measurable for every $x$). The **restricted Bayes risk** is $R^*_{L,P,H} := \inf_{f \in H} R_{L,P}(f) \in [0,\infty]$ (Eq. (5.30)); the **approximation error function** is $A_2(\lambda) := \inf_{f \in H} \lambda\|f\|_H^2 + R_{L,P}(f) - R^*_{L,P,H}$ (Definition 5.14, p. 179); the **empirical risk** of a sample $D$ is $R_{L,D}(f) := \frac1n \sum_i L(x_i,y_i,f(x_i))$; $f_{D,\lambda}$ is an **SVM solution** if it minimizes $\lambda\|g\|_H^2 + R_{L,D}(g)$ over $H$; and $H$ is **dense in $L^1(\mu)$** if every $\mu$-integrable $g$ is approximated in $L^1(\mu)$ by integrable elements of $H$.
--
--   **Formalization Note.** Identical to the retired module except that the restricted Bayes risk and $A_2$ are now infima in $[0,\infty]$ of the corrected $[0,\infty]$-valued risk (the retired real infima were junk for non-integrable functions in $H$); the subtraction in $A_2$ is exact whenever $R^*_{L,P,H} < \infty$, the book's standing requirement for Definition 5.14.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 119 Definition 4.18, p. 125 Lemma 4.24, p. 179 Definition 5.14 and Eq. (5.30), p. 23 Eq. (2.1)

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- `H` (with feature evaluation `toFun`) is the RKHS of the measurable kernel `k` over `X`
(Steinwart & Christmann, *Support Vector Machines*, Springer 2008, Definition 4.18, restated
locally per Hard Rule 9): `toFun` is injective, and there is a feature map `x ↦ kAt x`
reproducing both `k` and the evaluation functionals via the inner product. The kernel is also
required to be measurable (Lemma 4.24, p. 125: `k(·,x)` measurable for every `x` is equivalent
to every `f ∈ H` being measurable) — the book's own "measurable kernel" hypothesis, stated in
Lemma 4.24's own terms rather than as the derived consequence; it is what makes the `L`-risk of
every `f ∈ H` a genuine integral. -/
def IsRKHSOfKernel {X : Type*} [MeasurableSpace X] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) : Prop :=
  Function.Injective toFun ∧
    (∃ kAt : X → H, (∀ x x' : X, toFun (kAt x) x' = k x x') ∧
      ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x)) ∧
    ∀ x : X, Measurable (fun x' => k x' x)

/-- The restricted Bayes `L`-risk on `H` (Eq. (5.30), p. 179): `R*_{L,P,H} := inf_{f∈H} R_{L,P}(f)`,
the smallest `L`-risk attainable by a function in `H` (identified with `toFun f : X → ℝ`), an
infimum in `[0,∞]`. -/
noncomputable def restrictedBayesRisk {X : Type*} [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (L : Loss X)
    (P : Measure (X × ℝ)) : ENNReal :=
  ⨅ f : H, risk L P (toFun f)

/-- The approximation error function (Definition 5.14, p. 179):
`A2(λ) := inf_{f∈H} λ‖f‖²_H + R_{L,P}(f) − R*_{L,P,H}`, in `[0,∞]`; the subtraction is exact
whenever `R*_{L,P,H} < ∞` (the book's standing requirement for this definition), since the
infimum is always `≥ R*_{L,P,H}`. -/
noncomputable def approxErrorA2 {X : Type*} [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (L : Loss X)
    (P : Measure (X × ℝ)) (lam : ℝ) : ENNReal :=
  (⨅ f : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + risk L P (toFun f)) -
    restrictedBayesRisk H toFun L P

/-- The empirical `L`-risk of `f` with respect to a sample `D : Fin n → X × ℝ` (Definition 2.2,
Eq. (2.1), p. 23, restated locally): `R_{L,D}(f) := (1/n) ∑ᵢ L(xᵢ,yᵢ,f(xᵢ))`, a finite sum of
nonnegative reals. -/
noncomputable def empiricalRisk {X : Type*} [MeasurableSpace X] (n : ℕ) (L : Loss X)
    (D : Fin n → X × ℝ) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L (D i).1 (D i).2 (f (D i).1)

/-- `f` is the SVM decision function `f_{D,λ}` for sample `D` (the minimizer used throughout
Chapters 5-6, restated locally): `f` minimizes `g ↦ λ‖g‖²_H + R_{L,D}(g)` over `H`. -/
def IsSVMSolution {X : Type*} [MeasurableSpace X] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (L : Loss X) (lam : ℝ) (n : ℕ)
    (D : Fin n → X × ℝ) (f : H) : Prop :=
  ∀ g : H, lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) ≤
    lam * ‖g‖ ^ 2 + empiricalRisk n L D (toFun g)

/-- `H` (via `toFun`) is dense in `L¹(μ)` (used for Theorem 8.1's hypothesis "`H` is dense in
`L1(PX)`", restated locally as ε-approximation in the `L¹` seminorm rather than via the `Lp`
subtype): every `μ`-integrable `g` is approximated in `L¹(μ)`-distance by some `μ`-integrable
`toFun f`, `f ∈ H`. -/
def DenseInL1 {X : Type*} [MeasurableSpace X] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (μ : Measure X) : Prop :=
  ∀ g : X → ℝ, Integrable g μ → ∀ ε > 0, ∃ f : H, Integrable (toFun f) μ ∧
    ∫ x, |toFun f x - g x| ∂μ < ε

end SupportVectorMachines.Classification


