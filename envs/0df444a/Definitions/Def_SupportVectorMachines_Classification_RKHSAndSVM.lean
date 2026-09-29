-- Prove2me | Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM
-- name    : SupportVectorMachines_Classification_RKHSAndSVM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:02.823104+00:00
-- url     : https://prove2.me/theorems/56fd7070-2449-4bdb-851f-78930fccfce7
-- title:
--   RKHSs, restricted Bayes risk, the approximation error function, and SVM solutions
-- statement:
--   $H$ **is the RKHS of the kernel $k$** over $X$ (Steinwart & Christmann, *Support Vector
--   Machines*, Springer 2008, Definition 4.18, restated locally) if the evaluation map
--   `toFun : H → (X → ℝ)` is injective and there is a feature map $x \mapsto k_x \in H$ with
--   $\mathrm{toFun}(k_x)(x') = k(x,x')$ and $\mathrm{toFun}(f)(x) = \langle f, k_x\rangle_H$ for
--   all $f \in H$, $x, x' \in X$.
--
--   The **restricted Bayes $L$-risk on $H$** (Eq. (5.30), p. 179) is
--   $R^*_{L,P,H} := \inf_{f \in H} R_{L,P}(f)$, and the **approximation error function**
--   (Definition 5.14, p. 179) is
--   $$
--   A_2(\lambda) := \inf_{f \in H} \lambda \|f\|_H^2 + R_{L,P}(f) - R^*_{L,P,H}, \qquad \lambda \ge 0.
--   $$
--
--   For a sample $D := ((x_1,y_1),\dots,(x_n,y_n)) \in (X\times Y)^n$, the **empirical $L$-risk**
--   of $f$ is $R_{L,D}(f) := \tfrac1n \sum_{i=1}^n L(x_i,y_i,f(x_i))$ (Definition 2.2, Eq. (2.1)),
--   and the **SVM decision function** $f_{D,\lambda}$ (used throughout Chapters 5-6) is the
--   minimizer over $H$ of $g \mapsto \lambda\|g\|_H^2 + R_{L,D}(g)$.
--
--   Finally, $H$ **is dense in $L^1(P_X)$** — the hypothesis of Theorem 8.1 ensuring $A_2(\lambda)$
--   is a meaningful (vanishing as $\lambda \to 0$) quantity — means every $P_X$-integrable
--   function is approximated arbitrarily well, in $L^1(P_X)$-distance, by some $\mathrm{toFun}(f)$
--   with $f \in H$.
--
--   **Formalization Note** `restrictedBayesRisk`, `approxErrorA2`, `empiricalRisk` and
--   `IsSVMSolution` restate the corresponding pieces of this series' `04-representer` mission
--   (Chapter 5's own machinery) locally, per Hard Rule 9, specialized to the real-valued (Bochner,
--   junk-at-non-integrable) risk convention this chunk uses rather than `04-representer`'s
--   `ENNReal`-valued `populationRisk`. `DenseInL1` renders "dense in $L^1(P_X)$" directly as an
--   $\varepsilon$-approximation property in the $L^1$ seminorm, rather than via the `Lp` subtype,
--   to keep the statement self-contained.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 179, Definition 5.14 and Eq. (5.30); p. 23, Eq. (2.1); Chapter 5-6 SVM solution convention

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- `H` (with feature evaluation `toFun`) is the RKHS of the kernel `k` over `X` (Steinwart &
Christmann, *Support Vector Machines*, Springer 2008, Definition 4.18, restated locally per Hard
Rule 9): `toFun` is injective, and there is a feature map `x ↦ kAt x` reproducing both `k` and the
evaluation functionals via the inner product. The kernel is also required to be measurable
(Lemma 4.24, p. 118: `k(·,x)` measurable for every `x` is equivalent to every `f ∈ H` being
measurable) — the book's own "measurable kernel" hypothesis, stated in Lemma 4.24's own terms
rather than as the derived consequence, since every theorem that uses this RKHS notion needs
`toFun f` measurable for every `f ∈ H` (to make its `L`-risk well-defined as a genuine, not
junk-valued, Bochner integral). -/
def IsRKHSOfKernel {X : Type*} [MeasurableSpace X] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) : Prop :=
  Function.Injective toFun ∧
    (∃ kAt : X → H, (∀ x x' : X, toFun (kAt x) x' = k x x') ∧
      ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x)) ∧
    ∀ x : X, Measurable (fun x' => k x' x)

/-- The restricted Bayes `L`-risk on `H` (Eq. (5.30), p. 179): `R*_{L,P,H} := inf_{f∈H} R_{L,P}(f)`,
the smallest `L`-risk attainable by a function in `H` (identified with `toFun f : X → ℝ`). -/
noncomputable def restrictedBayesRisk {X : Type*} [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (L : Loss X)
    (P : Measure (X × ℝ)) : ℝ :=
  sInf {r : ℝ | ∃ f : H, risk L P (toFun f) = r}

/-- The approximation error function (Definition 5.14, p. 179):
`A2(λ) := inf_{f∈H} λ‖f‖²_H + R_{L,P}(f) − R*_{L,P,H}`. -/
noncomputable def approxErrorA2 {X : Type*} [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (L : Loss X)
    (P : Measure (X × ℝ)) (lam : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : H, r = lam * ‖f‖ ^ 2 + risk L P (toFun f)} -
    restrictedBayesRisk H toFun L P

/-- The empirical `L`-risk of `f` with respect to a sample `D : Fin n → X × ℝ` (Definition 2.2,
Eq. (2.1), p. 23, restated locally): `R_{L,D}(f) := (1/n) ∑ᵢ L(xᵢ,yᵢ,f(xᵢ))`. -/
noncomputable def empiricalRisk {X : Type*} (n : ℕ) (L : Loss X) (D : Fin n → X × ℝ)
    (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, L (D i).1 (D i).2 (f (D i).1)

/-- `f` is the SVM decision function `f_{D,λ}` for sample `D` (the minimizer used throughout
Chapters 5-6, restated locally): `f` minimizes `g ↦ λ‖g‖²_H + R_{L,D}(g)` over `H`. -/
def IsSVMSolution {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (L : Loss X) (lam : ℝ) (n : ℕ) (D : Fin n → X × ℝ) (f : H) : Prop :=
  ∀ g : H, lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) ≤
    lam * ‖g‖ ^ 2 + empiricalRisk n L D (toFun g)

/-- `H` (via `toFun`) is dense in `L¹(μ)` (used for Theorem 8.1's hypothesis "`H` is dense in
`L1(PX)`", restated locally as ε-approximation in the `L¹` seminorm rather than via the `Lp`
subtype): every `μ`-integrable `g` is approximated in `L¹(μ)`-distance by some `toFun f`,
`f ∈ H`. -/
def DenseInL1 {X : Type*} [MeasurableSpace X] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (toFun : H →ₗ[ℝ] (X → ℝ)) (μ : Measure X) : Prop :=
  ∀ g : X → ℝ, Integrable g μ → ∀ ε > 0, ∃ f : H, Integrable (toFun f) μ ∧
    ∫ x, |toFun f x - g x| ∂μ < ε

end SupportVectorMachines.Classification


