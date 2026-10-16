-- Prove2me | Definitions.Def_SubsetShrink_BIC_Model
-- name    : SubsetShrink_BIC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:57.279578+00:00
-- url     : https://prove2.me/theorems/ace5b5d0-ee72-4c73-8fd8-de0ac1eb6788
-- title:
--   §3.1 and §3.5, pp. 12–13, 20 — norms, the Gaussian noise law, the BIC-type estimators β̂^B_2, β̂^B_1 and the corrected event G'_s
-- statement:
--   This file fixes the objects of the BIC-type model-size selection of Mazumder, Radchenko and Dedieu (§3.5).
--
--   **Model.** We observe $y=f^*+\epsilon\in\mathbb R^n$, where $f^*\in\mathbb R^n$ is an unknown deterministic mean and $\epsilon$ has independent $N(0,\sigma^2)$ entries. The design $X\in\mathbb R^{n\times p}$ is deterministic and its columns have unit Euclidean norm, $\sum_i X_{ij}^2=1$ for every $j$. The law of $\epsilon$ is the product measure $\bigotimes_{i=1}^n N(0,\sigma^2)$ on $\mathbb R^n$.
--
--   **Norms.** For $v\in\mathbb R^m$: $\|v\|=\sqrt{\sum_i v_i^2}$ (Euclidean), $\|v\|_1=\sum_i|v_i|$, and $\|v\|_0$ is the number of nonzero coordinates. The inner product is $a^\top b=\sum_i a_ib_i$.
--
--   **Data-dependent penalties.** For $a,b\ge 0$ and $\beta\in\mathbb R^p$,
--   $$\lambda_\beta=a\sqrt{\|\beta\|_0\log(ep/\|\beta\|_0)},\qquad \mu_\beta=b\log(ep/\|\beta\|_0).$$
--
--   **Estimators.** $\hat\beta^{B}_2$ is any global minimizer over $\beta\in\mathbb R^p$ of
--   $$\|y-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0,$$
--   and, for a fixed $\lambda\ge0$, $\hat\beta^{B}_1$ is any global minimizer of
--   $$\|y-X\beta\|^2+\lambda\|\beta\|_1+\mu_\beta\|\beta\|_0 .$$
--   These are unconstrained problems: the model size $\|\beta\|_0$ is chosen by the penalty, not fixed in advance.
--
--   **The event $G'_s$.** For $\sigma>0$, $\delta_0\in(0,1]$ and an integer $s$,
--   $$G'_s=\Big\{\epsilon:\ \epsilon^\top Xu\le\sigma\sqrt{5s\log(ep/s)+3\log(1/\delta_0)}\,\|Xu\|\ \text{ for all } u \text{ with } \|u\|_0\le s\Big\}.$$
--   This is the event $G_s$ of §3.1 with the coefficient of $\log(1/\delta_0)$ raised from $1$ to $3$.
--
--   These objects are used by every statement of the mission: the basic inequality (51), the high-probability bounds (54)–(58), the union bound over model sizes, and Theorem 5.
--
--   **Formalization Note** Vectors are `Fin m → ℝ` with explicit norms `l2`, `l1`, `l0` (Mathlib's norm on `Fin m → ℝ` is the sup norm); `dot` is the inner product and `X.mulVec` the matrix–vector product. The estimators are argmin predicates `IsBIC2 X y a b βhat` and `IsBIC1 X y λ b βhat` ("`βhat` minimizes the objective over all of $\mathbb R^p$"); no minimizer is selected and none is assumed to exist or to be unique. The penalty $\mu_\beta\|\beta\|_0$ is always written as the product `muB b β * l0 β`, and $\lambda_\beta$ as $a\sqrt{\|\beta\|_0\cdot\log(ep/\|\beta\|_0)}$: at $\beta=0$ both are $0$, which is the paper's convention $0\cdot\infty=0$ (p. 13); Lean's `Real.log (e*p/0) = 0` gives the same value. Logarithms are natural and $e=\exp(1)$. The noise law is `noiseLaw n σ = Measure.pi (fun _ => gaussianReal 0 σ²)`. The printed $G_s$ (coefficient $1$ on $\log(1/\delta_0)$) does not satisfy Theorem 1's bound $P(G_s)\ge1-\delta_0$: for $n=p=s=1$, $X=[1]$, $P(G_s^c)=2\bar\Phi(\sqrt{5+L})>e^{-L}=\delta_0$ for $L=\log(1/\delta_0)\ge 9$. The corrected $G'_s$ is what the union bound of p. 50 needs; inside the paper's $\lesssim$ the change of constant is absorbed.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, pp. 12–13, §3.1, (15), events G_s (corrected); p. 20, §3.5, definitions of β̂^B_2, β̂^B_1, λ_β, µ_β

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- `λ_β = a √(‖β‖₀ log(ep/‖β‖₀))` (§3.5, p. 20). At `‖β‖₀ = 0` it is `0`. -/
noncomputable def lamB {p : ℕ} (a : ℝ) (β : Fin p → ℝ) : ℝ :=
  a * Real.sqrt ((SubsetShrink.Events.l0 β : ℝ) * Real.log (Real.exp 1 * p / (SubsetShrink.Events.l0 β : ℝ)))

/-- `µ_β = b log(ep/‖β‖₀)` (§3.5, p. 20). It is only used multiplied by `‖β‖₀`, so the
empty model has penalty `µ_β ‖β‖₀ = 0`. -/
noncomputable def muB {p : ℕ} (b : ℝ) (β : Fin p → ℝ) : ℝ :=
  b * Real.log (Real.exp 1 * p / (SubsetShrink.Events.l0 β : ℝ))

/-- The objective of `β̂^B_2`: `‖y − Xβ‖² + λ_β ‖β‖ + µ_β ‖β‖₀`. -/
noncomputable def obj2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (a b : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  ∑ i, (y i - X.mulVec β i) ^ 2 + lamB a β * SubsetShrink.Events.l2 β + muB b β * (SubsetShrink.Events.l0 β : ℝ)

/-- `βhat` is a (global, unconstrained) minimizer of the objective of `β̂^B_2`. -/
def IsBIC2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (a b : ℝ)
    (βhat : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, obj2 X y a b βhat ≤ obj2 X y a b β

/-- The objective of `β̂^B_1`: `‖y − Xβ‖² + λ ‖β‖₁ + µ_β ‖β‖₀`. -/
noncomputable def obj1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam b : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  ∑ i, (y i - X.mulVec β i) ^ 2 + lam * SubsetShrink.Events.l1 β + muB b β * (SubsetShrink.Events.l0 β : ℝ)

/-- `βhat` is a (global, unconstrained) minimizer of the objective of `β̂^B_1`. -/
def IsBIC1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam b : ℝ)
    (βhat : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, obj1 X y lam b βhat ≤ obj1 X y lam b β

end SubsetShrink.BIC


