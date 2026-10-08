-- Prove2me | Definitions.Def_FastRatesSVM_Rates_RKHS
-- name    : FastRatesSVM_Rates_RKHS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:57.108253+00:00
-- url     : https://prove2.me/theorems/0c527290-d6ba-4763-918b-1c8792021985
-- title:
--   Gaussian RKHS norm, empirical hinge risk, SVM, and approximation error
-- statement:
--   For $\sigma>0$, the Gaussian kernel is $k_\sigma(x,x')=\exp(-\sigma^2\|x-x'\|^2)$. Its restricted RKHS on $X$ is represented by a squared norm obtained by taking the supremum over finite normalized linear combinations of kernel sections. The norm is $+\infty$ outside the RKHS.
--
--   For a sample $T=((x_i,y_i))_{i=1}^n$, the empirical hinge risk is the average of $\max\{0,1-y_if(x_i)\}$. An SVM solution without offset minimizes
--   $$
--   \lambda\|f\|_{H_\sigma(X)}^2+R_{\ell,T}(f)
--   $$
--   among all functions with finite RKHS norm. The approximation error is
--   $$
--   a_\sigma(\lambda)=\inf_{f\in H_\sigma(X)}
--     \{\lambda\|f\|_{H_\sigma(X)}^2+R_{\ell,P}(f)\}-R_{\ell,P}.
--   $$
--
--   The concrete norm allows $\sigma$ to vary with sample size. **Formalization Note** All risks and squared norms lie in $[0,\infty]$; the subtraction in the approximation error is truncated, but its minuend is at least the unrestricted Bayes hinge risk.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 4, Gaussian kernel and (3); p. 6, (6)

import Definitions.Def_FastRatesSVM_Rates_Noise

open MeasureTheory

namespace FastRatesSVM.Rates

/-- The Gaussian RBF kernel in §2.1. -/
noncomputable def gaussian {d : ℕ} (σ : ℝ) (x y : E d) : ℝ :=
  Real.exp (-(σ ^ 2) * ‖x - y‖ ^ 2)

/-- Squared RKHS norm, via all finite normalized kernel-section combinations.
It is infinite exactly outside the RKHS restriction to `S`. -/
noncomputable def rkhsNormSq {ι : Type*} (k : ι → ι → ℝ) (S : Set ι)
    (f : ι → ℝ) : ENNReal :=
  ⨆ (m : ℕ) (x : Fin m → ι) (_hx : ∀ i, x i ∈ S) (c : Fin m → ℝ)
      (_hc : ∑ i, ∑ j, c i * c j * k (x i) (x j) ≤ 1),
    ENNReal.ofReal ((∑ i, c i * f (x i)) ^ 2)

noncomputable def gaussianNormSq {d : ℕ} (σ : ℝ) (f : E d → ℝ) : ENNReal :=
  rkhsNormSq (gaussian σ) (X d) f

/-- Equation (3), empirical hinge risk. -/
noncomputable def empiricalHingeRisk {d n : ℕ} (T : Fin n → E d × ℝ)
    (f : E d → ℝ) : ENNReal :=
  ENNReal.ofReal
    ((∑ i, max 0 (1 - (T i).2 * f (T i).1)) / (n : ℝ))

/-- Every finite-norm minimizer of the SVM objective without offset. -/
noncomputable def IsSVMSol {d n : ℕ} (σ reg : ℝ) (T : Fin n → E d × ℝ)
    (f : E d → ℝ) : Prop :=
  gaussianNormSq σ f < ⊤ ∧
    ∀ g : E d → ℝ, gaussianNormSq σ g < ⊤ →
      ENNReal.ofReal reg * gaussianNormSq σ f + empiricalHingeRisk T f ≤
        ENNReal.ofReal reg * gaussianNormSq σ g + empiricalHingeRisk T g

/-- Equation (6), with the unrestricted Bayes hinge risk as baseline. -/
noncomputable def approxError {d : ℕ} (D : BinaryDistribution d)
    (σ reg : ℝ) : ENNReal :=
  (⨅ (f : E d → ℝ) (_hf : gaussianNormSq σ f < ⊤),
    ENNReal.ofReal reg * gaussianNormSq σ f + hingeRisk D f) - bayesHingeRisk D

end FastRatesSVM.Rates


