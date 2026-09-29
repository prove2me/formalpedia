-- Prove2me | Definitions.Def_SoarScaling
-- name    : SoarScaling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-22T18:56:44.482527+00:00
-- url     : https://prove2.me/theorems/4c7bc5ec-069d-4e44-964c-3616de8d118a
-- title:
--   Regular and polynomial regret scaling of a matching instance
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   A matching instance is the triple $(P, Q, \varphi)$, and its hindsight regret sequence is $\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) = U_\infty - U^H_n$.
--
--   **Regular scaling (Definition 1).** The instance **scales regularly with parameter $\beta > 0$** if for every $0 < \epsilon < \beta$,
--   $$\lim_{n \to \infty} n^{\beta - \epsilon}\,\bigl(U_\infty - U^H_n\bigr) = 0 \qquad\text{and}\qquad \lim_{n \to \infty} n^{\beta + \epsilon}\,\bigl(U_\infty - U^H_n\bigr) = \infty .$$
--
--   **Polynomial scaling (Definition 1).** The instance **scales polynomially with parameter $\beta$ and limit $l_0$** if it scales regularly with parameter $\beta$ and in addition
--   $$\lim_{n \to \infty} n^{\beta}\,\bigl(U_\infty - U^H_n\bigr) = l_0 .$$
--
--   **Role.** These are the hypotheses under which Corollary 2 transfers the rate of the hindsight regret to the rate of SOAR's regret. The paper notes that for uniform demand and supply on $[0,1]^d$ with $\varphi = -\|x - y\|^p$ the instance scales regularly by the results of Caracciolo et al. on the random Euclidean assignment problem.
--
--   **Formalization Note** The paper writes the first condition as $\limsup = 0$ and the second as $\liminf = \infty$; for a sequence of nonnegative terms these are the same as the limits stated, and the formalization uses limits. Powers $n^{\beta \pm \epsilon}$ are real powers of the real number $n$, with $0^{a} = 0$ for $a > 0$, so the $n = 0$ term is irrelevant to the limits. The parameter $\beta$ is required to be positive as part of regular scaling.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, Definition 1

import Mathlib
import Definitions.Def_SoarModel

/-!
# Regular and polynomial regret scaling

Chen, Kanoria, Kumar, Zhang, *Feature-Based Dynamic Matching*, Definition 1.
-/

open MeasureTheory Filter Topology

/-- A matching instance `(P, Q, φ)` scales regularly with parameter `β > 0` (Definition 1): for
every `0 < ε < β`, `n^{β-ε} (U_∞ - U^H_n) → 0` and `n^{β+ε} (U_∞ - U^H_n) → ∞`. -/
def SoarScalesRegularly {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [SigmaFinite P] [SigmaFinite Q] (φ : X → Y → ℝ) (β : ℝ) :
    Prop :=
  0 < β ∧ ∀ ε : ℝ, 0 < ε → ε < β →
    Tendsto (fun n : ℕ => (n : ℝ) ^ (β - ε) * SoarRegretH P Q φ n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (β + ε) * SoarRegretH P Q φ n) atTop atTop

/-- A matching instance scales polynomially with parameter `β` and limit `l₀` (Definition 1): it
scales regularly with parameter `β` and, in addition, `n^β (U_∞ - U^H_n) → l₀`. -/
def SoarScalesPolynomially {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [SigmaFinite P] [SigmaFinite Q] (φ : X → Y → ℝ)
    (β l₀ : ℝ) : Prop :=
  SoarScalesRegularly P Q φ β ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ β * SoarRegretH P Q φ n) atTop (𝓝 l₀)


