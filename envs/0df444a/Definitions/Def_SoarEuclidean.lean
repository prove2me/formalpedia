-- Prove2me | Definitions.Def_SoarEuclidean
-- name    : SoarEuclidean
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-22T18:57:37.826668+00:00
-- url     : https://prove2.me/theorems/e86deb06-97bf-487c-b9dd-e29f1df3a0f4
-- title:
--   Euclidean matching instances: quality functions, distributions, curvature condition, and the regret rates
-- statement:
--   This module fixes the concrete matching instances of Sections 3.1 and 4 and the regret rates the paper proves for them.
--
--   **Quality functions.** On $\mathbb R^d$ with the Euclidean norm, for $p \ge 1$,
--   $$\varphi_p(x, y) = -\|x - y\|^p, \qquad \varphi_{\mathrm{dot}}(x, y) = \langle x, y \rangle,$$
--   and on the real line (Proposition 1) $\varphi(x, y) = -|x - y|^p$.
--
--   **Distributions.** A distribution is **supported on a bounded set** if some bounded set carries all its mass. The **unit cube** is $[0,1]^d = \{x : 0 \le x_i \le 1 \ \forall i\}$ and $\mathrm{Uniform}([0,1]^d)$ is Lebesgue measure restricted to it, a probability measure. A distribution $P$ **has a density on a set $s$ bounded by $\gamma \ge 1$** if $P$ is absolutely continuous with a density $f$ that vanishes outside $s$ and satisfies $\gamma^{-1} \le f \le \gamma$ on $s$ (the density assumptions of Proposition 1, with $s = [0,1]$, and of Theorem 3, with $s = [0,1]^d$).
--
--   **Assumption 1 (curvature condition).** The Brenier potential from $P$ to $Q$ is a convex function $\psi_0$ whose gradient is the optimal transport map from $P$ to $Q$ for the quadratic cost, $\nabla\psi_0 \# P = Q$. The condition says that $\psi_0 \in C^2([0,1]^d)$ and, for some $\lambda \ge 1$,
--   $$\lambda^{-1} I \preceq \nabla^2 \psi_0(x) \preceq \lambda I \qquad \text{for all } x \in [0,1]^d,$$
--   i.e. $\lambda^{-1}\|v\|^2 \le v^\top \nabla^2\psi_0(x)\, v \le \lambda \|v\|^2$ for every direction $v$.
--
--   **Rate functions.** The paper's rate tables are recorded as functions of $n$. For Theorem 2 with quality $\varphi_p$:
--   $$r^{\uparrow}_{d,p}(n) = \begin{cases} n^{-1/2}, & d < 2(p \wedge 2),\\ n^{-1/2}\log n, & d = 2(p \wedge 2),\\ n^{-(p \wedge 2)/d}, & d > 2(p \wedge 2), \end{cases} \qquad r^{\downarrow}_{d,p}(n) = \begin{cases} n^{-1/2}, & d \le 2(p \wedge 2),\\ n^{-(p \wedge 2)/d}, & d > 2(p \wedge 2). \end{cases}$$
--   For Proposition 2 ($P = Q = \mathrm{Uniform}([0,1]^d)$), the upper rate is
--   $$u_{d,p}(n) = \begin{cases} n^{-(\frac p2 \wedge 1)} \ (p \ne 2), \quad n^{-1}\log n \ (p = 2), & d = 1,\\ (n^{-1}\log n)^{p/2} \ (p < 2), \quad n^{-1}(\log n)^2 \ (p = 2), \quad n^{-1} \ (p > 2), & d = 2,\\ n^{-(\frac pd \wedge 1)} \ (p \ne d), \quad n^{-1}\log n \ (p = d), & d \ge 3, \end{cases}$$
--   and the lower rate $\ell_{d,p}(n)$ is the same table except that the $p = 2$ entry in dimension $1$ is $n^{-1}$ and the $p = 2$ entry in dimension $2$ is $n^{-1}\log n$. For Theorem 3 (dot product under the curvature condition),
--   $$\kappa_d(n) = n^{-1}\log n \ (d = 1), \qquad n^{-1}(\log n)^3 \ (d = 2), \qquad n^{-2/d} \ (d \ge 3).$$
--
--   **Role.** These are the objects of Proposition 1, Theorem 2, Proposition 2, Corollary 3 and Theorem 3; the rate functions let those theorems be stated as $\mathrm{Reg}_n \le C\, r(n)$ and $\mathrm{Reg}_n \ge c\, r(n)$ with the paper's exact case distinctions.
--
--   **Formalization Note** Powers are real powers of the real number $n$ and $\log$ is the natural logarithm; at $n = 1$ every rate containing $\log n$ is $0$, which is why the theorems using them start at $n \ge 2$. The uniform distribution's total mass $1$ is proved, not assumed. Assumption 1 is encoded existentially: some $\psi$ that is $C^2$ on all of $\mathbb R^d$, convex on the cube, has Hessian bounds on the cube and pushes $P$ to $Q$ by its gradient; by Brenier's theorem such a $\psi$ is the Brenier potential (up to a constant) whenever $P$ is absolutely continuous, and a function that is $C^2$ on the closed cube extends to a $C^2$ function on $\mathbb R^d$, so nothing is gained or lost by the global smoothness. The density predicate does not itself assert total mass $1$; the theorems require $P$ and $Q$ to be probability measures separately, as the paper's word "distribution" does. Bounded support is $\exists$ bounded $s$ with $P(s^c) = 0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.1 (Proposition 1's instance), Section 4 (the quality functions $\varphi_p$ and $\langle x, y\rangle$, bounded supports, $\mathrm{Uniform}([0,1]^d)$, Assumption 1) and the rate tables of Theorem 2, Proposition 2 and Theorem 3

import Mathlib

/-!
# The Euclidean matching instances of Section 4

Chen, Kanoria, Kumar, Zhang, *Feature-Based Dynamic Matching*, Sections 3.1 and 4.

Demand and supply live in `ℝ^d` with the Euclidean norm; the quality functions are
`φ_p(x, y) = -‖x - y‖^p` and the dot product `⟨x, y⟩`; the distributions are either supported on
bounded sets, or have densities bounded above and below on the unit cube, or are uniform on the
unit cube.  The regret rates of Theorem 2, Proposition 2 and Theorem 3 are recorded as explicit
functions of `n`.
-/

open MeasureTheory
open scoped BigOperators

/-- The quality function `φ_p(x, y) = -‖x - y‖^p` on `ℝ^d` (Section 4). -/
noncomputable def SoarLpQuality (d : ℕ) (p : ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x y => -(‖x - y‖ ^ p)

/-- The dot-product quality function `φ_dot(x, y) = ⟨x, y⟩` on `ℝ^d` (Section 4.2). -/
noncomputable def SoarDotQuality (d : ℕ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x y => inner ℝ x y

/-- The quality function `φ(x, y) = -|x - y|^p` on the real line (Proposition 1). -/
noncomputable def SoarAbsQuality (p : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => -(|x - y| ^ p)

/-- A distribution is supported on a bounded set. -/
def SoarBoundedSupport {E : Type*} [MeasurableSpace E] [Bornology E] (P : Measure E) : Prop :=
  ∃ s : Set E, Bornology.IsBounded s ∧ P sᶜ = 0

/-- The unit cube `[0, 1]^d` in `ℝ^d`. -/
def SoarCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- The uniform distribution `Uniform([0, 1]^d)`: Lebesgue measure restricted to the unit cube. -/
noncomputable def SoarUniformCube (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.restrict (SoarCube d)

/-- The unit cube is the image of the product of unit intervals under the coordinate map. -/
lemma SoarCube_eq_preimage (d : ℕ) :
    (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1) = SoarCube d := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc, SoarCube, Set.mem_ofPred_eq]

lemma SoarCube_measurableSet (d : ℕ) : MeasurableSet (SoarCube d) := by
  rw [← SoarCube_eq_preimage]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

instance (d : ℕ) : IsProbabilityMeasure (SoarUniformCube d) := by
  constructor
  unfold SoarUniformCube
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, ← SoarCube_eq_preimage,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet,
    volume_pi_pi]
  simp [Real.volume_Icc]

/-- `P` is absolutely continuous with a density `f` supported on `s` and bounded there between
`γ⁻¹` and `γ` (the density assumptions of Proposition 1 and Theorem 3). -/
def SoarHasDensityOn {E : Type*} [MeasureSpace E] (s : Set E)
    (P : Measure E) (γ : ℝ) : Prop :=
  1 ≤ γ ∧ ∃ f : E → ℝ, Measurable f ∧ P = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (∀ x ∈ s, γ⁻¹ ≤ f x ∧ f x ≤ γ) ∧ (∀ x ∉ s, f x = 0)

/-- Assumption 1 (curvature condition): the Brenier potential from `P` to `Q` — a convex
function `ψ₀` whose gradient pushes `P` forward to `Q` — is twice continuously differentiable on
the unit cube with Hessian between `λ⁻¹ I` and `λ I` there, for some `λ ≥ 1`. -/
def SoarCurvatureCondition (d : ℕ) (P Q : Measure (EuclideanSpace ℝ (Fin d))) (lam : ℝ) :
    Prop :=
  1 ≤ lam ∧ ∃ ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 ψ ∧ ConvexOn ℝ (SoarCube d) ψ ∧
    (∀ x ∈ SoarCube d, ∀ v : EuclideanSpace ℝ (Fin d),
      lam⁻¹ * ‖v‖ ^ 2 ≤ iteratedFDeriv ℝ 2 ψ x ![v, v] ∧
        iteratedFDeriv ℝ 2 ψ x ![v, v] ≤ lam * ‖v‖ ^ 2) ∧
    Measure.map (fun x => gradient ψ x) P = Q

/-- The upper-bound rate of Theorem 2 for `φ_p` in dimension `d`: `n^{-1/2}` if `d < 2(p ∧ 2)`,
`n^{-1/2} log n` if `d = 2(p ∧ 2)`, and `n^{-(p ∧ 2)/d}` if `d > 2(p ∧ 2)`. -/
noncomputable def SoarRateLp (d : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  if (d : ℝ) < 2 * min p 2 then (n : ℝ) ^ (-(1 / 2 : ℝ))
  else if (d : ℝ) = 2 * min p 2 then (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n
  else (n : ℝ) ^ (-(min p 2) / d)

/-- The lower-bound rate of Theorem 2: `n^{-1/2}` if `d ≤ 2(p ∧ 2)` and `n^{-(p ∧ 2)/d}` if
`d > 2(p ∧ 2)`. -/
noncomputable def SoarRateLpLower (d : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  if (d : ℝ) ≤ 2 * min p 2 then (n : ℝ) ^ (-(1 / 2 : ℝ))
  else (n : ℝ) ^ (-(min p 2) / d)

/-- The upper-bound rate of Proposition 2 (`P = Q = Uniform([0,1]^d)`, quality `φ_p`). -/
noncomputable def SoarRateUniform (d : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  if d = 1 then (if p = 2 then Real.log n / n else (n : ℝ) ^ (-(min (p / 2) 1)))
  else if d = 2 then
    (if p < 2 then (Real.log n / n) ^ (p / 2)
     else if p = 2 then (Real.log n) ^ 2 / n else (n : ℝ)⁻¹)
  else (if p = d then Real.log n / n else (n : ℝ) ^ (-(min (p / d) 1)))

/-- The lower-bound rate of Proposition 2. -/
noncomputable def SoarRateUniformLower (d : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  if d = 1 then (if p = 2 then (n : ℝ)⁻¹ else (n : ℝ) ^ (-(min (p / 2) 1)))
  else if d = 2 then
    (if p < 2 then (Real.log n / n) ^ (p / 2)
     else if p = 2 then Real.log n / n else (n : ℝ)⁻¹)
  else (if p = d then Real.log n / n else (n : ℝ) ^ (-(min (p / d) 1)))

/-- The rate of Theorem 3 (dot-product quality under the curvature condition): `n^{-1} log n`
in dimension `1`, `n^{-1} (log n)^3` in dimension `2`, `n^{-2/d}` in dimension `d ≥ 3`. -/
noncomputable def SoarRateCurvature (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then Real.log n / n
  else if d = 2 then (Real.log n) ^ 3 / n
  else (n : ℝ) ^ (-(2 / d : ℝ))


