-- Prove2me | Definitions.Def_FastRatesSVM_Rates_Noise
-- name    : FastRatesSVM_Rates_Noise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:05.508098+00:00
-- url     : https://prove2.me/theorems/38efaef5-793f-4ada-94c3-eaf36b930550
-- title:
--   Definitions 2.2 and 2.3 — Tsybakov and geometric noise
-- statement:
--   Write $X_{-1}=\{x\in X:\eta(x)<1/2\}$, $X_1=\{x\in X:\eta(x)>1/2\}$ and $X_0=\{x\in X:\eta(x)=1/2\}$. Equation (7) defines $\tau_x$ as the distance to $X_0\cup X_1$ on $X_{-1}$, to $X_0\cup X_{-1}$ on $X_1$, and as zero otherwise.
--
--   A distribution has **Tsybakov noise exponent** $q\in[0,\infty]$ when, for some $C>0$ and all sufficiently small $t>0$,
--   $$
--   \mu\{x\in X:|2\eta(x)-1|\le t\}\le Ct^q.
--   $$
--   For $q=\infty$, the right-hand side is zero for $t<1$. A distribution has **geometric noise exponent** $\alpha>0$ when, for some $C>0$ and every $t>0$,
--   $$
--   \int |2\eta(x)-1|e^{-\tau_x^2/t}\,d\mu(x)\le Ct^{\alpha d/2}.
--   $$
--   The explicit-constant predicate records a specified $C$ for Theorem 2.7.
--
--   These conditions separately control label ambiguity and the location of ambiguous mass. **Formalization Note** Distance to the empty set is set to zero, the convention needed for the paper's Lemma 4.1 and Theorem 2.7. The small-$t$ threshold is taken below one without changing Definition 2.2.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 6, Definition 2.2 and (5); p. 7, (7), Definition 2.3 and (8)

import Definitions.Def_FastRatesSVM_Rates_Model

open MeasureTheory

namespace FastRatesSVM.Rates

def Xminus {d : ℕ} (D : BinaryDistribution d) : Set (E d) :=
  {x | x ∈ X d ∧ D.η x < 1 / 2}

def Xplus {d : ℕ} (D : BinaryDistribution d) : Set (E d) :=
  {x | x ∈ X d ∧ 1 / 2 < D.η x}

def Xzero {d : ℕ} (D : BinaryDistribution d) : Set (E d) :=
  {x | x ∈ X d ∧ D.η x = 1 / 2}

/-- Equation (7); `Metric.infDist x ∅ = 0` pins the unspecified empty-set convention. -/
noncomputable def tau {d : ℕ} (D : BinaryDistribution d) (x : E d) : ℝ :=
  by
    classical
    exact if x ∈ Xminus D then Metric.infDist x (Xzero D ∪ Xplus D)
      else if x ∈ Xplus D then Metric.infDist x (Xzero D ∪ Xminus D)
      else 0

/-- Definition 2.2, including the paper's convention `t^∞ = 0` for `0 < t < 1`. -/
def TsybakovNoise {d : ℕ} (D : BinaryDistribution d) (q : ENNReal) : Prop :=
  ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ t₀ < 1 ∧
    ∀ t : ℝ, 0 < t → t ≤ t₀ →
      D.μ {x | x ∈ X d ∧ |2 * D.η x - 1| ≤ t} ≤
        if q = ⊤ then 0 else ENNReal.ofReal (C * t ^ q.toReal)

/-- The explicit-constant form of equation (8). -/
noncomputable def GeometricBound {d : ℕ} (D : BinaryDistribution d)
    (α C : ℝ) : Prop :=
  0 < C ∧ ∀ t : ℝ, 0 < t →
    (∫⁻ x, ENNReal.ofReal
      (|2 * D.η x - 1| * Real.exp (-(tau D x) ^ 2 / t)) ∂D.μ) ≤
      ENNReal.ofReal (C * t ^ (α * (d : ℝ) / 2))

/-- Definition 2.3 for finite positive exponent. -/
noncomputable def GeometricNoise {d : ℕ} (D : BinaryDistribution d) (α : ℝ) : Prop :=
  0 < α ∧ ∃ C : ℝ, GeometricBound D α C

end FastRatesSVM.Rates


