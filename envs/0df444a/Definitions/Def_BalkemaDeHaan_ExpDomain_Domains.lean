-- Prove2me | Definitions.Def_BalkemaDeHaan_ExpDomain_Domains
-- name    : BalkemaDeHaan_ExpDomain_Domains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:21.575979+00:00
-- url     : https://prove2.me/theorems/4bf862a9-d752-4c32-9b8c-85e57b2b1453
-- title:
--   §2 — D₀, the residual-life domain D_r(G), the maxima domain D(G), and (11)
-- statement:
--   Let $F$ be the distribution function of a probability law $\mu$ with survival function $R$. The class $D_0$ consists of laws with $R(x)>0$ for every real $x$. A law belongs to the **residual-life domain of attraction** $D_r(G)$ if it belongs to $D_0$ and there are functions $a(t)>0$ and $b(t)$ for which
--
--   $$F_t\bigl(b(t)+xa(t)\bigr)\longrightarrow G(x)$$
--
--   weakly as $t\to\infty$. It belongs to the **maxima domain of attraction** $D(G)$ if there are sequences $a_n>0$ and $b_n$ such that
--
--   $$F(a_nx+b_n)^n\longrightarrow G(x)$$
--
--   weakly as $n\to\infty$. Equation (11) is represented separately as $nR(b_n+xa_n)\to e^{-x}$ on a specified set of $x$ values.
--
--   **Formalization Note** In $D_r$, $b(t)$ shifts the residual lifetime $X-t$; in (11), $b_n$ shifts the original lifetime $X$. The two uses of $b$ are local to their own statements. The positivity condition $D_0$ is built into $D_r$ because it keeps the conditional distribution defined. It is not built into $D(G)$; bounded-support laws can belong to a maxima domain.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 798 (PDF 7), §2 definitions; p. 799 (PDF 8), (11)

import Definitions.Def_BalkemaDeHaan_ExpDomain_Distribution
import Definitions.Def_BalkemaDeHaan_ExpDomain_Laws

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- The paper's `D₀`: lifetime laws with no finite upper endpoint. -/
def InDZero (μ : Measure ℝ) : Prop :=
  ∀ x : ℝ, 0 < μ (Set.Ioi x)

/-- The domain `D_r(G)` using §2's shift of the residual lifetime `X - t`. -/
def InDr (μ : Measure ℝ) (G : ℝ → ℝ) : Prop :=
  InDZero μ ∧ ∃ a b : ℝ → ℝ, (∀ t : ℝ, 0 < a t) ∧
    WeakConvergenceReal (fun t x => BalkemaDeHaan.LimitTypes.residualCDF μ t (b t + x * a t)) G

/-- The extreme-value domain `D(G)` of normalized sample maxima. -/
def InD (μ : Measure ℝ) (G : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, (∀ n : ℕ, 0 < a n) ∧
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) G

/-- Equation (11), on a specified range of abscissas. -/
def TailScaledConvergence (μ : Measure ℝ) (a b : ℕ → ℝ) (U : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∈ U →
    Tendsto (fun n : ℕ => (n : ℝ) * BalkemaDeHaan.LimitTypes.tail μ (b n + x * a n)) atTop (nhds (Real.exp (-x)))

end BalkemaDeHaan.ExpDomain


