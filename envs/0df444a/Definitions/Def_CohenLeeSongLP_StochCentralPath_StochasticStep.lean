-- Prove2me | Definitions.Def_CohenLeeSongLP_StochCentralPath_StochasticStep
-- name    : CohenLeeSongLP_StochCentralPath_StochasticStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:48.110338+00:00
-- url     : https://prove2.me/theorems/04f137df-bee9-4736-883a-4eb87eced60e
-- title:
--   StochasticStep (Algorithm 1): sparse sampled direction, approximate projection step, resampling loop; Assumption 4.1
-- statement:
--   This module formalizes the procedure StochasticStep (Algorithm 1, p. 3:9) and Assumption 4.1 (p. 3:9). Fix a constraint matrix $A\in\mathbb R^{d\times n}$, positive vectors $x,s\in\mathbb R^n$ (the current primal and dual slack iterates), a vector $\widetilde v\in\mathbb R^n$ (the output of the data structure, $\widetilde v=\mathrm{mp.Update}(w)$ with $w=x/s$), a direction $\delta_\mu\in\mathbb R^n$ and a sampling parameter $k>0$.
--
--   1. **Rescaled point (line 3).** $\overline x=x\sqrt{\widetilde v/w}$ and $\overline s=s\sqrt{w/\widetilde v}$, so that $\overline x/\overline s=\widetilde v$ and $\overline x\,\overline s=xs$. Write $\overline X=\mathrm{diag}(\overline x)$, $\overline S=\mathrm{diag}(\overline s)$.
--   2. **Projection (Eq. (13)).** $\overline P=\sqrt{\overline X/\overline S}\,A^\top\big(A\tfrac{\overline X}{\overline S}A^\top\big)^{-1}A\sqrt{\overline X/\overline S}$.
--   3. **Step (lines 9–11).** For a vector $\widetilde\delta_\mu$, $p_\mu=\overline P\,\tfrac{1}{\sqrt{\overline X\,\overline S}}\widetilde\delta_\mu$ (the output of mp.Query, by Theorem 5.1), $\widetilde\delta_s=\tfrac{\overline S}{\sqrt{\overline X\,\overline S}}p_\mu$ and $\widetilde\delta_x=\tfrac{1}{\overline S}\widetilde\delta_\mu-\tfrac{\overline X}{\sqrt{\overline X\,\overline S}}p_\mu$; the new duality measure is $\mu^{\mathrm{new}}=(x+\widetilde\delta_x)(s+\widetilde\delta_s)$.
--   4. **Sparse direction (lines 5–6).** With $p_i=\min\!\big(1,\,k\,(\delta_{\mu,i}^2/\sum_{l=1}^n\delta_{\mu,l}^2+1/n)\big)$, the coordinates of $\widetilde\delta_\mu$ are independent and $\widetilde\delta_{\mu,i}=\delta_{\mu,i}/p_i$ with probability $p_i$, $0$ otherwise. This product law on $\mathbb R^n$ is the law *without resampling*.
--   5. **Resampling loop (lines 4 and 12).** The loop repeats until
--   $$\|\overline s^{-1}\widetilde\delta_s\|_\infty\le\frac{1}{100\log n}\quad\text{and}\quad\|\overline x^{-1}\widetilde\delta_x\|_\infty\le\frac{1}{100\log n}.$$
--   The law of the accepted sample is the product law conditioned on this success event $G$; the procedure returns $(x+\widetilde\delta_x,\,s+\widetilde\delta_s)$.
--
--   **Assumption 4.1** (verbatim): Assume the following for the input of the procedure StochasticStep (see Algorithm 1):
--   • $xs \approx_{0.1} t$ with $t > 0$.
--   • mp.Update($w$) outputs $\widetilde{v}$ such that $w \approx_{\epsilon_{\mathrm{mp}}} \widetilde{v}$ with $\epsilon_{\mathrm{mp}} \le 1/40{,}000$.
--   • $\|\delta_\mu\|_2 \le \epsilon t$ with $0 < \epsilon < 1/(40{,}000 \log n)$.
--   • $k \ge 1{,}000\epsilon\sqrt{n}\log^2 n/\epsilon_{\mathrm{mp}}$.
--
--   The predicate `Assumption41` is this assumption with $0<\epsilon\le 1/(40000\log n)$ (non-strict), together with $x>0$, $s>0$, $\epsilon_{\mathrm{mp}}>0$ and $k>0$.
--
--   **Formalization Note** The data structure is abstracted by its only property used in §4: $\widetilde v$ is an input with $w\approx_{\epsilon_{\mathrm{mp}}}\widetilde v$, and mp.Query is replaced by its value $\overline P\,(\overline X\,\overline S)^{-1/2}\widetilde\delta_\mu$. The paper prints $\epsilon<1/(40000\log n)$ but Algorithm 2 sets $\epsilon=1/(40000\log n)$ exactly, so the non-strict form is used (it only weakens a hypothesis). The conditioned law is `ProbabilityTheory.cond`, which is the zero measure when $G$ is null; every theorem using it concludes that it is a probability measure. $\log$ is the natural logarithm and the matrix inverse is Mathlib's (nonsingular under full row rank). When $\delta_\mu=0$, Lean's $0/0=0$ gives $p_i=\min(1,k/n)$, which does not change the (identically zero) sample.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:9, Algorithm 1 and Assumption 4.1; p. 3:10, Eq. (13); p. 3:11, proof of Lemma 4.2 (p_μ via Theorem 5.1)

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace CohenLeeSongLP.StochCentralPath

variable {n d : ℕ}

/-- Line 3 of Algorithm 1: `x̄ = x √(ṽ/w)` with `w = x/s` (coordinatewise). -/
noncomputable def xbar (x s v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i * Real.sqrt (v i / (x i / s i))

/-- Line 3 of Algorithm 1: `s̄ = s √(w/ṽ)` with `w = x/s` (coordinatewise). -/
noncomputable def sbar (x s v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => s i * Real.sqrt ((x i / s i) / v i)

/-- Equation (13): `P̄ = √(X̄/S̄) Aᵀ (A (X̄/S̄) Aᵀ)⁻¹ A √(X̄/S̄)`, for diagonal `X̄ = diag(xb)`,
`S̄ = diag(sb)`. (`⁻¹` is Mathlib's matrix inverse; under full row rank and positive `xb, sb`
the matrix inverted is nonsingular.) -/
noncomputable def projBar (A : Matrix (Fin d) (Fin n) ℝ) (xb sb : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (xb i / sb i)) * A.transpose *
    (A * Matrix.diagonal (fun i => xb i / sb i) * A.transpose)⁻¹ * A *
    Matrix.diagonal (fun i => Real.sqrt (xb i / sb i))

/-- Line 9 of Algorithm 1: `p_μ = mp.Query(δ̃_μ/√(x̄ s̄))`, which by Theorem 5.1 with
`Ṽ = X̄/S̄` equals `P̄ (1/√(X̄S̄)) δ̃_μ`. -/
noncomputable def pMu (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) : Fin n → ℝ :=
  projBar A (xbar x s v) (sbar x s v) *ᵥ
    (fun i => δ i / Real.sqrt (xbar x s v i * sbar x s v i))

/-- Line 10 of Algorithm 1: `δ̃_s = (S̄/√(X̄S̄)) p_μ`. -/
noncomputable def stepS (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => sbar x s v i / Real.sqrt (xbar x s v i * sbar x s v i) * pMu A x s v δ i

/-- Line 11 of Algorithm 1: `δ̃_x = (1/S̄) δ̃_μ − (X̄/√(X̄S̄)) p_μ`. -/
noncomputable def stepX (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => δ i / sbar x s v i -
    xbar x s v i / Real.sqrt (xbar x s v i * sbar x s v i) * pMu A x s v δ i

/-- `μ^new = (x + δ̃_x)(s + δ̃_s)` (coordinatewise; Lemma 4.8). -/
noncomputable def muNew (A : Matrix (Fin d) (Fin n) ℝ) (x s v δ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (x i + stepX A x s v δ i) * (s i + stepS A x s v δ i)

/-- Line 6 of Algorithm 1: the sampling probability
`p_i = min(1, k · (δ_{μ,i}² / ∑ₗ δ_{μ,l}² + 1/n))`. -/
noncomputable def sampleProb (kSamp : ℝ) (δμ : Fin n → ℝ) (i : Fin n) : ℝ :=
  min 1 (kSamp * (δμ i ^ 2 / ∑ l, δμ l ^ 2 + 1 / (n : ℝ)))

/-- The two-point law of one coordinate of `δ̃_μ`: value `a/p` with probability `p`, value `0`
with probability `1 - p`. -/
noncomputable def coordLaw (p a : ℝ) : Measure ℝ :=
  p.toNNReal • Measure.dirac (a / p) + (1 - p).toNNReal • Measure.dirac 0

instance (p a : ℝ) : IsFiniteMeasure (coordLaw p a) := by
  unfold coordLaw; infer_instance

/-- Lines 5–6 of Algorithm 1, without resampling: the law of the sparse direction `δ̃_μ`, whose
coordinates are independent, `δ̃_{μ,i} = δ_{μ,i}/p_i` with probability `p_i` and `0` otherwise. -/
noncomputable def sampleLaw (kSamp : ℝ) (δμ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => coordLaw (sampleProb kSamp δμ i) (δμ i))

/-- Line 12 of Algorithm 1: the success event of the resampling loop,
`‖s̄⁻¹δ̃_s‖_∞ ≤ 1/(100 log n)` and `‖x̄⁻¹δ̃_x‖_∞ ≤ 1/(100 log n)`, as a set of samples `δ̃_μ`. -/
def successEvent (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {δ | ∀ i, |stepS A x s v δ i / sbar x s v i| ≤ 1 / (100 * Real.log n) ∧
            |stepX A x s v δ i / xbar x s v i| ≤ 1 / (100 * Real.log n)}

/-- The law of the sample `δ̃_μ` accepted by the resampling loop (lines 4–12 of Algorithm 1):
the product law `sampleLaw` conditioned on the success event. -/
noncomputable def stepLaw (A : Matrix (Fin d) (Fin n) ℝ) (x s v : Fin n → ℝ) (kSamp : ℝ)
    (δμ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (sampleLaw kSamp δμ)[|successEvent A x s v]

/-- Assumption 4.1 (p. 3:9) on the input of StochasticStep, with the non-strict
`ε ≤ 1/(40000 log n)` (the paper prints `<`, but Main sets `ε = 1/(40000 log n)`), and with the
positivity of the iterates `x, s` and of `ε_mp`, `k` made explicit. -/
structure Assumption41 (x s : Fin n → ℝ) (t : ℝ) (v δμ : Fin n → ℝ) (kSamp ε εmp : ℝ) :
    Prop where
  x_pos : ∀ i, 0 < x i
  s_pos : ∀ i, 0 < s i
  t_pos : 0 < t
  xs_approx : ApproxScalar 0.1 (fun i => x i * s i) t
  εmp_pos : 0 < εmp
  εmp_le : εmp ≤ 1 / 40000
  w_approx : ApproxVec εmp (fun i => x i / s i) v
  ε_pos : 0 < ε
  ε_le : ε ≤ 1 / (40000 * Real.log n)
  δμ_norm : norm2 δμ ≤ ε * t
  kSamp_pos : 0 < kSamp
  kSamp_ge : 1000 * ε * Real.sqrt n * Real.log n ^ 2 / εmp ≤ kSamp

end CohenLeeSongLP.StochCentralPath


