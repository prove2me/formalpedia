-- Prove2me | Definitions.Def_AMPLowDeg_RankOne_Model
-- name    : AMPLowDeg_RankOne_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:58:06.741923+00:00
-- url     : https://prove2.me/theorems/39a53425-84af-4d97-a9f0-0895a728a895
-- title:
--   Model (1.1), the low-degree class $\mathrm{LD}(n,D)$, $\mathrm{MMSE}_{\le D}$ (1.6), $m_2$ and $M_D$
-- statement:
--   **Signal and noise.** Let $\pi$ be a probability measure on $\mathbb R$ (the prior of $\Theta$). For $n\ge1$ the signal $\theta=(\theta_1,\dots,\theta_n)$ has i.i.d. coordinates with law $\pi$. Write $\mathcal E_n=\{(i,j):1\le i\le j\le n\}$ for the upper triangle **including the diagonal**, and $x_e(\theta)=\theta_i\theta_j$ for $e=(i,j)\in\mathcal E_n$. The noise $(W_e)_{e\in\mathcal E_n}$ consists of i.i.d. $\mathcal N(0,1)$ variables (diagonal included), independent of $\theta$. The observation is
--
--   $$
--   Y_e=\frac{\theta_i\theta_j}{\sqrt n}+W_e,\qquad e=(i,j)\in\mathcal E_n,
--   $$
--
--   the upper-triangular coordinates of $Y=n^{-1/2}\theta\theta^\top+W$ with $W=W^\top$ (model (1.1), unit diagonal variance).
--
--   **Low-degree estimators.** $\mathrm{LD}(n,D)$ is the class of maps $\hat\theta=(\hat\theta_1,\dots,\hat\theta_n)$ whose coordinates are real polynomials of total degree at most $D$ in the variables $(Y_e)_{e\in\mathcal E_n}$, with deterministic coefficients. The low-degree minimum mean-square error is
--
--   $$
--   \mathrm{MMSE}_{\le D}=\inf_{\hat\theta\in\mathrm{LD}(n,D)}\frac1n\,\mathbb E\big[\|\hat\theta(Y)-\theta\|_2^2\big].
--   $$
--
--   **Prior moments.** $m_2=\mathbb E[\Theta^2]$, $\mathbb E[\Theta]$ is the prior mean, $\|\Theta\|_p=(\mathbb E|\Theta|^p)^{1/p}$, and $M_D=\max\{1,\|\Theta\|_{4D+2}\}$. The standing assumption of the paper is that $\mathbb E|\Theta|^p<\infty$ for every $p$.
--
--   These are the objects of the main theorem and of every bound on $\mathrm{MMSE}_{\le D}$ in the paper.
--
--   **Formalization Note** Vertices are `Fin n`, so the paper's vertex $k$ is `k-1`; $\mathcal E_n$ is the subtype of pairs with first coordinate at most the second. The risk is a lower Lebesgue integral in $[0,\infty]$, so $\mathrm{MMSE}_{\le D}$ takes values in $[0,\infty]$ and no integrability convention enters. $\|\Theta\|_p$ is Mathlib's `eLpNorm`.
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, pp. 2–6: model (1.1) p. 2; standing assumptions and m₂, ‖Θ‖_p p. 3; (1.6) and LD(n,D) p. 4; M_D in Remark 1.4 p. 5; ℰₙ and x_e(θ) p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- The index set `ℰₙ = {(i, j) : 1 ≤ i ≤ j ≤ n}` of the upper triangle of an `n × n` symmetric
matrix, **including the diagonal** (p. 6). Vertices are `Fin n` (0-based: the paper's vertex `k`
is `k - 1`). -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The edge with endpoints `i, j`, stored with the smaller endpoint first. -/
def mkEdge {n : ℕ} (i j : Fin n) : Edge n :=
  if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

/-- The edge variable `x_{ij}(θ) = θᵢ θⱼ` (p. 6). -/
def edgeVar {n : ℕ} (θ : Fin n → ℝ) (e : Edge n) : ℝ := θ e.1.1 * θ e.1.2

/-- The upper-triangular observation of model (1.1): `Y_e = θᵢθⱼ/√n + W_e` for `e = (i, j) ∈ ℰₙ`. -/
noncomputable def obs {n : ℕ} (θ : Fin n → ℝ) (W : Edge n → ℝ) : Edge n → ℝ :=
  fun e => edgeVar θ e / Real.sqrt n + W e

/-- The joint law of `(θ, W)` in model (1.1): `θ₁, …, θₙ` i.i.d. `∼ π`, independent of the noise
`(W_e)_{e ∈ ℰₙ}`, whose upper-triangular entries (diagonal included) are i.i.d. `𝒩(0, 1)`. -/
noncomputable def modelLaw (π : Measure ℝ) (n : ℕ) : Measure ((Fin n → ℝ) × (Edge n → ℝ)) :=
  (Measure.pi fun _ : Fin n => π).prod (Measure.pi fun _ : Edge n => gaussianReal 0 1)

/-- The class `LD(n, D)`: maps whose `n` coordinates are real polynomials of total degree at most
`D` in the upper-triangular observations `(Y_e)_{e ∈ ℰₙ}`, with deterministic coefficients (p. 4). -/
def LD (n D : ℕ) : Set (Fin n → MvPolynomial (Edge n) ℝ) :=
  {f | ∀ i, (f i).totalDegree ≤ D}

/-- The normalized mean-square error `(1/n) E‖θ̂(Y) − θ‖₂²` of a polynomial estimator, as a lower
Lebesgue integral in `[0, ∞]` (so no integrability convention is involved). -/
noncomputable def ldRisk (π : Measure ℝ) (n : ℕ) (f : Fin n → MvPolynomial (Edge n) ℝ) : ENNReal :=
  (n : ENNReal)⁻¹ * ∫⁻ w, ENNReal.ofReal
    (∑ i, (MvPolynomial.eval (obs w.1 w.2) (f i) - w.1 i) ^ 2) ∂(modelLaw π n)

/-- The low-degree minimum mean-square error (1.6):
`MMSE_{≤D} = inf_{θ̂ ∈ LD(n, D)} (1/n) E‖θ̂(Y) − θ‖₂²`, an infimum in `[0, ∞]`. -/
noncomputable def mmseLD (π : Measure ℝ) (n D : ℕ) : ENNReal :=
  ⨅ f ∈ LD n D, ldRisk π n f

/-- The second moment `m₂ = E[Θ²]` of the prior (p. 3). -/
noncomputable def m2 (π : Measure ℝ) : ℝ := ∫ x, x ^ 2 ∂π

/-- The prior mean `E[Θ]`. -/
noncomputable def mean (π : Measure ℝ) : ℝ := ∫ x, x ∂π

/-- The standing moment assumption of p. 3: `E|Θ|^p < ∞` for every (integer) `p`. -/
def AllMomentsFinite (π : Measure ℝ) : Prop :=
  ∀ p : ℕ, Integrable (fun x : ℝ => |x| ^ p) π

/-- `M_D = max{1, ‖Θ‖_{4D+2}}` (Remark 1.4, p. 5), with `‖Θ‖_p = (E|Θ|^p)^{1/p}`. -/
noncomputable def MD (π : Measure ℝ) (D : ℕ) : ℝ :=
  max 1 (eLpNorm (fun x : ℝ => x) ((4 * D + 2 : ℕ) : ENNReal) π).toReal

end AMPLowDeg.RankOne


