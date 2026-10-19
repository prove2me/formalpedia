-- Prove2me | Definitions.Def_SOSInference_Means_Model
-- name    : SOSInference_Means_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:56.744114+00:00
-- url     : https://prove2.me/theorems/a601f53e-b4ad-487a-8e3d-42127988bef9
-- title:
--   Assumptions A1)–A4) — the two-sample model, $m=\lfloor\kappa n\rfloor$, the merged sample $\mathcal Z_{n+m}$ and the random profile $R_n^W(\theta_*)$
-- statement:
--   A **model** in dimension $l$ consists of a probability space $(\Omega,\mathbb P)$, two sequences of random vectors $X_1,X_2,\dots$ and $Y_1,Y_2,\dots$ in $\mathbb R^l$, two functions $f_X,f_Y:\mathbb R^l\to\mathbb R$ and a number $\kappa$. The **standing assumptions** A1)–A4) of §4.1 are:
--
--   1. (A1, A2) $X_1,X_2,\dots,Y_1,Y_2,\dots$ are mutually independent; each $X_k$ has the law with Lebesgue density $f_X$ and each $Y_k$ the law with density $f_Y$ (densities are measurable and integrate to $1$); and $\kappa\in[0,\infty)$.
--   2. (A3) $\mathbb E\|X_1\|_2^2<\infty$ and $\mathbb E\|Y_1\|_2^2<\infty$.
--   3. (A4) $f_X(x)>0$ and $f_Y(x)>0$ for every $x$; if $l\ge 2$, $f_X$ and $f_Y$ are moreover differentiable with bounded gradients.
--
--   For each $n$ let $m=\lfloor\kappa n\rfloor$ and let the **merged sample** be $\mathcal Z_{n+m}=(X_1,\dots,X_n,Y_1,\dots,Y_m)$. With $\theta_*=\mathbb E X_1$, the **random SOS profile** is
--   $$R_n^W(\theta_*)=R^W\big(X_1,\dots,X_n;\ \mathcal Z_{n+m};\ \theta_*\big),$$
--   the SOS function of Definition 1 evaluated on the sample. The **covariance matrix** is $\mathrm{Var}(X)=\mathbb E\big[(X_1-\theta_*)(X_1-\theta_*)^{\mathsf T}\big]$, computed entrywise.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The samples are infinite sequences indexed from $0$ (Lean's $X_0$ is the paper's $X_1$), and the $n$-th profile uses the first $n$ of the $X$'s and the first $\lfloor\kappa n\rfloor$ of the $Y$'s; $m=[\kappa n]$ is read as the floor. The merged sample is the indexed family over $\{1,\dots,n\}\sqcup\{1,\dots,m\}$. "Continuous distribution" in A1)–A2) is implied by the densities. "Var(X) exists" in Theorem 1 is implied by A3). $R_n^W(\theta_*)$ is $0$ on the (asymptotically negligible) event that $\theta_*$ is outside the convex hull of the merged sample.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 14, §4.1, A1)–A4) and Z_{n+m}; p. 15, Definition 1; p. 11 (covariance)

import Mathlib
import Definitions.Def_SOSInference_Means_sos

/-!
# Sample out-of-sample inference: the sampling model A1)–A4) and the random SOS profile

Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4,
p. 14, §4.1, Assumptions A1)–A4) and the merged sample `Z_{n+m}`; p. 15, Definition 1;
p. 11 (covariance convention).
-/

namespace SOSInference.Means

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The data of the sampling model of §4.1 (p. 14) in dimension `l`: a probability space
`(Ω, P)`, the in-sample observations `X_1, X_2, …` and the out-of-sample scenarios
`Y_1, Y_2, …` (indexed from `0`), their densities `f_X`, `f_Y`, and the ratio `κ`. -/
structure Model (l : ℕ) where
  /-- the sample space -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the probability measure -/
  P : Measure Ω
  [hP : IsProbabilityMeasure P]
  /-- the in-sample observations `X_1, X_2, …` (Lean index `k` is the paper's `X_{k+1}`) -/
  X : ℕ → Ω → E l
  /-- the out-of-sample scenarios `Y_1, Y_2, …` -/
  Y : ℕ → Ω → E l
  /-- the density `f_X` of the `X_i` -/
  fX : E l → ℝ
  /-- the density `f_Y` of the `Y_j` -/
  fY : E l → ℝ
  /-- the ratio `κ` in `m = [κn]` -/
  κ : ℝ

attribute [instance] Model.mΩ Model.hP

/-- The probability measure on `ℝ^l` with Lebesgue density `f`. -/
def lawOfDensity {l : ℕ} (f : E l → ℝ) : Measure (E l) :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- The regularity of A4) for `l ≥ 2` (p. 14): `f_X`, `f_Y` are differentiable with bounded
gradients. -/
def Model.SmoothDensities {l : ℕ} (M : Model l) : Prop :=
  Differentiable ℝ M.fX ∧ Differentiable ℝ M.fY ∧
    ∃ K : ℝ, ∀ x, ‖fderiv ℝ M.fX x‖ ≤ K ∧ ‖fderiv ℝ M.fY x‖ ≤ K

/-- The standing assumptions A1)–A4) of §4.1 (p. 14).

* A1), A2): the `X_k` are i.i.d. with density `f_X`, the `Y_k` are i.i.d. with density `f_Y`, the
  two samples are independent (all of `X_1, X_2, …, Y_1, Y_2, …` are mutually independent), and
  `κ ∈ [0, ∞)`. "Continuous distribution" is implied by the densities. A density is a measurable
  function integrating to `1`.
* A3): `E‖X_1‖₂² < ∞` and `E‖Y_1‖₂² < ∞`.
* A4): `f_X`, `f_Y` positive everywhere; for `l ≥ 2` also differentiable with bounded gradients.
-/
structure Model.Standing {l : ℕ} (M : Model l) : Prop where
  kappa_nonneg : 0 ≤ M.κ
  measurable_fX : Measurable M.fX
  measurable_fY : Measurable M.fY
  lintegral_fX : ∫⁻ x, ENNReal.ofReal (M.fX x) = 1
  lintegral_fY : ∫⁻ x, ENNReal.ofReal (M.fY x) = 1
  measurable_X : ∀ k, Measurable (M.X k)
  measurable_Y : ∀ k, Measurable (M.Y k)
  law_X : ∀ k, M.P.map (M.X k) = lawOfDensity M.fX
  law_Y : ∀ k, M.P.map (M.Y k) = lawOfDensity M.fY
  indep : iIndepFun (Sum.elim M.X M.Y) M.P
  sq_integrable_X : Integrable (fun ω => ‖M.X 0 ω‖ ^ 2) M.P
  sq_integrable_Y : Integrable (fun ω => ‖M.Y 0 ω‖ ^ 2) M.P
  fX_pos : ∀ x, 0 < M.fX x
  fY_pos : ∀ x, 0 < M.fY x
  smooth : 2 ≤ l → M.SmoothDensities

/-- The number of scenarios `m = [κn]` (A2), p. 14), read as `⌊κn⌋`. -/
def mOf (κ : ℝ) (n : ℕ) : ℕ := ⌊κ * n⌋₊

/-- The merged sample `Z_{n+m} = X_n ∪ Y_m` (p. 14) as an indexed family:
`Z_k = X_k` for `k ≤ n` (left summand) and `Z_{n+j} = Y_j` for `j ≤ m` (right summand). -/
def Zfam {l : ℕ} (M : Model l) (n : ℕ) (ω : M.Ω) : Fin n ⊕ Fin (mOf M.κ n) → E l :=
  Sum.elim (fun i => M.X i ω) (fun j => M.Y j ω)

/-- The true mean `θ* = E(X)`. -/
def theta {l : ℕ} (M : Model l) : E l := ∫ ω, M.X 0 ω ∂M.P

/-- The random SOS profile function at the true mean, `R_n^W(θ*)` (Definition 1, p. 15), computed
from `X_1, …, X_n` and `Z_{n+m}` with `m = ⌊κn⌋`.

**Formalization Note.** On the event that `θ*` is outside the convex hull of `Z_{n+m}` the LP is
infeasible and the value is `0` by convention (see `sos`); the probability of this event tends
to `0` (p. 35). -/
def Rn {l : ℕ} (M : Model l) (n : ℕ) (ω : M.Ω) : ℝ :=
  sos (fun i : Fin n => M.X i ω) (Zfam M n ω) (theta M)

/-- The covariance matrix `Var(X) = E[(X − θ*)(X − θ*)ᵀ]` of `X_1`, entrywise. -/
def covX {l : ℕ} (M : Model l) : Matrix (Fin l) (Fin l) ℝ :=
  Matrix.of fun a b => ∫ ω, (M.X 0 ω a - theta M a) * (M.X 0 ω b - theta M b) ∂M.P

end

end SOSInference.Means


