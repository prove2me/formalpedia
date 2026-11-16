-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness
-- name    : QMatVecLB_ConvexOpt_Supplement_Witness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:21:03.730756+00:00
-- url     : https://prove2.me/theorems/b60d85b8-b8e2-4830-aadf-48815a40ba77
-- title:
--   Determinantal witnesses, product functions, mollifiers and decision functions of §§3.2, 4, 5.2
-- statement:
--   This file adds the objects of Sections 3.2, 4 and 5.2 that the published base definitions do not provide. Throughout, $\partial_{X_{ij}}$ is the coordinate derivative on $\mathbb R^{n\times n}$ and $c=-\frac{1}{2\pi i}$.
--
--   1. **Determinantal witness** (Eq. (23)). For $b:\mathbb R^{n\times n}\to\mathbb R$,
--   $$\beta=\det\!\Big(-\tfrac{1}{2\pi i}\partial_X\Big)b=c^n\sum_{\sigma\in S_n}\operatorname{sgn}(\sigma)\prod_{i=1}^n\partial_{X_{i\sigma(i)}}b .$$
--   2. **Minor witnesses** (Eq. (24)). For row and column lists $I,J$ of length $r$, $\beta_{I,J}=\det\big((-\frac{1}{2\pi i}\partial_X)_{I,J}\big)b$.
--   3. **Product function** (Eq. (25)). $b(A)=\prod_i b_{\mathrm d}(A_{ii})\prod_{i\ne j}b_{\mathrm{od}}(A_{ij})$.
--   4. **Convolution powers.** $(f*g)(\tau)=\int_{\mathbb R}f(a)g(\tau-a)\,da$, and $f^{*1}=f$, $f^{*(m+1)}=f^{*m}*f$.
--   5. **Mollifier.** A smooth, even, nonnegative $g:\mathbb R\to\mathbb R$ with $\|g\|_1=1$ vanishing outside $[-\delta,\delta]$.
--   6. **The choices of §4.** $b_{\mathrm d}=\mathbf 1_{[0,1]}*g_\delta$; $w=16n^{3/2}$; $b_{\mathrm{od}}=\frac1w\mathbf 1_{[0,w]}*g_{w/2}$; $\theta=(n-1)/2$; $D(A)=\mathbf 1_{\operatorname{tr}A\ge\theta}$; the promise
--   $$\mathcal P=\{A:\ |\theta-\operatorname{tr}A|\ge\tfrac13,\ \|A\|_{\max}\le24n^{3/2}\};$$
--   the identity term $\beta_{\mathrm{id}}(A)=c^n\prod_i b_{\mathrm d}'(A_{ii})\prod_{i\ne j}b_{\mathrm{od}}(A_{ij})$ and the remainder $\beta_{\overline{\mathrm{id}}}=\beta-\beta_{\mathrm{id}}$.
--   7. **§5.2 decision function.** $D_\theta(A)=\mathbf 1_{(\det A)^2\ge\theta}$.
--
--   These objects let the lemmas of Sections 3.2, 4 and 5.2 be stated exactly as on the page.
--
--   **Formalization Note** The differential operators reuse the published `minorCayley` (with coefficient $c$) from the base mission's calculus file, and the convolution is Mathlib's `MeasureTheory.convolution` against Lebesgue measure. A mollifier's support condition is written as `Function.support g ⊆ [−δ, δ]`, which is equivalent to closed support in $[-\delta,\delta]$ because the interval is closed.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Eqs. (23)–(25), Section 4 set-up and Eq. (56) context, D_θ of Lemma 5.5, PDF p. 8 (printed p. 7); also PDF pp. 9–10, 14.

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Calculus

noncomputable section

namespace QMatVecLB.ConvexOpt.Supplement
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

/-- The coefficient `−1/(2πi)` of Eqs. (23)–(24). -/
def witnessCoeff : ℂ := -(1 / (2 * Real.pi * Complex.I))

/-- Eq. (23): the determinantal witness `β = det(−(1/2πi)∂_X) b`, written as the full
`n × n` minor of the differential operator (identity rows and columns). -/
def detWitness {n : ℕ} (b : RMat n → ℝ) : RMat n → ℂ :=
  minorCayley (n := n) (r := n) id id witnessCoeff (fun X => (b X : ℂ))

/-- Eq. (24): `β_{I,J} = det((−(1/2πi)∂_X)_{I,J}) b`, for rows and columns listed by
`rows cols : Fin r → Fin n` (for subsets `I, J`, their increasing enumerations). -/
def minorWitness {n r : ℕ} (rows cols : Fin r → Fin n) (b : RMat n → ℝ) : RMat n → ℂ :=
  minorCayley rows cols witnessCoeff (fun X => (b X : ℂ))

/-- Eq. (25): `b(A) = ∏_i b_d(A_ii) ∏_{i≠j} b_od(A_ij)`. -/
def productB {n : ℕ} (bd bod : ℝ → ℝ) (A : RMat n) : ℝ :=
  ∏ i, ∏ j, if i = j then bd (A i j) else bod (A i j)

/-- Convolution on `ℝ`, `(f ∗ g)(τ) = ∫ f(a) g(τ − a) da`. -/
def conv (f g : ℝ → ℝ) : ℝ → ℝ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- Iterated convolution: `convPow f m = f^{∗(m+1)}` (so `convPow f 0 = f`). -/
def convPow (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | m + 1 => conv (convPow f m) f

/-- A smooth, even, nonnegative mollifier with `‖g‖₁ = 1`, supported on `[−δ, δ]` (§4). -/
def IsMollifier (g : ℝ → ℝ) (δ : ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, g (-x) = g x) ∧ (∀ x, 0 ≤ g x) ∧
    (∫ x, |g x|) = 1 ∧ Function.support g ⊆ Set.Icc (-δ) δ

/-- §4: `b_d = 1_{[0,1]} ∗ g_δ`. -/
def bDiag (gδ : ℝ → ℝ) : ℝ → ℝ :=
  conv (Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => 1)) gδ

/-- §4: `w = 16 n^{3/2}`. -/
def offWidth (n : ℕ) : ℝ := 16 * (n : ℝ) ^ ((3 : ℝ) / 2)

/-- §4: `b_od = (1/w) 1_{[0,w]} ∗ g_{w/2}`. -/
def bOff (n : ℕ) (gw : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 / offWidth n) *
    conv (Set.indicator (Set.Icc (0 : ℝ) (offWidth n)) (fun _ => 1)) gw x

/-- §4: `θ = (n − 1)/2`. -/
def traceTheta (n : ℕ) : ℝ := ((n : ℝ) - 1) / 2

/-- §4: `D(A) = 1_{tr A ≥ θ}`. -/
def traceDecision {n : ℕ} (θ : ℝ) (A : RMat n) : ℝ :=
  Set.indicator {A : RMat n | θ ≤ A.trace} (fun _ => 1) A

/-- §4: `P = {A : |θ − tr A| ≥ 1/3, ‖A‖_max ≤ 24 n^{3/2}}`, with `θ = (n−1)/2`. -/
def tracePromise (n : ℕ) : Set (RMat n) :=
  {A | (1 / 3 : ℝ) ≤ |traceTheta n - A.trace| ∧ maxNorm A ≤ 24 * (n : ℝ) ^ ((3 : ℝ) / 2)}

/-- §4: `β_id(A) = (−1/(2πi))^n ∏_i b_d′(A_ii) ∏_{i≠j} b_od(A_ij)`, the `σ = id` term of `β`. -/
def betaId {n : ℕ} (bd bod : ℝ → ℝ) (A : RMat n) : ℂ :=
  witnessCoeff ^ n * ((∏ i, ∏ j, if i = j then deriv bd (A i j) else bod (A i j) : ℝ) : ℂ)

/-- §4: `β̄_id = β − β_id`, with `β` built from `b` of Eq. (25). -/
def betaBar {n : ℕ} (bd bod : ℝ → ℝ) (A : RMat n) : ℂ :=
  detWitness (productB bd bod) A - betaId bd bod A

/-- §5.2: `D_θ(A) = 1_{(det A)² ≥ θ}`. -/
def detSqDecision {n : ℕ} (θ : ℝ) (A : RMat n) : ℝ :=
  Set.indicator {A : RMat n | θ ≤ A.det ^ 2} (fun _ => 1) A

end QMatVecLB.ConvexOpt.Supplement
end


