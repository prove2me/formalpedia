-- Prove2me | Definitions.Def_HighDimCLT_MultBoot_Setting
-- name    : HighDimCLT_MultBoot_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:01.479552+00:00
-- url     : https://prove2.me/theorems/8c7a2a79-b8ee-48ac-9ab5-3707e2e7af00
-- title:
--   §1–§4.1, pp. 2309–2318 — S^Y_n, E[X_iX_i′], (M.1), hyperrectangles (4), F_β, Σ̂, Σ, Δ_{n,r}, the bootstrap law of S^{eX}_n, A^m and A^{m,ϵ}
-- statement:
--   This module fixes the standing setting and the objects of the multiplier bootstrap theorem of Chernozhukov, Chetverikov and Kato (2017).
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $n,p\in\mathbb N$. Let $X_1,\dots,X_n$ be random vectors in $\mathbb R^p$ with coordinates $X_{ij}$, and $Y_1,\dots,Y_n$ further random vectors in $\mathbb R^p$.
--
--   1. **Covariance.** For a random vector $Z$, $\mathrm{cov}(Z)$ is the $p\times p$ matrix with entries $\mathrm E[Z_jZ_k]$; for centred $X_i$ this is $\mathrm E[X_iX_i']$.
--   2. **Normalized sums.** $S_n^X=n^{-1/2}\sum_{i=1}^n X_i$ and $S_n^Y=n^{-1/2}\sum_{i=1}^n Y_i$.
--   3. **Standing setting** (§1): the $X_i$ are measurable, independent, centred ($\mathrm E[X_{ij}]=0$) with $\mathrm E[X_{ij}^2]<\infty$; the $Y_i$ are measurable, independent, and $Y_i\sim N(0,\mathrm E[X_iX_i'])$.
--   4. **Condition (M.1)** with constant $b$: $n^{-1}\sum_{i=1}^n\mathrm E[X_{ij}^2]\ge b$ for all $j=1,\dots,p$.
--   5. **Hyperrectangles** (4): $\{w\in\mathbb R^p: a_j\le w_j\le b_j\ \text{for all } j\}$ with $-\infty\le a_j\le b_j\le\infty$.
--   6. **Smooth max** (App. B): for $\beta>0$ and $y\in\mathbb R^p$,
--   $$F_\beta(w)=\beta^{-1}\log\Big(\sum_{j=1}^p e^{\beta(w_j-y_j)}\Big).$$
--   7. **Bilinear form** $v_1'Mv_2=\sum_{j,k}v_{1j}M_{jk}v_{2k}$.
--   8. **Data quantities** (§4.1), for one realization $x=(x_1,\dots,x_n)$ of the data: $\bar X=n^{-1}\sum_i x_i$, $\widehat\Sigma=n^{-1}\sum_i(x_i-\bar X)(x_i-\bar X)'$, together with $\Sigma=n^{-1}\sum_i\mathrm E[X_iX_i']$ and
--   $$\Delta_{n,r}=\max_{1\le j,k\le p}|\widehat\Sigma_{jk}-\Sigma_{jk}|.$$
--   9. **Bootstrap law.** With $e_1,\dots,e_n$ i.i.d. $N(0,1)$, the law of $S_n^{eX}=n^{-1/2}\sum_i e_i(x_i-\bar X)$ for the fixed data $x$; this is the conditional law of $S^{eX}_n$ given $X_1^n=x$, so $P(S^{eX}_n\in A\mid X_1^n)$ is the mass it gives to $A$.
--   10. **Polyhedra** (§3.1): for a finite set $V$ of vectors and thresholds $s(v)$, $A^m=\bigcap_{v\in V}\{w:w'v\le s(v)\}$ and its enlargement $A^{m,\epsilon}=\bigcap_{v\in V}\{w:w'v\le s(v)+\epsilon\}$.
--
--   These are the objects of Theorem 4.1, Remark 4.1 and the displays of its proof.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin p)`, so that $N(0,\Sigma)$ is Mathlib's `multivariateGaussian 0 Σ`; because each $X_{ij}$ is square integrable, $\mathrm E[X_iX_i']$ is positive semidefinite and this is the genuine Gaussian law. Hyperrectangle endpoints are extended reals, used only in comparisons. The finite maximum $\Delta_{n,r}$ is a supremum over a finite index set. The bootstrap probability is taken per realization of the data: e is independent of the data, so this measure is a version of the conditional law. The restrictions $n\ge4$, $p\ge3$ of §1 are stated in each theorem.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), pp. 2309–2318: §1 (p. 2309), §1.1 (p. 2312), §2 (4) and (M.1) (pp. 2312, 2314), §3.1 (p. 2315), §4.1 (p. 2318); App. B (p. 2325); App. E.2 (p. 2342)

import Mathlib

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- The covariance matrix `E[Z Z′]` of a random vector `Z : Ω → ℝ^p`, entry `(j, k)` being
`∫ Z_j Z_k dP` (Chernozhukov–Chetverikov–Kato 2017, §1, p. 2309: `Y_i ∼ N(0, E[X_i X_i′])`). -/
noncomputable def covMat {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => ∫ ω, Z ω j * Z ω k ∂P

/-- The normalized sum `S_n = n^{-1/2} ∑_{i=1}^n Z_i` (§1, p. 2309). -/
noncomputable def normSum {Ω : Type u} {n p : ℕ} (Z : Fin n → Ω → EuclideanSpace ℝ (Fin p))
    (ω : Ω) : EuclideanSpace ℝ (Fin p) :=
  (Real.sqrt n)⁻¹ • ∑ i, Z i ω

/-- The standing setting of §1 (pp. 2309, 2312): `X₁, …, X_n` are independent, centred random
vectors in `ℝ^p` with finite second moments, and `Y₁, …, Y_n` are independent with
`Y_i ∼ N(0, E[X_i X_i′])`. (The restrictions `n ≥ 4`, `p ≥ 3` are stated separately.) -/
structure Standing {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)) : Prop where
  measurable_X : ∀ i, Measurable (X i)
  indep_X : iIndepFun X P
  centred_X : ∀ i j, ∫ ω, X i ω j ∂P = 0
  memLp_X : ∀ i j, MemLp (fun ω => X i ω j) 2 P
  measurable_Y : ∀ i, Measurable (Y i)
  indep_Y : iIndepFun Y P
  law_Y : ∀ i, P.map (Y i) = multivariateGaussian 0 (covMat P (X i))

/-- Condition (M.1) (§2, p. 2314): `n^{-1} ∑_{i=1}^n E[X_ij²] ≥ b` for all `j = 1, …, p`. -/
def VarFloor {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin p)) (b : ℝ) : Prop :=
  ∀ j, b ≤ (∑ i, ∫ ω, X i ω j ^ 2 ∂P) / n

/-- The hyperrectangle (4) (§2, p. 2312) `{w ∈ ℝ^p : lo_j ≤ w_j ≤ hi_j for all j}` with
endpoints in `[-∞, ∞]`. -/
def hyperrect {p : ℕ} (lo hi : Fin p → EReal) : Set (EuclideanSpace ℝ (Fin p)) :=
  {w | ∀ j, lo j ≤ ((w j : ℝ) : EReal) ∧ ((w j : ℝ) : EReal) ≤ hi j}

/-- The smooth max (App. B, p. 2325; App. E.2, p. 2342):
`F_β(w) = β^{-1} log(∑_{j=1}^p exp(β(w_j − y_j)))`. -/
noncomputable def Fβ {p : ℕ} (β : ℝ) (y w : EuclideanSpace ℝ (Fin p)) : ℝ :=
  β⁻¹ * Real.log (∑ j, Real.exp (β * (w j - y j)))

/-- The bilinear form `v₁′ M v₂ = ∑_{j,k} v₁_j M_{jk} v₂_k`. -/
def quadForm {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (v₁ v₂ : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ j, ∑ k, v₁ j * M j k * v₂ k

/-- The sample mean `X̄ = 𝔼_n[x_i] = n^{-1} ∑_i x_i` of one realization `x` of the data
(§4.1, p. 2318). -/
noncomputable def xbar {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- `Σ̂ = n^{-1} ∑_i (x_i − X̄)(x_i − X̄)′` for one realization `x` of the data (§4.1, p. 2318). -/
noncomputable def SigmaHat {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (∑ i, (x i j - xbar x j) * (x i k - xbar x k)) / n

/-- `Σ = n^{-1} ∑_i E[X_i X_i′]` (§4.1, p. 2318). -/
noncomputable def Sigma {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {n p : ℕ}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (∑ i, covMat P (X i) j k) / n

/-- `Δ_{n,r} = max_{1 ≤ j,k ≤ p} |Σ̂_jk − Σ_jk|` (Remark 4.1, p. 2319; App. E.2, p. 2342), with
`Σ̂` computed from the realization `x` (a finite maximum). -/
noncomputable def DeltaR {Ω : Type u} [MeasurableSpace Ω] {n p : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (P : Measure Ω)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin p)) : ℝ :=
  ⨆ (j : Fin p) (k : Fin p), |SigmaHat x j k - Sigma P X j k|

/-- The law of the multiplier-bootstrap sum `S^{eX}_n = n^{-1/2} ∑_i e_i (x_i − X̄)` when the data
are fixed at the realization `x` and `e₁, …, e_n` are i.i.d. `N(0, 1)` (§4.1, p. 2318); this is
the conditional law of `S^{eX}_n` given `X₁ⁿ = x`. -/
noncomputable def mbLaw {n p : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Measure (EuclideanSpace ℝ (Fin p)) :=
  (Measure.pi fun _ : Fin n => gaussianReal 0 1).map
    (fun e => (Real.sqrt n)⁻¹ • ∑ i, e i • (x i - xbar x))

/-- The intersection of half-spaces `⋂_{v ∈ V} {w : w′v ≤ s(v)}` (§3.1, p. 2315: `A^m`). -/
def polyhedron {p : ℕ} (V : Finset (EuclideanSpace ℝ (Fin p)))
    (s : EuclideanSpace ℝ (Fin p) → ℝ) : Set (EuclideanSpace ℝ (Fin p)) :=
  {w | ∀ v ∈ V, inner ℝ w v ≤ s v}

/-- The enlargement `⋂_{v ∈ V} {w : w′v ≤ s(v) + ε}` (§3.1, p. 2315: `A^{m,ε}`). -/
def enlarge {p : ℕ} (V : Finset (EuclideanSpace ℝ (Fin p)))
    (s : EuclideanSpace ℝ (Fin p) → ℝ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin p)) :=
  {w | ∀ v ∈ V, inner ℝ w v ≤ s v + ε}

end HighDimCLT.MultBoot


