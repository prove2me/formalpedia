-- Prove2me | Definitions.Def_InventoryAnomaly_EW_Model
-- name    : InventoryAnomaly_EW_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:12.09219+00:00
-- url     : https://prove2.me/theorems/8ae173d6-ff6b-4f83-95b3-dd354d0cbff6
-- title:
--   §2–§3, pp. 8–18 — low-rank Poisson anomaly model, sampling law, EW algorithm (SVD_r, moment matching (7), plug-in (9), threshold (4)), cost (5), assumptions, Lemma 1's regularity conditions
-- statement:
--   This file sets up the model and algorithm of Farias, Li and Peng.
--
--   **Model (§2, pp. 8–9).** An instance consists of dimensions $n$ (stores) and $m$ (SKUs), an expected-demand matrix $M^*\in\mathbb R^{n\times m}$ with an SVD $M^*=U\,\mathrm{diag}(\sigma)\,V^\top$ of rank $r$, an anomaly model $\mathrm{Anom}(\alpha,M)$ (a family of laws on $\mathbb N$ indexed by $\alpha\in\mathbb R^d$ and a mean level $M\ge 0$, with a known parameter set $\Gamma\subset\mathbb R^d$ and a mean factor $g$), the true parameter $\alpha^*$, the anomaly probability $p_A^*$, the observation probability $p_O$, and two cost matrices $c^{(0)}$ (false positive: flag a non-anomalous entry) and $c^{(1)}$ (false negative: miss an anomaly). Each entry $(i,j)$ independently draws
--   1. $O_{ij}\sim\mathrm{Bernoulli}(p_O)$ (observed or not),
--   2. $B_{ij}\sim\mathrm{Bernoulli}(p_A^*)$ (anomalous or not),
--   3. $X_{ij}\sim\mathrm{Anom}(\alpha^*,M^*_{ij})$ if $B_{ij}=1$, and $X_{ij}\sim\mathrm{Poisson}(M^*_{ij})$ otherwise.
--
--   The data is $X_\Omega$: the sales on $\Omega=\{(i,j):O_{ij}=1\}$.
--
--   **Algorithm 1 (pp. 14–18).** With $X'$ the matrix $X_\Omega$ with unobserved entries set to $0$ and $\mathrm{SVD}(X_\Omega)_r$ a best rank-$\le r$ approximation of $X'$ in Frobenius norm,
--   $$\hat M=\frac{nm}{|\Omega|}\,\mathrm{SVD}(X_\Omega)_r .$$
--   For $\theta=(\alpha,p_A)$ let $e(\theta)=p_Ag(\alpha)+(1-p_A)$ and
--   $$g_t(\theta,M)=\frac1{nm}\sum_{i,j}\Big(p_A\,\mathbb P_{\mathrm{Anom}(\alpha,M_{ij})}(X\le t)+(1-p_A)\,\mathbb P_{\mathrm{Poisson}(M_{ij})}(X\le t)\Big),$$
--   $$h(\theta)=\sum_{t=0}^{T-1}\Big(g_t\big(\theta,\hat M/e(\theta)\big)-\frac{|\{(i,j)\in\Omega:X_{ij}\le t\}|}{|\Omega|}\Big)^2 \qquad (7).$$
--   The estimator $\hat\theta=(\hat\alpha,\hat p_A)$ is a point of $\Theta=\Gamma\times[0,1-c_A]$ with $h(\hat\theta)\le h(\theta^*)$. The plug-in estimates are $\hat x_{ij}=[\hat p_A\,\mathbb P_{\mathrm{Anom}(\hat\alpha,\hat M_{ij}/e(\hat\theta))}(X_{ij})]$, $\hat y_{ij}=[(1-\hat p_A)\,\mathbb P_{\mathrm{Poisson}(\hat M_{ij}/e(\hat\theta))}(X_{ij})]$ with $[z]=\max(\min(z,1),0)$, and $\hat f_{ij}=\hat y_{ij}/(\hat x_{ij}+\hat y_{ij})$ (9). The oracle quantities are $x^*_{ij}=p_A^*\mathbb P_{\mathrm{Anom}(\alpha^*,M^*_{ij})}(X_{ij})$, $y^*_{ij}=(1-p_A^*)\mathbb P_{\mathrm{Poisson}(M^*_{ij})}(X_{ij})$ and $f^*_{ij}=y^*_{ij}/(x^*_{ij}+y^*_{ij})=\mathbb P(B_{ij}=0\mid X_\Omega)$ (8).
--
--   **Decisions and cost.** Given an estimate $f$ of $f^*$, entry $(i,j)$ is flagged iff $f_{ij}\le c^{(1)}_{ij}/(c^{(0)}_{ij}+c^{(1)}_{ij})$ (rule (4) for $f^*$, Step 4 for $\hat f$). For decisions $A$,
--   $$\mathrm{cost}^A(X_\Omega)=\frac1{|\Omega|}\sum_{(i,j)\in\Omega}\Big(c^{(0)}_{ij}\,\mathbf 1\{A_{ij}=1\}\,f^*_{ij}+c^{(1)}_{ij}\,\mathbf 1\{A_{ij}=0\}\,(1-f^*_{ij})\Big),$$
--   the second line of (5). $\mathrm{cost}^{\pi^{EW}}$ uses $\hat f$, $\mathrm{cost}^{\pi^*}$ uses $f^*$.
--
--   **Assumptions.** `Model` collects §2's assumptions on $M^*$ (nonnegativity, SVD with orthonormal factors and decreasing positive singular values, $\|M^*\|_{\max}\ge c_M$, $\|M^*\|_{\max}\le L$, incoherence with parameter $\mu$, sparsity $\sqrt{p_O}\ge C_{sp}\log^{1.5}(m)\mu r\kappa^2/\sqrt m$), $p_A^*\le1-c_A$, and on $\mathrm{Anom}$ (sub-exponential with $\psi_1$-norm $\le L$, $K$-Lipschitz pmf, mean decomposition (2) with $g$ valued in $[0,1]$ and $K$-Lipschitz). `SparsityMax` is the sparsity condition in the form the proof of Theorem 2 uses (p. 41), $C_{sp}\log^{1.5}(m)\mu rL\kappa^2/(\|M^*\|_{\max}\sqrt m)\le\sqrt{p_O}$. `Regular` is Lemma 1's four regularity conditions on $F(\theta)=(g_t(\theta,M^*e(\theta^*)/e(\theta)))_{t<T}$, with $\tilde\delta=\delta'(K+L)\log m$ and $\delta'=\kappa^4\mu rL\sqrt{\log(m)/(p_Om)}$. `CostBound` says the costs lie in $[0,c_{\max}]$. `ThetaSel` is the selector property of $\hat\theta$ above, and `IsBestRankApprox` that of $\mathrm{SVD}_r$.
--
--   **Formalization Note.** $\theta=(\alpha,p_A)$ is a vector of $\mathbb R^{d+1}$ with $p_A$ the last coordinate, and $T=d+1$ moments are matched (the paper: "$T=d+1$ typically suffices"). $\Theta$ is $\Gamma\times[0,1-c_A]$ rather than $\Gamma\times[0,1)$, since the proof of Lemma 15 uses $e(\theta)\ge 1-p_A\ge c$ on $\Theta$. Laws are evaluated at the mean $\max(M,0)$, because $\hat M_{ij}/e(\hat\theta)$ may be negative. The cost is the closed form (5) with $f^*$ written by Bayes' rule (8); for decisions that are functions of $X_\Omega$ it equals the conditional expectation of p. 11. $c^{(0)}$ is the false-positive cost as in the bullets of p. 11, (4), (5) and Step 4 (the display on p. 12 swaps the two labels). The added conditions $2\le m$ (so $\log m>0$), $m\le n$ ("without loss of generality", p. 8), $1\le r\le m$, finiteness of the anomaly means (so (2) is not about a junk integral), and membership of $\mathrm{Anom}(\alpha^*,M^*_{ij})$ in the $\psi_1$-admissible set (so the norm bound is not about an empty infimum) are disclosed. $h$ counts $X_{ij}\le t$, as (7) does (the display in B.1.1 prints $=t$). The norm in the Lipschitz conditions is the Euclidean norm on $\alpha$ and the max metric on $(\alpha,M)$; the paper does not name one. `PMF.bernoulli` and `poissonPMF` are deprecated at this Mathlib revision but sound.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, pp. 8–18, §2–§3, eqs. (2)–(9), Algorithm 1, Lemma 1; p. 41 (sparsity as read in the proof of Theorem 2); p. 42 (g_t, h)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

/-- One entry of the experiment: (observed?, anomalous?, sales). -/
abbrev Entry := Bool × Bool × ℕ

/-- The probabilistic anomaly model `Anom(α, M)` with its mean factor `g` and known set `Γ`. -/
structure AnomModel (d : ℕ) where
  Γ : Set (EuclideanSpace ℝ (Fin d))
  anom : EuclideanSpace ℝ (Fin d) → ℝ≥0 → PMF ℕ
  g : EuclideanSpace ℝ (Fin d) → ℝ

/-- `P(Anom(α, M) = k)` as a real number, at a real mean clamped at `0`. -/
noncomputable def AnomModel.pmf {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d))
    (M : ℝ) (k : ℕ) : ℝ :=
  (A.anom α M.toNNReal k).toReal

noncomputable def AnomModel.cdf {d : ℕ} (A : AnomModel d) (α : EuclideanSpace ℝ (Fin d))
    (M : ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (t + 1), A.pmf α M k

/-- Poisson pmf at a real mean clamped at `0`. -/
noncomputable def poisPmf (M : ℝ) (k : ℕ) : ℝ := poissonPMFReal M.toNNReal k

noncomputable def poisCdf (M : ℝ) (t : ℕ) : ℝ := ∑ k ∈ Finset.range (t + 1), poisPmf M k

/-- θ = (α, p_A) ∈ ℝ^{d+1}: the first `d` coordinates and the last one. -/
noncomputable def alphaOf {d : ℕ} (θ : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => θ (Fin.castSucc i))

def pAOf {d : ℕ} (θ : EuclideanSpace ℝ (Fin (d + 1))) : ℝ := θ (Fin.last d)

/-- e(θ) = p_A g(α) + (1 − p_A). -/
noncomputable def AnomModel.e {d : ℕ} (A : AnomModel d) (θ : EuclideanSpace ℝ (Fin (d + 1))) : ℝ :=
  pAOf θ * A.g (alphaOf θ) + (1 - pAOf θ)

/-- Problem instance. -/
structure Instance (d : ℕ) where
  n : ℕ
  m : ℕ
  r : ℕ
  Mstar : Matrix (Fin n) (Fin m) ℝ
  U : Matrix (Fin n) (Fin r) ℝ
  V : Matrix (Fin m) (Fin r) ℝ
  σ : Fin r → ℝ
  model : AnomModel d
  αstar : EuclideanSpace ℝ (Fin d)
  pAstar : ℝ≥0
  pO : ℝ≥0
  c0 : Matrix (Fin n) (Fin m) ℝ
  c1 : Matrix (Fin n) (Fin m) ℝ

variable {d : ℕ}

noncomputable def Instance.θstar (I : Instance d) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (Fin.snoc (fun i => I.αstar i) (I.pAstar : ℝ))

/-- Law of one entry: Ω ∋ (i,j) w.p. p_O, B_ij ~ Bernoulli(p_A*), X_ij ~ Poisson or Anom. -/
noncomputable def Instance.entryPMF (I : Instance d) (ij : Fin I.n × Fin I.m) : PMF Entry :=
  (PMF.bernoulli (min I.pO 1) (min_le_right _ _)).bind fun o =>
    (PMF.bernoulli (min I.pAstar 1) (min_le_right _ _)).bind fun b =>
      (if b then I.model.anom I.αstar (I.Mstar ij.1 ij.2).toNNReal
        else poissonPMF (I.Mstar ij.1 ij.2).toNNReal).map fun x => (o, b, x)

abbrev Instance.Sample (I : Instance d) := Fin I.n × Fin I.m → Entry

noncomputable def Instance.law (I : Instance d) : Measure I.Sample :=
  Measure.pi fun ij => (I.entryPMF ij).toMeasure

/-- The observation X_Ω. -/
abbrev Instance.Obs (I : Instance d) := Fin I.n × Fin I.m → Option ℕ

def Instance.obs (I : Instance d) (ω : I.Sample) : I.Obs :=
  fun ij => if (ω ij).1 then some (ω ij).2.2 else none

def Instance.omega (I : Instance d) (x : I.Obs) : Finset (Fin I.n × Fin I.m) :=
  Finset.univ.filter fun ij => (x ij).isSome

/-- X': X_Ω with unobserved entries set to 0. -/
def Instance.Xzero (I : Instance d) (x : I.Obs) : Matrix (Fin I.n) (Fin I.m) ℝ :=
  fun i j => ((x (i, j)).getD 0 : ℝ)

def frobSq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- `svdr` returns a best rank-≤r approximation in Frobenius norm. -/
def IsBestRankApprox {a b : ℕ} (r : ℕ)
    (svdr : Matrix (Fin a) (Fin b) ℝ → Matrix (Fin a) (Fin b) ℝ) : Prop :=
  ∀ X, (svdr X).rank ≤ r ∧ ∀ Y : Matrix (Fin a) (Fin b) ℝ, Y.rank ≤ r →
    frobSq (svdr X - X) ≤ frobSq (Y - X)

noncomputable def Instance.Mhat (I : Instance d)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ) (x : I.Obs) :
    Matrix (Fin I.n) (Fin I.m) ℝ :=
  ((I.n * I.m : ℝ) / (I.omega x).card) • svdr (I.Xzero x)

/-- g_t(θ, M) (B.1.1). -/
noncomputable def Instance.gt (I : Instance d) (θ : EuclideanSpace ℝ (Fin (d + 1)))
    (M : Matrix (Fin I.n) (Fin I.m) ℝ) (t : ℕ) : ℝ :=
  (1 / (I.n * I.m : ℝ)) * ∑ i, ∑ j,
    (pAOf θ * I.model.cdf (alphaOf θ) (M i j) t + (1 - pAOf θ) * poisCdf (M i j) t)

/-- Objective of (7). -/
noncomputable def Instance.hobj (I : Instance d) (T : ℕ)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ) (x : I.Obs)
    (θ : EuclideanSpace ℝ (Fin (d + 1))) : ℝ :=
  ∑ t ∈ Finset.range T,
    (I.gt θ ((I.model.e θ)⁻¹ • I.Mhat svdr x) t -
      ((I.omega x).filter fun ij => ((x ij).getD 0) ≤ t).card / (I.omega x).card) ^ 2

def clamp01 (z : ℝ) : ℝ := max (min z 1) 0

/-- Plug-in estimates x̂_ij, ŷ_ij (p. 18) at θ̂ and M̂_ij / e(θ̂), truncated to [0, 1]. -/
noncomputable def Instance.xhat (I : Instance d)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) (x : I.Obs) (i : Fin I.n) (j : Fin I.m) : ℝ :=
  clamp01 (pAOf (θhat x) * I.model.pmf (alphaOf (θhat x))
    (I.Mhat svdr x i j / I.model.e (θhat x)) ((x (i, j)).getD 0))

noncomputable def Instance.yhat (I : Instance d)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) (x : I.Obs) (i : Fin I.n) (j : Fin I.m) : ℝ :=
  clamp01 ((1 - pAOf (θhat x)) * poisPmf (I.Mhat svdr x i j / I.model.e (θhat x))
    ((x (i, j)).getD 0))

/-- f̂_ij, (9). -/
noncomputable def Instance.fhat (I : Instance d)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) (x : I.Obs) (i : Fin I.n) (j : Fin I.m) : ℝ :=
  I.yhat svdr θhat x i j / (I.xhat svdr θhat x i j + I.yhat svdr θhat x i j)

noncomputable def Instance.xstar (I : Instance d) (x : I.Obs) (i : Fin I.n) (j : Fin I.m) : ℝ :=
  (I.pAstar : ℝ) * I.model.pmf I.αstar (I.Mstar i j) ((x (i, j)).getD 0)

noncomputable def Instance.ystar (I : Instance d) (x : I.Obs) (i : Fin I.n) (j : Fin I.m) : ℝ :=
  (1 - (I.pAstar : ℝ)) * poisPmf (I.Mstar i j) ((x (i, j)).getD 0)

/-- f*_ij, (8). -/
noncomputable def Instance.fstar (I : Instance d) (x : I.Obs) (i : Fin I.n) (j : Fin I.m) : ℝ :=
  I.ystar x i j / (I.xstar x i j + I.ystar x i j)

/-- Threshold rule (4) applied to an estimate f. -/
noncomputable def Instance.rule (I : Instance d) (f : ℝ) (i : Fin I.n) (j : Fin I.m) : Bool :=
  decide (f ≤ I.c1 i j / (I.c0 i j + I.c1 i j))

/-- cost^π(X_Ω) in the form (5): decisions `A`. -/
noncomputable def Instance.cost (I : Instance d) (x : I.Obs) (A : Fin I.n → Fin I.m → Bool) : ℝ :=
  (1 / ((I.omega x).card : ℝ)) * ∑ ij ∈ I.omega x,
    (if A ij.1 ij.2 then I.c0 ij.1 ij.2 * I.fstar x ij.1 ij.2
      else I.c1 ij.1 ij.2 * (1 - I.fstar x ij.1 ij.2))

noncomputable def Instance.costEW (I : Instance d)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) (x : I.Obs) : ℝ :=
  I.cost x fun i j => I.rule (I.fhat svdr θhat x i j) i j

noncomputable def Instance.costStar (I : Instance d) (x : I.Obs) : ℝ :=
  I.cost x fun i j => I.rule (I.fstar x i j) i j

def maxNorm {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) (B : ℝ) : Prop := ∀ i j, |A i j| ≤ B

/-- F(θ) of Lemma 1, T = d + 1. -/
noncomputable def Instance.F (I : Instance d) (θ : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm fun t =>
    I.gt θ ((I.model.e I.θstar / I.model.e θ) • I.Mstar) t

noncomputable def Instance.Θ (I : Instance d) (cA : ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {θ | alphaOf θ ∈ I.model.Γ ∧ 0 ≤ pAOf θ ∧ pAOf θ ≤ 1 - cA}

/-- κ = σ₁*/σ_r*. -/
noncomputable def Instance.κ (I : Instance d) (hr : 0 < I.r) : ℝ := I.σ ⟨0, hr⟩ / I.σ ⟨I.r - 1, by omega⟩

/-- §2 (pp. 8–10) assumptions on the instance: dimensions, SVD of M*, boundedness, incoherence,
sparsity (with constant `Csp`), p_O, p_A* ≤ 1 − cA, and the three assumptions on Anom(·,·). -/
structure Instance.Model (I : Instance d) (cM cA Csp K L μ : ℝ) : Prop where
  two_le_m : 2 ≤ I.m
  m_le_n : I.m ≤ I.n
  r_pos : 0 < I.r
  r_le_m : I.r ≤ I.m
  nonneg : ∀ i j, 0 ≤ I.Mstar i j
  svd : I.Mstar = I.U * Matrix.diagonal I.σ * I.V.transpose
  U_orth : I.U.transpose * I.U = 1
  V_orth : I.V.transpose * I.V = 1
  σ_anti : Antitone I.σ
  σ_pos : ∀ k, 0 < I.σ k
  max_lb : ∃ i j, cM ≤ I.Mstar i j
  max_ub : maxNorm I.Mstar L
  incoh_U : ∀ i, ∑ k, I.U i k ^ 2 ≤ μ * I.r / I.n
  incoh_V : ∀ j, ∑ k, I.V j k ^ 2 ≤ μ * I.r / I.m
  sparsity : Csp * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * I.κ r_pos ^ 2 / Real.sqrt I.m ≤
    Real.sqrt I.pO
  pO_le : I.pO ≤ 1
  pA_le : (I.pAstar : ℝ) ≤ 1 - cA
  α_mem : I.αstar ∈ I.model.Γ
  subexp : ∀ i j, ∃ t > 0, Integrable (fun k : ℕ => Real.exp (|(k : ℝ)| / t))
      (I.model.anom I.αstar (I.Mstar i j).toNNReal).toMeasure ∧
    ∫ k, Real.exp (|(k : ℝ)| / t) ∂(I.model.anom I.αstar (I.Mstar i j).toNNReal).toMeasure ≤ 2
  subexp_le : ∀ i j, HighDimProb.Concentration.subexponentialNorm
      (I.model.anom I.αstar (I.Mstar i j).toNNReal).toMeasure (fun k : ℕ => (k : ℝ)) ≤ L
  smooth : ∀ k : ℕ, ∀ p ∈ I.model.Γ ×ˢ Set.Ici (0 : ℝ), ∀ q ∈ I.model.Γ ×ˢ Set.Ici (0 : ℝ),
    |I.model.pmf p.1 p.2 k - I.model.pmf q.1 q.2 k| ≤ K * dist p q
  mean_int : ∀ α ∈ I.model.Γ, ∀ M : ℝ≥0,
    Integrable (fun k : ℕ => (k : ℝ)) (I.model.anom α M).toMeasure
  mean : ∀ α ∈ I.model.Γ, ∀ M : ℝ≥0,
    ∫ k, (k : ℝ) ∂(I.model.anom α M).toMeasure = I.model.g α * M
  g_mem : ∀ α, 0 ≤ I.model.g α ∧ I.model.g α ≤ 1
  g_lip : ∀ α β, |I.model.g α - I.model.g β| ≤ K * dist α β

/-- δ' = κ⁴ μ r L √(log m / (p_O m)) (p. 17). -/
noncomputable def Instance.δ' (I : Instance d) (hr : 0 < I.r) (μ L : ℝ) : ℝ :=
  I.κ hr ^ 4 * μ * I.r * L * Real.sqrt (Real.log I.m / (I.pO * I.m))

/-- Lemma 1's regularity conditions on F (p. 17), with T = d + 1 and both of its constants `C`
equal to `CRC`. The Jacobian J_F is the derivative of F within Θ (one-sided at boundary points of
Θ, where F is only assumed C¹ on Θ). -/
def Instance.Regular (I : Instance d) (hr : 0 < I.r) (cA CRC K L μ : ℝ) : Prop :=
  let δt := I.δ' hr μ L * (K + L) * Real.log I.m
  ContDiffOn ℝ 1 I.F (I.Θ cA) ∧ Set.InjOn I.F (I.Θ cA) ∧
  Metric.closedBall I.θstar δt ⊆ I.Θ cA ∧
  (∀ θ ∈ Metric.closedBall I.θstar δt,
    ‖fderivWithin ℝ I.F (I.Θ cA) θ - fderivWithin ℝ I.F (I.Θ cA) I.θstar‖ ≤
      CRC / δt * ‖θ - I.θstar‖) ∧
  ∃ Jinv : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)),
    Jinv.comp (fderivWithin ℝ I.F (I.Θ cA) I.θstar) = ContinuousLinearMap.id ℝ _ ∧
    (fderivWithin ℝ I.F (I.Θ cA) I.θstar).comp Jinv = ContinuousLinearMap.id ℝ _ ∧ ‖Jinv‖ ≤ CRC

def Instance.CostBound (I : Instance d) (cmax : ℝ) : Prop :=
  ∀ i j, 0 ≤ I.c0 i j ∧ I.c0 i j ≤ cmax ∧ 0 ≤ I.c1 i j ∧ I.c1 i j ≤ cmax

/-- The selector θ̂ returns a point of Θ whose objective (7) is at most that of θ*. -/
def Instance.ThetaSel (I : Instance d) (cA : ℝ)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) : Prop :=
  ∀ x, θhat x ∈ I.Θ cA ∧ I.hobj (d + 1) svdr x (θhat x) ≤ I.hobj (d + 1) svdr x I.θstar

/-- The sparsity assumption in the form the proof of Theorem 2 reads it (p. 41):
`Csp · log^{1.5}(m) μ r L κ² / (‖M*‖_max √m) ≤ √p_O`, where `‖M*‖_max` is the entry `(i₀, j₀)`
that dominates all others (`M*` is nonnegative). -/
def Instance.SparsityMax (I : Instance d) (hr : 0 < I.r) (Csp μ L : ℝ) : Prop :=
  ∀ i₀ j₀, (∀ i j, I.Mstar i j ≤ I.Mstar i₀ j₀) →
    Csp * Real.log I.m ^ ((3 : ℝ) / 2) * μ * I.r * L * I.κ hr ^ 2 /
      (I.Mstar i₀ j₀ * Real.sqrt I.m) ≤ Real.sqrt I.pO

end InventoryAnomaly.EW


