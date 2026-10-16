-- Prove2me | Definitions.Def_RobustSpecClust_Est_Setting
-- name    : RobustSpecClust_Est_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:48.394144+00:00
-- url     : https://prove2.me/theorems/5ba3b65e-bd1d-417b-b524-d6cc3828be98
-- title:
--   §2.2, §3, (6), App. A — sub-Gaussian mixture with outliers, Gaussian kernel, Robust-LP solution X̂, true clustering matrix X⁰, reference matrix R
-- statement:
--   This file fixes the objects of the sub-Gaussian mixture model with outliers and of the Robust-LP clustering algorithm of Srivastava, Sarkar and Hanasusanto.
--
--   **Points.** There are $N = n + m$ points in $\mathbb R^d$: $n$ inliers $\mathcal I$ and $m$ outliers $\mathcal O$, indexed together by $\mathrm{Fin}\,n \sqcup \mathrm{Fin}\,m$. Each inlier $i$ carries a label $\varphi_i \in [r]$; the clusters are $\mathcal C_k = \{i \in \mathcal I : \varphi_i = k\}$ with sizes $n_k = |\mathcal C_k|$ and $n_{\min} = \min_{k\in[r]} n_k$ (for $r \ge 1$). Given centres $\mu_1,\dots,\mu_r \in \mathbb R^d$, the separations are $\Delta_{kl} = \|\mu_k - \mu_l\|_2$ and $\Delta_{\min} = \min_{k \ne l} \Delta_{kl}$ (for $r \ge 2$). The observed inlier is
--   $$y_i = \mu_{\varphi_i} + \xi_i ,$$
--   and the outlier $o$ is an arbitrary vector $z_o$.
--
--   **Sub-gaussian vectors (Definition 3).** A random vector $\xi$ in $\mathbb R^d$ is sub-gaussian with parameter $\psi > 0$ if, for every $\nu \in \mathbb R^d$, $e^{t\,\nu^\top \xi}$ is integrable for all real $t$ and
--   $$\mathbb E\big[e^{\nu^\top \xi}\big] \le e^{\psi^2 \|\nu\|^2/2}.$$
--   (This forces $\mathbb E\,\xi = 0$.) The **noise model** with fixed labels requires the inlier noises $\xi_1,\dots,\xi_n$ to be measurable, mutually independent, identically distributed within each cluster, with $\xi_i$ sub-gaussian with parameter $\sigma_{\varphi_i}$, and $\sigma_k > 0$ for every $k$; $\sigma_{\max} = \max_k \sigma_k$.
--
--   **Kernel and Robust-LP.** The Gaussian kernel is $K_{ij} = \exp(-\|y_i - y_j\|^2/2\theta^2)$. The Robust-LP solution is the closed form $\hat X_{ij} = 1$ if $K_{ij} - \gamma > 0$ and $0$ otherwise. The true clustering matrix $X^0$ has $X^0_{ij} = 1$ exactly when $i$ and $j$ are inliers with the same label.
--
--   **Matrix notation (§2.1).** $\|A\|_1 = \sum_{ij} |A_{ij}|$ (entrywise), $\langle A, B\rangle = \sum_{ij} A_{ij} B_{ij}$, $E_N$ is the all-ones matrix, and $A_{\mathcal I}$ is the inlier $\times$ inlier block. $\tau_{\mathrm{out}} = \max_{k\ne l} \tau^{(k,l)}_{\mathrm{out}}$.
--
--   **Reference matrix (6).** Given thresholds $\tau_{\mathrm{in}}$ and $\tau^{(k,l)}_{\mathrm{out}}$,
--   $$R_{ij} = \begin{cases} \max\{K_{ij}, \tau_{\mathrm{in}}\} & i, j \in \mathcal C_k,\\ \min\{K_{ij}, \tau^{(k,l)}_{\mathrm{out}}\} & i \in \mathcal C_k,\ j \in \mathcal C_l,\ l \ne k,\\ \gamma & i \in \mathcal O \text{ or } j \in \mathcal O.\end{cases}$$
--
--   **Corruption counts (E.2).** $m_c^{(k,k)}$ is the number of ordered pairs $(i,j) \in \mathcal C_k \times \mathcal C_k$ with $K_{ij} < \tau_{\mathrm{in}}$, and $m_c^{(k,l)}$ the number of $(i,j) \in \mathcal C_k \times \mathcal C_l$ with $K_{ij} > \tau^{(k,l)}_{\mathrm{out}}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The labels $\varphi$ are fixed (the paper draws them from Multinomial$(\pi)$, but its proof conditions on them and $n_{\min}$ appears in the probability bound). $\sigma_k$ is the Definition 3 parameter, not the "largest eigenvalue of the second moment matrix" of §2.2 (the proof uses the former, (E.5)). The sub-gaussian condition is Mathlib's `HasSubgaussianMGF` of $\nu^\top\xi$ with variance proxy $\psi^2\|\nu\|^2$. Minima and maxima over $[r]$ and over pairs $k \ne l$ are `Finset.inf'`/`sup'` and take an explicit nonemptiness proof ($r \ge 1$, resp. $r \ge 2$). Outliers carry no assumption.
-- source:
--   arXiv:1912.07546v3, §2.1 (p. 6), §2.2 (pp. 6–7), §3 (pp. 9–10, Robust-LP and closed form of X̂), display (6) (p. 11), Appendix A Definition 3 (p. 37), (E.2) (p. 39)

import Mathlib

namespace RobustSpecClust.Est

noncomputable section

open MeasureTheory ProbabilityTheory

/-- `E d` is the Euclidean space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Point index: `Sum.inl i` is inlier `i`, `Sum.inr o` is outlier `o` (N = n + m points). -/
abbrev Pt (n m : ℕ) := Fin n ⊕ Fin m

/-- Appendix A, Definition 3 (mean zero): `ξ` is sub-gaussian with parameter `ψ > 0`, i.e.
`E[exp(νᵀξ)] ≤ exp(ψ²‖ν‖²/2)` for every `ν ∈ ℝ^d` (with the exponential moments integrable). -/
def IsSubgaussianVec {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (ξ : Ω → E d)
    (ψ : ℝ) : Prop :=
  0 < ψ ∧ ∀ ν : E d,
    HasSubgaussianMGF (fun ω => inner ℝ ν (ξ ω)) (Real.toNNReal (ψ ^ 2 * ‖ν‖ ^ 2)) P

/-- §2.2: the inlier noise of the sub-gaussian mixture model with fixed labels `φ`:
measurable, mutually independent, identically distributed within each cluster, and the noise of
a point of cluster `k` is sub-gaussian (Definition 3) with parameter `σ k > 0`. -/
structure IsSGMMNoise {Ω : Type*} [MeasurableSpace Ω] {d n r : ℕ} (P : Measure Ω)
    (φ : Fin n → Fin r) (σ : Fin r → ℝ) (ξ : Fin n → Ω → E d) : Prop where
  measurable : ∀ i, Measurable (ξ i)
  indep : iIndepFun ξ P
  identDistrib : ∀ i j, φ i = φ j → IdentDistrib (ξ i) (ξ j) P P
  subgaussian : ∀ i, IsSubgaussianVec P (ξ i) (σ (φ i))
  pos : ∀ k, 0 < σ k

/-- §2.2: the observed points. Inlier `i` is `y_i = μ_{φ i} + ξ_i`; outlier `o` is `z_o`. -/
def dataPoints {Ω : Type*} {d n m r : ℕ} (μ : Fin r → E d) (φ : Fin n → Fin r)
    (ξ : Fin n → Ω → E d) (z : Fin m → Ω → E d) (ω : Ω) : Pt n m → E d
  | Sum.inl i => μ (φ i) + ξ i ω
  | Sum.inr o => z o ω

/-- §2.2: the Gaussian kernel matrix `K_ij = exp(-‖y_i - y_j‖² / (2θ²))`. -/
def kernel {ι : Type*} {d : ℕ} (θ : ℝ) (y : ι → E d) : Matrix ι ι ℝ :=
  fun i j => Real.exp (-(‖y i - y j‖ ^ 2) / (2 * θ ^ 2))

/-- §3, p. 10: the closed-form Robust-LP solution `X̂_ij = 1` if `K_ij - γ > 0`, else `0`. -/
def robustLPSol {ι : Type*} (K : Matrix ι ι ℝ) (γ : ℝ) : Matrix ι ι ℝ :=
  fun i j => if γ < K i j then 1 else 0

/-- §2.2: the true clustering matrix `X⁰`: `1` iff both points are inliers with the same label. -/
def trueClust {n m r : ℕ} (φ : Fin n → Fin r) : Matrix (Pt n m) (Pt n m) ℝ
  | Sum.inl i, Sum.inl j => if φ i = φ j then 1 else 0
  | _, _ => 0

/-- §2.1: the entrywise ℓ₁ norm `‖A‖₁ = Σ_ij |A_ij|`. -/
def l1 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |A i j|

/-- §2.1: the trace inner product `⟨A, B⟩ = Σ_ij A_ij B_ij`. -/
def frobInner {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- §2.1: the all-ones matrix `E_N`. -/
def ones (ι : Type*) : Matrix ι ι ℝ := Matrix.of fun _ _ => 1

/-- The inlier × inlier block `A_I`. -/
def inlierBlock {n m : ℕ} (A : Matrix (Pt n m) (Pt n m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A (Sum.inl i) (Sum.inl j)

/-- §2.2: the cluster size `n_k = |C_k|`. -/
def clusterSize {n r : ℕ} (φ : Fin n → Fin r) (k : Fin r) : ℕ :=
  (Finset.univ.filter (fun i => φ i = k)).card

lemma univ_nonempty_of_pos {r : ℕ} (hr : 0 < r) : (Finset.univ : Finset (Fin r)).Nonempty :=
  ⟨⟨0, hr⟩, Finset.mem_univ _⟩

lemma offDiag_nonempty_of_two_le {r : ℕ} (hr : 2 ≤ r) :
    (Finset.univ : Finset (Fin r)).offDiag.Nonempty :=
  ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩

/-- `n_min = min_k n_k` (needs `r ≥ 1`). -/
def nmin {n r : ℕ} (φ : Fin n → Fin r) (hr : 0 < r) : ℝ :=
  Finset.univ.inf' (univ_nonempty_of_pos hr) (fun k => (clusterSize φ k : ℝ))

/-- `Δ_kl = ‖μ_k - μ_l‖`. -/
def sep {d r : ℕ} (μ : Fin r → E d) (k l : Fin r) : ℝ := ‖μ k - μ l‖

/-- `Δ_min = min_{k ≠ l} Δ_kl` (needs `r ≥ 2`). -/
def Δmin {d r : ℕ} (μ : Fin r → E d) (hr : 2 ≤ r) : ℝ :=
  Finset.univ.offDiag.inf' (offDiag_nonempty_of_two_le hr) (fun p => sep μ p.1 p.2)

/-- `σ_max = max_k σ_k` (needs `r ≥ 1`). -/
def σmax {r : ℕ} (σ : Fin r → ℝ) (hr : 0 < r) : ℝ :=
  Finset.univ.sup' (univ_nonempty_of_pos hr) σ

/-- `τ_out = max_{k ≠ l} τ_out^{(k,l)}` (needs `r ≥ 2`). -/
def tauOutMax {r : ℕ} (τout : Fin r → Fin r → ℝ) (hr : 2 ≤ r) : ℝ :=
  Finset.univ.offDiag.sup' (offDiag_nonempty_of_two_le hr) (fun p => τout p.1 p.2)

/-- Display (6), p. 11: the reference matrix `R`. -/
def refMatrix {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (τout : Fin r → Fin r → ℝ) (γ : ℝ) : Matrix (Pt n m) (Pt n m) ℝ
  | Sum.inl i, Sum.inl j =>
      if φ i = φ j then max (K (Sum.inl i) (Sum.inl j)) τin
      else min (K (Sum.inl i) (Sum.inl j)) (τout (φ i) (φ j))
  | _, _ => γ

/-- (E.2): `m_c^{(k,k)}`, the number of entries `(i, j) ∈ C_k × C_k` with `K_ij < τ_in`. -/
def mcDiag {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (k : Fin r) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => φ p.1 = k ∧ φ p.2 = k ∧ K (Sum.inl p.1) (Sum.inl p.2) < τin)).card

/-- (E.2): `m_c^{(k,l)}`, the number of entries `(i, j) ∈ C_k × C_l` with `K_ij > τ_out^{(k,l)}`. -/
def mcOff {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r)
    (τout : Fin r → Fin r → ℝ) (k l : Fin r) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => φ p.1 = k ∧ φ p.2 = l ∧ τout k l < K (Sum.inl p.1) (Sum.inl p.2))).card

end

end RobustSpecClust.Est


