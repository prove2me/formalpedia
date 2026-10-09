-- Prove2me | Definitions.Def_DIGing_Undir_Setting
-- name    : DIGing_Undir_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:23.456981+00:00
-- url     : https://prove2.me/theorems/c5b48d05-72d0-41ca-8232-a4823007a596
-- title:
--   §2.1, §3, pp. 5–18 — W_B(k), σ_max, δ(k), Assumptions 1–3, DIGing (Algorithm 1), z(k), J₁, the rate λ, and α(τ), λ(τ) of (46)
-- statement:
--   This file fixes the objects of the undirected-graph analysis (Section 3) of Nedić, Olshevsky and Shi.
--
--   1. **Graphs and mixing products.** $E(k)$ is the undirected communication graph on the agents $\{1,\dots,n\}$ at time $k$, and $W(k)\in\mathbb R^{n\times n}$ is the mixing matrix. For $b\ge0$,
--   $$W_b(k)=W(k)W(k-1)\cdots W(k-b+1),$$
--   with $W_0(k)=I$ and any factor with a negative time index equal to $I$.
--   2. **The contraction factor.** $\sigma_{\max}\{M\}$ is the largest singular value of $M$, and
--   $$\delta(k)=\sigma_{\max}\Big\{W_B(k)-\tfrac1n\mathbf 1\mathbf 1^\top\Big\}.$$
--   3. **Assumption 1.** (i) $W_{ij}(k)=0$ whenever $i\ne j$ and $(j,i)\notin E(k)$; (ii) each $W(k)$ is doubly stochastic, $W(k)\mathbf 1=\mathbf 1$ and $\mathbf 1^\top W(k)=\mathbf 1^\top$, with nonnegative entries; (iii) for some positive integer $B$, $\sup_{k\ge B-1}\delta(k)<1$.
--   4. **Algorithm 1 (DIGing)** with step size $\alpha$: $\mathbf y(0)=\nabla\mathbf f(\mathbf x(0))$ and, for $k=0,1,\dots$,
--   $$\mathbf x(k+1)=W(k)\mathbf x(k)-\alpha\mathbf y(k),\qquad \mathbf y(k+1)=W(k)\mathbf y(k)+\nabla\mathbf f(\mathbf x(k+1))-\nabla\mathbf f(\mathbf x(k)).$$
--   5. **Gradient differences.** $\mathbf z(k)=\nabla\mathbf f(\mathbf x(k))-\nabla\mathbf f(\mathbf x(k-1))$ for $k\ge1$ and $\mathbf z(0)=0$.
--   6. **Constants of Theorem 10.** $J_1=3\bar\kappa B^2(1+4\sqrt n\sqrt{\bar\kappa})$. For $J>0$, $\delta$ and $\mu>0$, the split point $\alpha_{\rm s}=1.5(\sqrt{J^2+(1-\delta^2)J}-\delta J)^2/(\mu J(J+1)^2)$, the bound $\alpha_{\max}=1.5(1-\delta)^2/(\mu J)$, and the rate
--   $$\lambda=\begin{cases}\sqrt[2B]{1-\alpha\mu/1.5}, & \alpha\le\alpha_{\rm s},\\ \sqrt[B]{\sqrt{\alpha\mu J/1.5}+\delta}, & \alpha>\alpha_{\rm s}.\end{cases}$$
--   7. **Assumption 2.** For a positive integer $\tilde B$, the union graph $(V, E(t\tilde B)\cup\cdots\cup E(t\tilde B+\tilde B-1))$ is connected for every $t=0,1,\dots$
--   8. **Assumption 3** with constant $\tau$: unit row and column sums; $W_{ii}(k)>0$; for $i\ne j$, $W_{ij}(k)>0$ if $(j,i)\in E(k)$ and $W_{ij}(k)=0$ otherwise; $\tau>0$ and every positive entry is at least $\tau$.
--   9. **Corollary 11's step size and rate (46).**
--   $$\alpha(\tau)=\frac{3\tau^2}{128B^2n^{4.5}L\sqrt{\bar\kappa}}-\frac{1.5}{\bar\mu}\Big(\frac{\tau^2}{128B^2n^{4.5}\bar\kappa^{1.5}}\Big)^2,\qquad \lambda(\tau)=\sqrt[B]{1-\frac{\tau^2}{128B^2n^{4.5}\bar\kappa^{1.5}}}.$$
--
--   These are the data of Theorem 10 and its lemmas: Assumption 1 is the only network hypothesis of the main theorem, and $\delta$ and $J_1$ enter its explicit rate.
--
--   **Formalization Note.** "Doubly stochastic" is Mathlib's `doublyStochastic`, which includes **nonnegative entries**. The page glosses (ii) by the row and column sums only; nonnegativity is the standard meaning, the paper calls the $W(k)$ "nonnegative matrices" (Corollary 11), and step (14) of Lemma 6 is false without it. $\sigma_{\max}$ is the operator norm of $M$ on Euclidean $\mathbb R^n$. "$\sup_{k\ge B-1}\delta(k)<1$" is written as "some $c<1$ bounds every $\delta(k)$, $k\ge B-1$". Real powers $\sqrt[m]{\cdot}$, $n^{4.5}$ and $\bar\kappa^{1.5}$ are `Real.rpow`. The undirected graphs are Mathlib `SimpleGraph`s; in Assumption 3(iii), "otherwise" applies to $i\ne j$, since (ii) makes the diagonal positive.
-- source:
--   Nedić, Olshevsky & Shi, arXiv:1607.03218v3, Algorithm 1 (p. 5), §3 W_b(k) and Assumptions 1–3 (pp. 7–8), §3.2 z(k) (p. 10), Theorem 10 J₁ and λ (p. 16), Corollary 11 display (46) and λ(τ) (p. 18)

import Mathlib
import Definitions.Def_DIGing_Undir_Common

namespace DIGing.Undir

open Matrix

/-- The product of mixing matrices `W_b(k) = W(k) W(k − 1) ⋯ W(k − b + 1)` (arXiv:1607.03218v3,
§3, p. 7), with the page's convention that a factor with a negative time index is `I`; in
particular `W_0(k) = I`. -/
def prodW {n : ℕ} (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (b k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (List.ofFn (fun t : Fin b => if (t : ℕ) ≤ k then W (k - t) else 1)).prod

/-- The largest singular value `σ_max{M}` of a real `n × n` matrix, i.e. its operator norm as a
map of the Euclidean space `ℝⁿ` (§1.4, p. 4: "the spectral norm … equals the largest singular
value"). -/
noncomputable def sigmaMax {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- The averaging matrix `(1/n) 1 1ᵀ`. -/
noncomputable def avgMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => 1 / (n : ℝ)

/-- `δ(k) = σ_max{W_B(k) − (1/n) 1 1ᵀ}` of Assumption 1(iii), p. 7. -/
noncomputable def deltaK {n : ℕ} (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (B k : ℕ) : ℝ :=
  sigmaMax (prodW W B k - avgMat n)

/-- Assumption 1 (Mixing matrix sequence), p. 7, for the undirected graph sequence `E`:
(i) `W_ij(k) = 0` if `i ≠ j` and `(j, i) ∉ E(k)`; (ii) every `W(k)` is doubly stochastic
(Mathlib's `doublyStochastic`: nonnegative entries, unit row and column sums); (iii) for a positive
integer `B`, `sup_{k ≥ B − 1} δ(k) < 1`, written as: some `c < 1` bounds every `δ(k)`, `k ≥ B − 1`. -/
def Assumption1 {n : ℕ} (E : ℕ → SimpleGraph (Fin n)) (W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (B : ℕ) : Prop :=
  (∀ k i j, i ≠ j → ¬ (E k).Adj j i → W k i j = 0) ∧
  (∀ k, W k ∈ doublyStochastic ℝ (Fin n)) ∧
  0 < B ∧ ∃ c : ℝ, c < 1 ∧ ∀ k, B - 1 ≤ k → deltaK W B k ≤ c

/-- Algorithm 1 (DIGing), p. 5, with step size `α`: `y(0) = ∇f(x(0))`,
`x(k + 1) = W(k) x(k) − α y(k)`, `y(k + 1) = W(k) y(k) + ∇f(x(k + 1)) − ∇f(x(k))`. -/
def IsDIGingRun {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (W : ℕ → Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (x y : ℕ → Stack n p) : Prop :=
  y 0 = gradStack f (x 0) ∧
  ∀ k, x (k + 1) = mix (W k) (x k) - α • y k ∧
    y (k + 1) = mix (W k) (y k) + gradStack f (x (k + 1)) - gradStack f (x k)

/-- `z(k) = ∇f(x(k)) − ∇f(x(k − 1))` for `k ≥ 1` and `z(0) = 0` (§3.2, p. 10). -/
noncomputable def zSeq {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (x : ℕ → Stack n p) (k : ℕ) : Stack n p :=
  if k = 0 then 0 else gradStack f (x k) - gradStack f (x (k - 1))

/-- `J₁ = 3 κ̄ B² (1 + 4 √n √κ̄)` (Theorem 10, p. 16). -/
noncomputable def J1 {n : ℕ} (Lc mu : Fin n → ℝ) (B : ℕ) : ℝ :=
  3 * kappa Lc mu * (B : ℝ) ^ 2 * (1 + 4 * Real.sqrt n * Real.sqrt (kappa Lc mu))

/-- The split point `1.5(√(J² + (1 − δ²)J) − δJ)² / (μ J (J + 1)²)` of the two step-size regimes. -/
noncomputable def alphaSplit (J δ μ : ℝ) : ℝ :=
  3 / 2 * (Real.sqrt (J ^ 2 + (1 - δ ^ 2) * J) - δ * J) ^ 2 / (μ * J * (J + 1) ^ 2)

/-- The step-size bound `1.5(1 − δ)²/(μ J)`. -/
noncomputable def alphaMax (J δ μ : ℝ) : ℝ := 3 / 2 * (1 - δ) ^ 2 / (μ * J)

/-- The rate `λ`: `(1 − αμ/1.5)^{1/(2B)}` if `α ≤ alphaSplit`, else `(√(αμJ/1.5) + δ)^{1/B}`. -/
noncomputable def rateLam (J δ μ α : ℝ) (B : ℕ) : ℝ :=
  if α ≤ alphaSplit J δ μ then (1 - α * μ / (3 / 2)) ^ ((1 : ℝ) / (2 * (B : ℝ)))
  else (Real.sqrt (α * μ * J / (3 / 2)) + δ) ^ ((1 : ℝ) / (B : ℝ))

/-- Assumption 2 (`B̃`-connected graph sequence), p. 7: `B̃` is a positive integer and the union
graph `G_{B̃}(tB̃) = (V, E(tB̃) ∪ ⋯ ∪ E(tB̃ + B̃ − 1))` is connected for every `t = 0, 1, …`. -/
def Assumption2 {n : ℕ} (E : ℕ → SimpleGraph (Fin n)) (Bt : ℕ) : Prop :=
  0 < Bt ∧ ∀ t : ℕ, (⨆ l ∈ Finset.Ico (t * Bt) ((t + 1) * Bt), E l).Connected

/-- Assumption 3 (Mixing matrix sequence), pp. 7–8, with the constant `τ` of item (iv):
(i) `W(k) 1 = 1`, `1ᵀ W(k) = 1ᵀ`; (ii) `W_ii(k) > 0`; (iii) for `i ≠ j`, `W_ij(k) > 0` if
`(j, i) ∈ E(k)` and `W_ij(k) = 0` otherwise; (iv) `τ > 0` and every positive entry is `≥ τ`. -/
def Assumption3 {n : ℕ} (E : ℕ → SimpleGraph (Fin n)) (W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ) : Prop :=
  (∀ k, W k *ᵥ (fun _ => (1 : ℝ)) = (fun _ => 1) ∧ (fun _ => (1 : ℝ)) ᵥ* W k = (fun _ => 1)) ∧
  (∀ k i, 0 < W k i i) ∧
  (∀ k i j, i ≠ j → ((E k).Adj j i → 0 < W k i j) ∧ (¬ (E k).Adj j i → W k i j = 0)) ∧
  0 < τ ∧ ∀ k i j, 0 < W k i j → τ ≤ W k i j

/-- The step size (46) of Corollary 11, p. 18:
`α(τ) = 3τ²/(128 B² n^{4.5} L √κ̄) − (1.5/μ̄)(τ²/(128 B² n^{4.5} κ̄^{1.5}))²`. -/
noncomputable def alphaTau {n : ℕ} (Lc mu : Fin n → ℝ) (B : ℕ) (τ : ℝ) : ℝ :=
  3 * τ ^ 2 / (128 * (B : ℝ) ^ 2 * (n : ℝ) ^ (4.5 : ℝ) * Lmax Lc * Real.sqrt (kappa Lc mu)) -
    3 / 2 / mubar mu *
      (τ ^ 2 / (128 * (B : ℝ) ^ 2 * (n : ℝ) ^ (4.5 : ℝ) * kappa Lc mu ^ (3 / 2 : ℝ))) ^ 2

/-- The rate of Corollary 11, p. 18: `λ(τ) = (1 − τ²/(128 B² n^{4.5} κ̄^{1.5}))^{1/B}`. -/
noncomputable def lamTau {n : ℕ} (Lc mu : Fin n → ℝ) (B : ℕ) (τ : ℝ) : ℝ :=
  (1 - τ ^ 2 / (128 * (B : ℝ) ^ 2 * (n : ℝ) ^ (4.5 : ℝ) * kappa Lc mu ^ (3 / 2 : ℝ))) ^
    ((1 : ℝ) / (B : ℝ))

end DIGing.Undir


