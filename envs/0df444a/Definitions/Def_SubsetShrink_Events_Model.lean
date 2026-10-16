-- Prove2me | Definitions.Def_SubsetShrink_Events_Model
-- name    : SubsetShrink_Events_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:30:42.821428+00:00
-- url     : https://prove2.me/theorems/190d4bd3-dc4e-475c-ae51-4630c66a3439
-- title:
--   §3.1, (15), p. 12–13 — norms, B₀(s), Gaussian noise law, sorted sum, and the events 𝓔_s, 𝓕, 𝓖_s (printed and corrected), 𝓗
-- statement:
--   Fix integers $n, p \ge 0$ and a deterministic design matrix $X \in \mathbb R^{n\times p}$. The data follow the model $y = f^* + \epsilon$ (15), where $f^*\in\mathbb R^n$ is a deterministic mean and the noise $\epsilon\in\mathbb R^n$ has independent $N(0,\sigma^2)$ coordinates. This file sets up the objects in terms of which the paper's error bounds are proved.
--
--   1. **Norms.** For $v \in \mathbb R^m$: the Euclidean norm $\|v\| = (\sum_i v_i^2)^{1/2}$, $\|v\|_1 = \sum_i |v_i|$, $\|v\|_\infty = \max_i |v_i|$, and $\|v\|_0$, the number of non-zero coordinates. $B_0(s) = \{u\in\mathbb R^p : \|u\|_0 \le s\}$, and $a^\top b = \sum_i a_i b_i$.
--   2. **Unit columns.** $X$ has columns of unit Euclidean norm: $\sum_i X_{ij}^2 = 1$ for every $j$.
--   3. **Noise law.** The law of $\epsilon$ is the product measure $N(0,\sigma^2)^{\otimes n}$ on $\mathbb R^n$.
--   4. **Sorted sum.** For $u \in \mathbb R^p$ let $u^\sharp_1 \ge \dots \ge u^\sharp_p$ be the non-increasing rearrangement of $|u_1|,\dots,|u_p|$; the sorted sum is
--   $$\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)} .$$
--   5. **Events** (p. 13), for $s\in\mathbb N$ and $\delta_0 \in (0,1]$, as sets of noise vectors $\epsilon$:
--   $$\mathcal E_s = \bigl\{\epsilon^\top X u \le [4+\sqrt2]\,\sigma\sqrt{s\log(2ep/s)}\,\|u\|,\ \forall u\in B_0(s)\bigr\},$$
--   $$\mathcal F = \Bigl\{\epsilon^\top X u \le [4+\sqrt2]\,\sigma\max\Bigl(\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)},\ \sqrt{\log(1/\delta_0)}\,\|Xu\|\Bigr),\ \forall u\in\mathbb R^p\Bigr\},$$
--   $$\mathcal G_s = \bigl\{\epsilon^\top X u \le \sigma\sqrt{5s\log(ep/s)+\log(1/\delta_0)}\,\|Xu\|,\ \forall u\in B_0(s)\bigr\}\quad\text{(as printed)},$$
--   $$\mathcal G'_s = \bigl\{\epsilon^\top X u \le \sigma\sqrt{5s\log(ep/s)+3\log(1/\delta_0)}\,\|Xu\|,\ \forall u\in B_0(s)\bigr\}\quad\text{(corrected)},$$
--   $$\mathcal H = \bigl\{\|X^\top\epsilon\|_\infty \le \sigma\sqrt{2\log(2p)}+\sigma\sqrt{2\log(1/\delta_0)}\bigr\}.$$
--
--   These are the random events on which all deterministic error bounds of §3 (Theorems 2–5) are proved; Theorem 1 says each holds with high probability.
--
--   **Formalization Note** Vectors are functions `Fin m → ℝ`, and the norms are explicit definitions because Mathlib's norm on `Fin m → ℝ` is the sup norm. Indices are 0-based: `j : Fin p` stands for the paper's index $j+1$. The sorted sum is encoded as the maximum over all permutations $\pi$ of $\sum_j |u_{\pi(j)}|\sqrt{\log(2p/j)}$; since the weights $\sqrt{\log(2p/j)}$ are non-negative and non-increasing for $j\le p$, the rearrangement inequality makes this equal to the paper's $\sum_j u^\sharp_j\sqrt{\log(2p/j)}$. Logarithms are natural and $e = \exp(1)$. Both $\mathcal G_s$ as printed (`G`) and the corrected $\mathcal G'_s$ (`Gc`) are defined: the printed bound $\mathbb P(\mathcal G_s)\ge 1-\delta_0$ of Theorem 1 is false (see `theorem_1`), and the mission's statements use `Gc`.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, pp. 12–13, (15), §3.1 notation, events E_s, F, G_s, H (p. 13)

import Mathlib

namespace SubsetShrink.Events

open MeasureTheory ProbabilityTheory

/-- The Euclidean norm `‖v‖ = √(∑ᵢ vᵢ²)` of a vector `v ∈ ℝᵐ` (p. 12: `‖·‖` is `‖·‖₂`).
Mathlib's `‖·‖` on `Fin m → ℝ` is the sup norm, so the norm is defined explicitly. -/
noncomputable def l2 {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The `ℓ₁` norm `‖v‖₁ = ∑ᵢ |vᵢ|`. -/
noncomputable def l1 {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ∑ i, |v i|

/-- The `ℓ∞` norm `‖v‖_∞ = maxᵢ |vᵢ|` (a finite supremum; it is `0` for `m = 0`). -/
noncomputable def lInf {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ⨆ i, |v i|

/-- The `ℓ₀` "norm" `‖v‖₀`, the number of non-zero coordinates of `v`. -/
noncomputable def l0 {m : ℕ} (v : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- `B₀(s) = {u ∈ ℝᵖ : ‖u‖₀ ≤ s}` (p. 13). -/
def B0 (p s : ℕ) : Set (Fin p → ℝ) :=
  {u | l0 u ≤ s}

/-- The inner product `a⊤b = ∑ᵢ aᵢ bᵢ` in `ℝⁿ`. -/
def dot {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  ∑ i, a i * b i

/-- The columns of the design `X ∈ ℝ^{n×p}` have unit Euclidean norm (§3.1, p. 12). -/
def UnitCols {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  ∀ j, ∑ i, X i j ^ 2 = 1

/-- The law of the noise vector `ϵ ∈ ℝⁿ` in the model `y = f* + ϵ` (15): independent
`N(0, σ²)` coordinates, i.e. the product of `n` centred Gaussian laws with variance `σ²`. -/
noncomputable def noiseLaw (n : ℕ) (σ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)

/-- The sorted weighted sum `∑_{j=1}^p u♯_j √log(2p/j)` of p. 13, where `u♯` is the
non-increasing rearrangement of `|u₁|, …, |u_p|`. It is encoded as the maximum over all
permutations `π` of `∑_j |u_{π(j)}| √log(2p/j)`: the weights `√log(2p/j)` are non-negative and
non-increasing in `j ∈ [p]`, so by the rearrangement inequality the maximum is attained by a
permutation that lists `|u|` in non-increasing order. Indices are 0-based: `j : Fin p` stands
for the paper's index `j.val + 1`. -/
noncomputable def sortedSum {p : ℕ} (u : Fin p → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun π : Equiv.Perm (Fin p) =>
    ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))))

/-- The event `𝓔_s = {ϵ⊤Xu ≤ [4 + √2] σ √(s log(2ep/s)) ‖u‖, ∀u ∈ B₀(s)}` (p. 13), as a set of
noise vectors `ϵ`. -/
def E {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ : ℝ) (s : ℕ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ, l0 u ≤ s →
    dot ε (X.mulVec u) ≤ (4 + Real.sqrt 2) * σ *
      Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u}

/-- The event
`𝓕 = {ϵ⊤Xu ≤ [4 + √2] σ max(∑_{j=1}^p u♯_j √log(2p/j), √log(1/δ₀) ‖Xu‖), ∀u ∈ ℝᵖ}` (p. 13). -/
def F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ,
    dot ε (X.mulVec u) ≤ (4 + Real.sqrt 2) * σ *
      max (sortedSum u) (Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))}

/-- The event `𝓖_s` **as printed** on p. 13:
`𝓖_s = {ϵ⊤Xu ≤ σ √(5s log(ep/s) + log(1/δ₀)) ‖Xu‖, ∀u ∈ B₀(s)}`.
The printed bound `P(𝓖_s) ≥ 1 − δ₀` of Theorem 1 is false for this event (n = p = s = 1,
δ₀ ≤ e⁻⁹); see `Gc` for the corrected event. -/
def G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) (s : ℕ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ, l0 u ≤ s →
    dot ε (X.mulVec u) ≤ σ *
      Real.sqrt (5 * (s : ℝ) * Real.log (Real.exp 1 * p / s) + Real.log (1 / δ0)) *
        l2 (X.mulVec u)}

/-- The **corrected** event `𝓖'_s`: the printed `𝓖_s` of p. 13 with `3 log(1/δ₀)` in place of
`log(1/δ₀)` under the root:
`𝓖'_s = {ϵ⊤Xu ≤ σ √(5s log(ep/s) + 3 log(1/δ₀)) ‖Xu‖, ∀u ∈ B₀(s)}`. It contains `G`. -/
def Gc {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) (s : ℕ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ, l0 u ≤ s →
    dot ε (X.mulVec u) ≤ σ *
      Real.sqrt (5 * (s : ℝ) * Real.log (Real.exp 1 * p / s) + 3 * Real.log (1 / δ0)) *
        l2 (X.mulVec u)}

/-- The event `𝓗 = {‖X⊤ϵ‖_∞ ≤ σ √(2 log(2p)) + σ √(2 log(1/δ₀))}` (p. 13). -/
def H {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) : Set (Fin n → ℝ) :=
  {ε | lInf (X.transpose.mulVec ε) ≤
    σ * Real.sqrt (2 * Real.log (2 * p)) + σ * Real.sqrt (2 * Real.log (1 / δ0))}

end SubsetShrink.Events


