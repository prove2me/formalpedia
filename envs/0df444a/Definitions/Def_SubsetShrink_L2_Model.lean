-- Prove2me | Definitions.Def_SubsetShrink_L2_Model
-- name    : SubsetShrink_L2_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:30:44.295696+00:00
-- url     : https://prove2.me/theorems/db0f43da-5b55-4bfe-8146-72463dbf6210
-- title:
--   §3.1, (15)–(16), pp. 12–13 — norms, B0(s), γ_s, the events E_s, F, G_s, and the ℓ2-regularized best-subsets estimator
-- statement:
--   Fix a design matrix $X\in\mathbb R^{n\times p}$, a mean vector $f^*\in\mathbb R^n$ and a noise vector $\epsilon\in\mathbb R^n$; the data are $y=f^*+\epsilon$. This file defines the objects used throughout §3 of the paper.
--
--   1. The Euclidean norm $\|v\|=\big(\sum_i v_i^2\big)^{1/2}$, the support size $\|v\|_0=\#\{i: v_i\neq 0\}$, the inner product $a^\top b=\sum_i a_ib_i$, the sparse class $B_0(s)=\{u\in\mathbb R^p:\|u\|_0\le s\}$, the residual $f^*-X\beta$, and the property that every column of $X$ has unit Euclidean norm.
--   2. The minimal $s$-sparse eigenvalue
--   $$\gamma_s=\min_{u\neq 0,\ u\in B_0(s)}\frac{\|Xu\|}{\|u\|}.$$
--   3. The weighted sorted sum $\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)}$, where $u^\sharp_1\ge\dots\ge u^\sharp_p$ is the non-increasing rearrangement of $|u_1|,\dots,|u_p|$.
--   4. For $\sigma>0$, $\delta_0\in(0,1]$ and an integer $s$, the noise events of p. 13:
--   $$\mathcal E_s=\big\{\epsilon^\top Xu\le[4+\sqrt2]\,\sigma\sqrt{s\log(2ep/s)}\,\|u\|\ \ \forall u\in B_0(s)\big\},$$
--   $$\mathcal F=\Big\{\epsilon^\top Xu\le[4+\sqrt2]\,\sigma\max\Big(\sum_{j=1}^p u^\sharp_j\sqrt{\log(2p/j)},\ \sqrt{\log(1/\delta_0)}\,\|Xu\|\Big)\ \ \forall u\in\mathbb R^p\Big\},$$
--   $$\mathcal G_s=\big\{\epsilon^\top Xu\le\sigma\sqrt{5s\log(ep/s)+\log(1/\delta_0)}\,\|Xu\|\ \ \forall u\in B_0(s)\big\}.$$
--   5. The $\ell_2$-regularized best-subsets estimator (16) with $q=2$: $\hat\beta_2$ is any vector with $\|\hat\beta_2\|_0\le k$ that minimizes
--   $$\|y-X\beta\|^2+\lambda\|\beta\|\qquad\text{subject to }\|\beta\|_0\le k.$$
--
--   These definitions are the common model of Theorem 2 and of every step of its proof.
--
--   **Formalization Note** Vectors are functions on `Fin m`, with 0-based indices; the paper's index $j$ is `j.val + 1`. The norms are explicit sums because Mathlib's norm on `Fin m → ℝ` is the sup norm. The sorted sum is encoded as the maximum over permutations $\pi$ of $\sum_j|u_{\pi(j)}|\sqrt{\log(2p/j)}$; since these weights are non-increasing in $j$ and nonnegative for $j\le p$, the rearrangement inequality makes it equal to the sum with $u^\sharp$. $\gamma_s$ is a real infimum over the nonzero vectors of $B_0(s)$; for $p\ge1$, $s\ge1$ that set is nonempty and every ratio is $\ge0$, so the infimum is the paper's minimum. The events are sets of noise vectors defined by the printed inequalities; $\mathcal G_s$ is the printed event (not mission II's corrected one), which is all the deterministic statements here need. The estimator is a predicate satisfied by every minimizer; its objective has no factor $1/2$, exactly as in (16), and its penalty is $\|\beta\|$, not $\|\beta\|^2$. The noise law is not needed: every statement here is deterministic on an event.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, pp. 12–13, (15)–(16), §3.1 (definitions of B0(s), γ_s, u♯ and the events E_s, F, G_s)

import Mathlib

namespace SubsetShrink.L2

/-! The deterministic model of §3.1 (15)–(16), pp. 12–13, of Mazumder, Radchenko & Dedieu,
arXiv:1708.03288v4: explicit Euclidean norm and support size on `Fin m → ℝ`, the sparse
class `B0 s`, the minimal sparse eigenvalue `γ_s`, the noise events `E_s`, `F`, `G_s` of
p. 13 (as printed), and the ℓ2-regularized best-subsets estimator (16) with `q = 2`. -/

/-- Euclidean norm `‖v‖ = √(∑ vᵢ²)`. (Mathlib's `‖·‖` on `Fin m → ℝ` is the sup norm.) -/
noncomputable def l2 {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- Number of nonzero coordinates `‖v‖₀`. -/
noncomputable def l0 {m : ℕ} (v : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- Inner product `a⊤b`. -/
def dot {m : ℕ} (a b : Fin m → ℝ) : ℝ :=
  ∑ i, a i * b i

/-- `B0(s) = {u ∈ ℝᵖ : ‖u‖₀ ≤ s}`. -/
def B0 {p : ℕ} (s : ℕ) : Set (Fin p → ℝ) :=
  {u | l0 u ≤ s}

/-- The columns of `X` have unit Euclidean norm. -/
def UnitCols {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  ∀ j, ∑ i, X i j ^ 2 = 1

/-- The residual `f* − Xβ`. -/
def resid {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ)
    (β : Fin p → ℝ) : Fin n → ℝ :=
  fun i => fstar i - X.mulVec β i

/-- `∑_{j=1}^p u♯_j √log(2p/j)`, encoded as the maximum over permutations `π` of
`∑_j |u_{π(j)}| √log(2p/j)`. The weights decrease in `j` and are `≥ 0` for `j ≤ p`, so by the
rearrangement inequality the maximum is attained at a permutation sorting `|u|`
non-increasingly. Indices are 0-based: `j.val + 1` is the paper's `j`. -/
noncomputable def sortedSum {p : ℕ} (u : Fin p → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun π : Equiv.Perm (Fin p) =>
      ∑ j, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))))

/-- The minimal `s`-sparse eigenvalue `γ_s = min_{u ≠ 0, u ∈ B0(s)} ‖Xu‖/‖u‖`. The index set
is nonempty for `p ≥ 1`, `s ≥ 1`, and every ratio is `≥ 0`, so the real infimum is the
paper's minimum there. -/
noncomputable def gam {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (s : ℕ) : ℝ :=
  ⨅ u : {u : Fin p → ℝ // u ≠ 0 ∧ l0 u ≤ s}, l2 (X.mulVec u.val) / l2 u.val

/-- Event `E_s = {ε⊤Xu ≤ [4 + √2] σ √(s log(2ep/s)) ‖u‖, ∀ u ∈ B0(s)}` (p. 13). -/
def E {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ : ℝ) (s : ℕ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ, l0 u ≤ s →
    dot ε (X.mulVec u) ≤
      (4 + Real.sqrt 2) * σ *
        Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * (p : ℝ) / (s : ℝ))) * l2 u}

/-- Event `F = {ε⊤Xu ≤ [4 + √2] σ max(∑_j u♯_j √log(2p/j), √log(1/δ0) ‖Xu‖), ∀ u ∈ ℝᵖ}`
(p. 13). -/
def F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ,
    dot ε (X.mulVec u) ≤
      (4 + Real.sqrt 2) * σ *
        max (sortedSum u) (Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec u))}

/-- Event `G_s = {ε⊤Xu ≤ σ √(5s log(ep/s) + log(1/δ0)) ‖Xu‖, ∀ u ∈ B0(s)}`, exactly as printed
on p. 13. -/
def G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) (s : ℕ) : Set (Fin n → ℝ) :=
  {ε | ∀ u : Fin p → ℝ, l0 u ≤ s →
    dot ε (X.mulVec u) ≤
      σ * Real.sqrt (5 * (s : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (s : ℝ)) +
        Real.log (1 / δ0)) * l2 (X.mulVec u)}

/-- `βhat` is an ℓ2-regularized best-subsets solution (16) with `q = 2`: it is feasible
(`‖βhat‖₀ ≤ k`) and minimizes `‖y − Xβ‖² + λ‖β‖` over `‖β‖₀ ≤ k`. No factor `1/2`; the
penalty is the Euclidean norm, not its square. -/
def IsL2BestSubset {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (k : ℕ)
    (lam : ℝ) (βhat : Fin p → ℝ) : Prop :=
  l0 βhat ≤ k ∧
    ∀ β : Fin p → ℝ, l0 β ≤ k →
      l2 (fun i => y i - X.mulVec βhat i) ^ 2 + lam * l2 βhat ≤
        l2 (fun i => y i - X.mulVec β i) ^ 2 + lam * l2 β

end SubsetShrink.L2


