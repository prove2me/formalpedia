-- Prove2me | Definitions.Def_SubsetShrink_LowerBound_Model
-- name    : SubsetShrink_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:59.29192+00:00
-- url     : https://prove2.me/theorems/a2b94031-bb28-428d-833b-2a2e99dd307c
-- title:
--   (1), p. 2; §3.1, pp. 12–13; B.9, p. 44 — norms, supports, B0(s), γ_s, the Gaussian noise law, the best-subsets estimator, G and H
-- statement:
--   This module fixes the objects of the paper's lower bound for best subset selection.
--
--   Vectors live in $\mathbb R^m$, written as functions on $\{0,\dots,m-1\}$ (coordinate $j$ of the paper is index $j-1$).
--
--   1. **Norms and supports.** $\|v\|=\sqrt{\sum_i v_i^2}$ (Euclidean), $\|v\|_1=\sum_i|v_i|$, $\operatorname{supp}(v)=\{i: v_i\neq0\}$, $\|v\|_0=|\operatorname{supp}(v)|$, the inner product $v^\top w=\sum_i v_iw_i$, and the $\ell_0$ ball $B_0(s)=\{u\in\mathbb R^p:\|u\|_0\le s\}$.
--   2. **Design.** A real $n\times p$ matrix $X$ has *unit columns* when $\sum_i X_{ij}^2=1$ for every column $j$.
--   3. **Minimal sparse eigenvalue** (p. 13):
--   $$
--   \gamma_s=\min_{u\neq 0,\ u\in B_0(s)}\frac{\|Xu\|}{\|u\|}.
--   $$
--   4. **Noise law.** The law of $\epsilon\in\mathbb R^n$ with independent $N(0,\sigma^2)$ entries, the $n$-fold product of the centred Gaussian of variance $\sigma^2$.
--   5. **Best subsets** (1): $\hat\beta$ is a best-subsets solution for the response $y$ and model size $k$ when $\|\hat\beta\|_0\le k$ and $\|y-X\hat\beta\|^2\le\|y-X\beta\|^2$ for every $\beta$ with $\|\beta\|_0\le k$.
--   6. **Restriction** (p. 44): for an index set $I$, $\beta_I$ agrees with $\beta$ on $I$ and vanishes off $I$.
--   7. **The functions of the proof of Theorem 4** (p. 44): for a reference vector $\tilde\beta$ and $w\in\mathbb R^n$,
--   $$
--   G(\beta)=\|y-X\beta\|^2-\|y-X\tilde\beta\|^2,\qquad H(u)=\|Xu\|^2-2\,w^\top Xu .
--   $$
--   In the paper $\tilde\beta=\tilde\beta^*$ and $w=\Delta^*+\epsilon$ with $\Delta^*=X\beta^*-X\tilde\beta^*$.
--
--   These are the model of §3.1 (y = Xβ* + ε with Gaussian noise and a deterministic design with unit columns), the estimator whose prediction error Theorem 4 bounds from below, and the two auxiliary functions on which its proof runs.
--
--   **Formalization Note** Mathlib's norm on `Fin m → ℝ` is the sup norm, so the Euclidean and $\ell_1$ norms are explicit definitions. $\gamma_s$ is an infimum over the subtype of nonzero vectors with $\|u\|_0\le s$; this set is nonempty when $p\ge1$ and $s\ge1$ and every ratio is $\ge0$, so the infimum is the paper's minimum value there (the minimum is attained since the ratio is scale invariant and continuous on each coordinate sphere). Best subsets is an argmin *predicate*: no minimizer is chosen and none is assumed to exist. The objective is $\|y-X\beta\|^2$ without a factor $\tfrac12$, as in (1) and (16).
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 2, (1); pp. 12–13, §3.1, (15), B0(s) and γ_s; p. 44, proof of Theorem 4 (B.9), G(β), H(u) and β_I

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model
import Definitions.Def_SubsetShrink_L2_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.LowerBound

/-- Support `supp(v) = {i : vᵢ ≠ 0}` (indices are 0-based: coordinate `j` of the paper is `j.val + 1`). -/
noncomputable def supp {m : ℕ} (v : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => v i ≠ 0)

/-- `‖v‖₀`, the number of nonzero coordinates. -/
noncomputable def l0 {m : ℕ} (v : Fin m → ℝ) : ℕ := (supp v).card

/-- The `ℓ₀` ball `B0(s) = {u ∈ ℝ^p : ‖u‖₀ ≤ s}`. -/
def B0 (p s : ℕ) : Set (Fin p → ℝ) := {u | l0 u ≤ s}

/-- `βhat` is a best-subsets solution (1): it minimizes `‖y − Xβ‖²` subject to `‖β‖₀ ≤ k`. -/
def IsBestSubset {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (k : ℕ)
    (βhat : Fin p → ℝ) : Prop :=
  l0 βhat ≤ k ∧ ∀ β : Fin p → ℝ, l0 β ≤ k →
    ∑ i, (y i - X.mulVec βhat i) ^ 2 ≤ ∑ i, (y i - X.mulVec β i) ^ 2

/-- `β_I`: agrees with `β` on `I` and vanishes off `I`. -/
noncomputable def restrict {p : ℕ} (β : Fin p → ℝ) (I : Finset (Fin p)) : Fin p → ℝ :=
  fun j => if j ∈ I then β j else 0

/-- `G(β) = ‖y − Xβ‖² − ‖y − Xβ̃‖²` (proof of Theorem 4, p. 44), with reference vector `βt = β̃*`. -/
noncomputable def Gfun {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (βt β : Fin p → ℝ) : ℝ :=
  ∑ i, (y i - X.mulVec β i) ^ 2 - ∑ i, (y i - X.mulVec βt i) ^ 2

/-- `H(u) = ‖Xu‖² − 2 w⊤Xu` (proof of Theorem 4, p. 44), with `w = Δ* + ε`. -/
noncomputable def Hfun {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ)
    (u : Fin p → ℝ) : ℝ :=
  ∑ i, X.mulVec u i ^ 2 - 2 * SubsetShrink.Events.dot w (X.mulVec u)

end SubsetShrink.LowerBound


