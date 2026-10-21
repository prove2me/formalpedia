-- Prove2me | Definitions.Def_HiddenIntSDP_OracleBound_Model
-- name    : HiddenIntSDP_OracleBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:17.295082+00:00
-- url     : https://prove2.me/theorems/2563c26d-ebda-49ea-b852-8f99759a478d
-- title:
--   Balanced mixture, SDP (7), and Oracle IP (10)
-- statement:
--   This module defines the balanced sub-Gaussian mixture setting and the two optimization problems compared in Theorem 1. There are $n$ points in $\mathbb R^d$, $k$ clusters with equal cardinality $\ell=n/k$, centers $\mu_a$, labels $\sigma^*(i)$, and realized noises $g_i$. The observed point is $h_i=\mu_{\sigma^*(i)}+g_i$, and the minimum separation is $\Delta=\min_{a\ne b}\|\mu_a-\mu_b\|_2$.
--
--   The SDP (7) minimizes the trace inner product with $A_{ij}=\|h_i-h_j\|_2^2$ over symmetric positive semidefinite matrices $Y$ with diagonal entries one, nonnegative entries, and row sums $n/k$. The true cluster matrix is $Y^*_{ij}=\mathbf1\{\sigma^*(i)=\sigma^*(j)\}$. The Oracle IP uses all zero-one assignment matrices $F$ with one one per row. With $\kappa=1/8$ and $\bar h_j=\mu_{\sigma^*(j)}+(2\kappa)^{-1}g_j$, its objective is
--
--   $$
--   \eta(F)=\sum_{j=1}^n\sum_{a=1}^k\|\bar h_j-\mu_a\|_2^2F_{ja}.
--   $$
--
--   The module also defines the true assignment $F^*$, the matrix trace inner product, and the entrywise $\ell_1$ norm. These objects are shared by every theorem in the mission.
--
--   **Formalization Note** Indices are zero-based in Lean. The Oracle assignments are not required to be balanced. The minimum separation is used when $k\ge2$, so its index set is nonempty.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, pp. 5–10, §3.1–§4.1, Model 1, (4), (7), (10)–(12)

import Mathlib

namespace HiddenIntSDP.OracleBound

/-- Equal cluster sizes, stated without truncated natural-number division. -/
def Balanced (n k : ℕ) (sig : Fin n → Fin k) : Prop :=
  ∀ a : Fin k, (Finset.univ.filter (fun i => sig i = a)).card * k = n

/-- The minimum separation of distinct centers. It is used only when `2 ≤ k`. -/
noncomputable def minSep {k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨅ p : {p : Fin k × Fin k // p.1 ≠ p.2}, ‖mu p.1.1 - mu p.1.2‖

/-- Squared pairwise distances in the observed sample. -/
noncomputable def distMat {n d : ℕ} (h : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ‖h i - h j‖ ^ 2

/-- The trace inner product, equal to `Tr(MᵀQ)`. -/
def frob {m p : ℕ} (M Q : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * Q i j

/-- Entrywise ℓ₁ norm of a matrix. -/
def l1 {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, |M i j|

/-- Feasible region of the SDP (7). -/
def SDPFeasible (n k : ℕ) (Y : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Y.mulVec (fun _ => 1) = (fun _ => (n : ℝ) / k) ∧
  (∀ i, Y i i = 1) ∧ Y.PosSemidef ∧ ∀ i j, 0 ≤ Y i j

/-- An optimum of the SDP (7). -/
def IsSDPOpt (n k : ℕ) (A Y : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  SDPFeasible n k Y ∧ ∀ Y', SDPFeasible n k Y' → frob Y A ≤ frob Y' A

/-- The ground-truth cluster matrix. -/
def Ystar {n k : ℕ} (sig : Fin n → Fin k) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if sig i = sig j then 1 else 0

/-- Assignment matrices in the Oracle IP have exactly one 1 in each row. -/
def IsAssignment {n k : ℕ} (F : Matrix (Fin n) (Fin k) ℝ) : Prop :=
  (∀ j a, F j a = 0 ∨ F j a = 1) ∧ ∀ j, ∑ a, F j a = 1

/-- True assignment matrix. -/
def Fstar {n k : ℕ} (sig : Fin n → Fin k) : Matrix (Fin n) (Fin k) ℝ :=
  fun j a => if sig j = a then 1 else 0

/-- The fixed constant in the paper's augmented-noise Oracle IP. -/
noncomputable def kappa : ℝ := 1 / 8

/-- Oracle observation with the same noise realization as the SDP data. -/
noncomputable def hbar {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (j : Fin n) : EuclideanSpace ℝ (Fin d) :=
  mu (sig j) + (2 * kappa)⁻¹ • g j

/-- The Oracle IP objective (10). -/
noncomputable def eta {n k d : ℕ} (mu : Fin k → EuclideanSpace ℝ (Fin d))
    (sig : Fin n → Fin k) (g : Fin n → EuclideanSpace ℝ (Fin d))
    (F : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∑ j, ∑ a, ‖hbar mu sig g j - mu a‖ ^ 2 * F j a

end HiddenIntSDP.OracleBound


