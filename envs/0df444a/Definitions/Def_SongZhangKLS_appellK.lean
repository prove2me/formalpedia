-- Prove2me | Definitions.Def_SongZhangKLS_appellK
-- name    : SongZhangKLS_appellK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:07:23.165245+00:00
-- url     : https://prove2.me/theorems/138713f2-033a-451a-86c5-f0fe1a31c66a
-- title:
--   Polynomial variance coefficients $K_k(\mu)$ and $c_k(\mu)=\sqrt{K_k(\mu)}/k!$
-- statement:
--   For $k\ge1$ and a probability measure $\mu$ on $\mathbb R^n$ with finite moments through order $2k$,
--   $$K_k(\mu)=\sup_{\substack{T\text{ symmetric}\\\|T\|_{HS}=1}}\mathrm{Var}_\mu\big[P_k^\mu[T]\big],\qquad c_k(\mu)=\frac{\sqrt{K_k(\mu)}}{k!}.$$
--
--   By homogeneity, $\mathrm{Var}_\mu[P_k^\mu[T]]\le K_k(\mu)\|T\|_{HS}^2$ for every symmetric $T$. Bounds on $c_k$ are the input of the paper's curvature comparison (Theorem 5.1) and its output for isotropic log-concave measures (Theorem 4.1).
--
--   **Formalization Note** Both quantities lie in $[0,\infty]$ and the variance is `evariance`, so neither an unbounded family nor a function outside $L^2$ produces a junk value.
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), §4, p.21 (definitions of $K_k(\mu)$ and $c_k(\mu)$)

import Mathlib
import Definitions.Def_SongZhangKLS_appellPoly

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace SongZhangKLS

variable {n : ℕ}

/-- The **Appell variance constant**
`K_k(µ) = sup_{T symmetric, ‖T‖_HS = 1} Var_µ[P_k^µ[T]]` (Song, Zhang, *An O(1) Bound for the KLS
Constant*, arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c, §4, p.21).

**Formalization Note.** Computed in `ℝ≥0∞` with `evariance`, so neither an unbounded family nor a
function outside `L²` produces a junk value. The paper defines `K_k(µ)` for `k ≥ 1` and `µ` with
finite moments through order `2k`; statements using it carry these hypotheses. -/
def appellK (μ : Measure (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (T : (Fin k → Fin n) → ℝ) (_ : IsSymmetricTensor T ∧ hsNorm T = 1),
    evariance (polyEval (appellPoly μ k T)) μ

/-- The **polynomial variance coefficient** `c_k(µ) = √K_k(µ) / k!` (Song, Zhang,
arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c, §4, p.21), in `ℝ≥0∞`. -/
def appellC (μ : Measure (EuclideanSpace ℝ (Fin n))) (k : ℕ) : ℝ≥0∞ :=
  appellK μ k ^ ((1 : ℝ) / 2) / (Nat.factorial k : ℝ≥0∞)

end SongZhangKLS


