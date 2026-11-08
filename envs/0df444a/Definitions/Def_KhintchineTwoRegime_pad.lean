-- Prove2me | Definitions.Def_KhintchineTwoRegime_pad
-- name    : KhintchineTwoRegime_pad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:47.086047+00:00
-- url     : https://prove2.me/theorems/9e9b593b-f7b6-4acf-8d8f-37230134af4e
-- title:
--   Coordinate with zero padding
-- statement:
--   For $\omega\in\mathbb R^n$ and an index $i\ge0$, the padded coordinate is $\omega_{i+1}$ if $i<n$ and $0$ otherwise. It formalizes the paper's phrase "adding a zero coordinate if necessary" (Lemma 2, Corollary 1), so that $a=\omega_1$ and $b=\omega_2$ make sense in every dimension.
--
--   **Formalization Note** Indices are 0-based: `pad ω 0` is the paper's $\omega_1$ and `pad ω 1` is $\omega_2$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 2 and Corollary 1, p.6

import Mathlib

namespace KhintchineTwoRegime

/-- The `i`-th coordinate of `ω ∈ ℝⁿ` (0-based), with `0` beyond the last coordinate: the
paper's "adding a zero coordinate if necessary" (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 2 and Corollary 1, p.6).

**Formalization Note** `pad ω 0` and `pad ω 1` are the paper's `ω₁` and `ω₂`. -/
def pad {n : ℕ} (ω : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then ω ⟨i, h⟩ else 0

end KhintchineTwoRegime


