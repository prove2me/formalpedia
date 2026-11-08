-- Prove2me | Definitions.Def_KhintchineTwoRegime_kappa
-- name    : KhintchineTwoRegime_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:38.798116+00:00
-- url     : https://prove2.me/theorems/b42d59f3-d27b-4bda-8378-7b6fdc3aae87
-- title:
--   $\kappa(c;y)=\mathbb E|c\epsilon_0+\sum_j y_j\epsilon_j|$ (Definition 1)
-- statement:
--   For $c\in\mathbb R$ and $y=(y_1,\dots,y_k)\in\mathbb R^k$,
--   $$
--   \kappa(c;y)=\mathbb E\Bigl|c\,\epsilon_0+\sum_{j=1}^k y_j\epsilon_j\Bigr|,
--   $$
--   where $\epsilon_0,\epsilon_1,\dots,\epsilon_k$ are independent Rademacher random variables; that is, $\kappa(c;y)=K_{k+1}(c,y_1,\dots,y_k)$. It is the building block of the four-coordinate decomposition (Lemma 4).
--
--   **Formalization Note** Defined as `K (k+1)` of the vector whose first coordinate is $c$ followed by $y$ (`Fin.cons`).
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Definition 1, p.7

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K

namespace KhintchineTwoRegime

/-- `κ(c; y) = E|cε₀ + ∑_{j=1}^k yⱼ εⱼ|` for independent Rademacher signs `ε₀, …, ε_k`
(Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Definition 1, p.7).

**Formalization Note** `κ(c; y) = K_{k+1}(c, y₁, …, y_k)`: the coefficient `c` of `ε₀` is
the head of `Fin.cons c y`. -/
noncomputable def kappa {k : ℕ} (c : ℝ) (y : Fin k → ℝ) : ℝ :=
  K (k + 1) (Fin.cons c y : Fin (k + 1) → ℝ)

end KhintchineTwoRegime


