-- Prove2me | Definitions.Def_KhintchineTwoRegime_Supplement_lowDegWeight
-- name    : KhintchineTwoRegime_Supplement_lowDegWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:24:49.840344+00:00
-- url     : https://prove2.me/theorems/fcadc986-f916-4ec8-8927-c79d1ceec25e
-- title:
--   Low-degree Fourier weight $W^{\le1}(h)=\sum_{|S|\le1}\hat h(S)^2$
-- statement:
--   For $h:\{-1,1\}^n\to\mathbb R$, the **low-degree Fourier weight** is
--   $$
--   W^{\le1}(h)=\sum_{S\subseteq[n],\ |S|\le1}\hat h(S)^2=\hat h(\emptyset)^2+\sum_{i=1}^n\hat h(\{i\})^2 ,
--   $$
--   the squared $L^2(\mu_n)$ norm of the degree-$\le1$ part $h^{\le1}=\sum_{|S|\le1}\hat h(S)x_S$. It includes the degree-0 term $\hat h(\emptyset)^2$; for a Boolean function it lies in $[0,1]$.
--
--   **Formalization Note** The sum runs over all `S : Finset (Fin n)` with at most one element.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Supplement_fourierCoeff

namespace KhintchineTwoRegime.Supplement

/-- The low-degree Fourier weight `W≤1(h) = ∑_{S ⊆ [n], |S| ≤ 1} ĥ(S)²`
(Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), §4, p.10), i.e. `ĥ(∅)² + ∑ᵢ ĥ({i})²`.

**Formalization Note** The sum runs over all `S : Finset (Fin n)` with `S.card ≤ 1`; it
includes the degree-0 term `ĥ(∅)²`. -/
noncomputable def lowDegWeight {n : ℕ} (h : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ 1),
    fourierCoeff h S ^ 2

end KhintchineTwoRegime.Supplement


