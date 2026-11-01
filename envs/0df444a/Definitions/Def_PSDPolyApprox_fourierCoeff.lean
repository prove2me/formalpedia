-- Prove2me | Definitions.Def_PSDPolyApprox_fourierCoeff
-- name    : PSDPolyApprox_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:48.751071+00:00
-- url     : https://prove2.me/theorems/f2af7305-56ad-4e3c-ae74-e9abc96668bc
-- title:
--   Fourier coefficient $\hat f(S)=\mathbb E[f\chi_S]$
-- statement:
--   For $f:H_n\to\mathbb R$ and $S\subseteq\{1,\dots,n\}$, the **Fourier coefficient**
--   $$
--   \hat f(S)=\mathbb E[f\,\chi_S]=\frac1{2^n}\sum_{x\in H_n}f(x)\chi_S(x).
--   $$
--   The Fourier expansion $f=f_0+f_1+\dots+f_n$ of the paper has degree-$i$ part $f_i=\sum_{|S|=i}\hat f(S)\chi_S$.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_expect
import Definitions.Def_PSDPolyApprox_chi

namespace PSDPolyApprox

/-- **Fourier coefficient** `f̂(S) = E[f χ_S]` of `f : Hₙ → ℝ`.
Fawzi, arXiv:1811.09649v1, §2.1, p.3 ("Any function f : Hn → R has a Fourier expansion
f = f0 + f1 + · · · + fn"); the degree-`i` part is `fᵢ = ∑_{|S| = i} f̂(S) χ_S`. -/
noncomputable def fourierCoeff {n : ℕ} (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  expect (fun x => f x * chi S x)

end PSDPolyApprox


