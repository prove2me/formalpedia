-- Prove2me | Definitions.Def_PSDPolyApprox_noise
-- name    : PSDPolyApprox_noise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:51:38.504254+00:00
-- url     : https://prove2.me/theorems/60fb8fad-e309-4709-bf9a-75b8f2e8ad11
-- title:
--   The noise operator $T_\rho f=\sum_i\rho^i f_i$
-- statement:
--   The **noise (smoothing) operator** $T_\rho$ multiplies the degree-$i$ Fourier part of $f:H_n\to\mathbb R$ by $\rho^i$:
--   $$
--   T_\rho f=f_0+\rho f_1+\rho^2f_2+\dots+\rho^nf_n=\sum_{S\subseteq\{1,\dots,n\}}\rho^{|S|}\hat f(S)\chi_S .
--   $$
--   For $\rho=0$, $T_\rho f$ is the constant $\mathbb E[f]$; for $\rho=1$, $T_\rho f=f$. It is the operator to which hypercontractivity (Theorem 3) applies.
--
--   **Formalization Note** The paper introduces $T_\rho$ for $\rho\in[0,1]$. The formula above is used for every real $\rho$ and agrees with the paper's operator on $[0,1]$; this gives a meaning to Lemma 1, whose $\rho=\sqrt{5/n}$ exceeds $1$ when $n<5$.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib
import Definitions.Def_PSDPolyApprox_fourierCoeff

namespace PSDPolyApprox

/-- **The noise (smoothing) operator `T_ρ`.**
Fawzi, arXiv:1811.09649v1, §2.1, p.3: "Given ρ ∈ [0, 1] the noise (or smoothing) operator Tρ
acts on a function f : Hn → R by multiplying the i'th Fourier term by ρi, namely:
Tρf = f0 + ρf1 + ρ2f2 + · · · + ρnfn."

`noise ρ f x = ∑_{S ⊆ [n]} ρ^{|S|} f̂(S) χ_S(x)`, which is `∑ᵢ ρⁱ fᵢ(x)` since
`fᵢ = ∑_{|S| = i} f̂(S) χ_S`.

**Formalization Note.** The Fourier formula is used for **every real** `ρ`, not only
`ρ ∈ [0, 1]`; on `[0, 1]` it is the paper's operator. This makes Lemma 1 (with `ρ = √(5/n)`,
which exceeds `1` for `n < 5`) meaningful for every `n`. `0 ^ 0 = 1`, so `noise 0 f` is the
constant `E[f]`. -/
noncomputable def noise {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) : Cube n → ℝ :=
  fun x => ∑ S : Finset (Fin n), ρ ^ S.card * fourierCoeff f S * chi S x

end PSDPolyApprox


