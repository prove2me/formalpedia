-- Prove2me | Definitions.Def_LL_Decomp587l_buchstabIntegral
-- name    : LL_Decomp587l_buchstabIntegral
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-18T01:23:37.01635+00:00
-- url     : https://prove2.me/theorems/9d2920a9-14bf-4a9d-8ba8-42308fc08ba9
-- title:
--   The Buchstab integral over an ordered box
-- statement:
--   For $\omega:\mathbb R\to\mathbb R$, $n\in\mathbb N$, vectors $\ell,h\in\mathbb R^{n+2}$ with coordinates indexed by $0,\dots,n+1$, and $\varphi\in\mathbb R$, the real number $\int_D \omega\bigl((\varphi-\sum_j x_j)/x_n\bigr)\,\bigl((\prod_j x_j)\,x_n\bigr)^{-1}\,dx$, the integral with respect to Lebesgue measure on $\mathbb R^{n+2}$ over the set $D$ of monotone $x$ with $\ell_j\le x_j\le h_j$ for all $j$. Here $x_n$ is the penultimate coordinate, so it appears squared in the denominator. As for every Bochner integral, the value is $0$ if the integrand is not integrable on $D$.

import Mathlib
import Definitions.Def_LL_Decomp587l_domain

open Real Set MeasureTheory
open scoped Classical

namespace LL_Decomp587l

noncomputable section

def buchstabIntegral (ω : ℝ → ℝ) (n : ℕ) (lo hi : Fin (n + 2) → ℝ) (φ : ℝ) : ℝ :=
  ∫ x in domain lo hi,
    ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) / ((∏ j, x j) * x ⟨n, by omega⟩)

end

end LL_Decomp587l


