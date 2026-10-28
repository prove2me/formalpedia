-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirect132Rule
-- name    : TaoFivePrimes_RHDirect132Rule
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:39:47.051294+00:00
-- url     : https://prove2.me/theorems/ec45f9af-26df-4695-b13c-b8c72ffe1dc2
-- title:
--   Fixed-point oscillatory theta quadrature rule at height 132
-- statement:
--   Let $h=3/16$, $c_i=3(2i+1)/16$, let $q_{i,r}$ be the stored rational base theta jet, and let $\phi_i$ be the stored fixed-point phase candidate. Put
--
--   $$
--   P_{i,k,m}=\begin{cases}
--   \dfrac{c_i^{k-m}h^m}{(k-m)!\,m!},&m\le k,\\
--   0,&m>k,
--   \end{cases}\quad
--   E_\ell=\frac{(66ih)^\ell}{\ell!},\quad
--   w_j=\frac{1-(-1)^{j+1}}{j+1}.
--   $$
--
--   For $k\ge0$ define the finite Gaussian-rational convolution
--
--   $$
--   R_k=h\sum_{i=0}^{15}\sum_{j=0}^{183}w_j
--   \sum_{m=0}^{j}P_{i,k,m}
--   \sum_{\ell=0}^{j-m}E_\ell\,\phi_i\,q_{i,j-m-\ell}.
--   $$
--
--   This is an exact finite arithmetic rule. Its accuracy and any consequence for zeta zeros are separate statements.
-- source:
--   Direct oscillatory convolution of the theta-jet and Mellin framework due to sometik179 and Gabewhigham, with separately certified fixed-point phase data at height 132.

/- Finite fixed-point/jet convolution proposed for height 132.
Theta-jet data and underlying Mellin framework are due to sometik179 and
Gabewhigham. No approximation or zero-location assertion is made here. -/
import Definitions.Def_TaoFivePrimes_RHDirectPhase132
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
open Complex Finset

namespace RHDirect132Rule

noncomputable def center (i : ℕ) : ℂ := ((3*(2*(i:ℝ)+1)/16:ℝ):ℂ)

noncomputable def powerJet (i k m : ℕ) : ℂ :=
  if m≤k then (center i)^(k-m)*(3/16:ℂ)^m/
    (((k-m).factorial:ℂ)*(m.factorial:ℂ)) else 0

noncomputable def phaseJet (m : ℕ) : ℂ :=
  (Complex.I*(66:ℂ)*(3/16:ℂ))^m/(m.factorial:ℂ)

noncomputable def baseJet (i j : ℕ) : ℂ := ((RHNextMomentRule.jet i j:ℚ):ℂ)

noncomputable def weight (j : ℕ) : ℂ := (1-(-1:ℂ)^(j+1))/(j+1)

noncomputable def panel (i k : ℕ) : ℂ :=
  (3/16:ℂ) * ∑ j ∈ range 184, weight j *
    ∑ m ∈ range (j+1), powerJet i k m *
      ∑ l ∈ range (j-m+1), phaseJet l *
        (RHDirectPhase132.asComplex (RHDirectPhase132.panels i) * baseJet i (j-m-l))

noncomputable def rule (k : ℕ) : ℂ := ∑ i ∈ range 16, panel i k

end RHDirect132Rule


