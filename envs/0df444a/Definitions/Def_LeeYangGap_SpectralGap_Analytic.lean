-- Prove2me | Definitions.Def_LeeYangGap_SpectralGap_Analytic
-- name    : LeeYangGap_SpectralGap_Analytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:36.369279+00:00
-- url     : https://prove2.me/theorems/fc609c97-289d-46b8-b9c5-1bc18880c687
-- title:
--   Normalized analytic logarithm and its computed Taylor coefficients
-- statement:
--   For the actual Trotter trace polynomial $P(y)=\mathcal Z_\epsilon(y)$, define
--   $$\Phi(y)=\log(P(0))+\int_0^1\frac{\frac{d}{dz}P(zy)|_{z=t}}{P(ty)}\,dt,$$
--   where the center logarithm is real. On the zero-free unit polydisc this is the normalized holomorphic logarithm, rather than pointwise principal logarithms. Polynomiality and zero-freeness make the radial integrand continuous there. Off that domain the total definition is not used by the theorem statements.
--
--   For a multi-index $q\in\mathbb N^{[n]\times\mathbb Z_M}$, put $d=|q|=\sum_lq_l$, $P_0=P(0)$ and $R=P/P_0-1$. The computed Taylor coefficients are
--   $$a_0=\log P_0,\qquad a_q=[y^q]\sum_{r=1}^{d}\frac{(-1)^{r+1}}rR(y)^r\quad(d>0).$$
--   The finite formula equals the Taylor coefficient of the normalized logarithm because $R(0)=0$; it is not a free coefficient array. Finally $u_k=\Phi(\sigma_0\sigma_k y_\star)+\Phi(y_\star)-\Phi(\sigma_0 y_\star)-\Phi(\sigma_k y_\star)$. This layer fixes both the branch convention used in the modulus bound and the precise coefficients used in the support lemma.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, pp. 7–9, Lemmas 5–7, Eqs. (17)–(23); real center convention p. 5, Eq. (8)

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Trotter
open scoped BigOperators Matrix Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Radial integral of the logarithmic derivative. On the zero-free polydisc
this is the unique holomorphic logarithm with real center value.
It is computed from the trace polynomial, not chosen subject to estimates. -/
def logPartition {n : ℕ} (B : System n) (β : ℝ) (M : ℕ)
    (y : LayerVariables n M) : ℂ :=
  (Real.log (trotterPartition B β M 0).re : ℂ) +
    ∫ t : ℝ in (0)..1,
      deriv (fun z : ℂ => trotterPartition B β M (fun l => z * y l)) (t : ℂ) /
        trotterPartition B β M (fun l => (t : ℂ) * y l)

/-- Formal Taylor coefficients of the normalized logarithm. For q ≠ 0,
only powers 1 through |q| of Z/Z(0)-1 can contribute. -/
def logCoefficient {n : ℕ} (B : System n) (β : ℝ) (M : ℕ)
    (q : Location n M → ℕ) : ℂ :=
  let d := ∑ l, q l
  let P := partitionPolynomial B β M
  let P0 := MvPolynomial.eval (fun _ => 0) P
  let R := MvPolynomial.C P0⁻¹ * P - 1
  if d = 0 then (Real.log P0.re : ℂ)
  else ∑ r ∈ Finset.Icc 1 d,
    ((-1 : ℂ)^(r+1) / r) * MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm q) (R^r)

def logCombination {n : ℕ} (B : System n) (h β : ℝ) (M : ℕ)
    (S : Finset (Fin n)) (k : ℕ) : ℂ :=
  let y : LayerVariables n M := starPoint h β
  logPartition B β M (reflectLayer S 0 (reflectLayer S k y)) + logPartition B β M y -
    logPartition B β M (reflectLayer S 0 y) - logPartition B β M (reflectLayer S k y)
end LeeYangGap.SpectralGap


