-- Prove2me | Definitions.Def_Transport_PhysicalHigh_TunedData
-- name    : Transport_PhysicalHigh_TunedData
-- status  : Definition
-- author  : @Himan
-- created : 2026-11-15T03:24:02.20302+00:00
-- url     : https://prove2.me/theorems/399424d0-de55-4ea5-915a-697165452459
-- title:
--   Tuned high-side scalar data: reserved loss, conductor cap and the record $\mathrm{TunedData}(K_{\min},a)$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). The tuned constants of LW56e2's refinement are $p=214651/1250000000$, the Gram exponent $b=192821/1562500$, the total slot length $\ell=\tfrac16+p$, the row and column exponents $\ell_x=(1-\ell-b)/2$ and $\ell_y=(1-\ell+b)/2$, the conductor exponent $h=(1+3\ell+b)/2$, the cushion $\zeta=1/(8\cdot 10^{12})$, the boundary $B=\tfrac{11}{12}-\tfrac{\ell}{4}=4374785349/5000000000$ and the signal exponent $\operatorname{sig}(s)=s+\ell_x/2-1+h/6=s-2147607/3125000$.
--
--   This file fixes the scalar data of the high-side estimate at the tuned boundary.
--
--   1. **Reserved loss.** $t=10^{-15}$.
--
--   2. **Conductor cap.** $d_{\max}=h+\zeta+2t$, the largest conductor exponent that the tuned detector is allowed to reach.
--
--   3. **Tuned data.** For a natural number $K_{\min}$ and a real allowance $a$, a record $\mathrm{TunedData}(K_{\min},a)$ consists of
--      - a positive even number of slots $K\ge K_{\min}$;
--      - slot lengths $\ell_j\in\mathbb R$, $j=1,\dots,K$, pairwise distinct, with $\sum_j\ell_j=\ell$;
--      - the minimal slot length $\ell_{\min}=\ell/(2K)>0$ and the minimal conductor ratio $r_{\min}=\ell_{\min}/d_{\max}>0$, with
--   $$
--   \ell_{\min}\le \ell_j\le \frac{t}{200},\qquad \ell_j\le\frac{\operatorname{plainMesh}(t)}{200}\qquad(1\le j\le K);
--   $$
--      - a system $P$ of detector scales $(\varepsilon,e,\kappa,\mathrm{cost},\mathrm{eps},\sigma)$ for the parameters $(t,K,r_{\min},\ell_{\min},a)$, that is, positive reals bounded by the allowance $a$ and satisfying the budget inequalities of the definition `Transport_PhysicalHigh_Parameters`.
--
--   The record collects every scalar choice of the high-side argument in the order in which the source makes them: the loss $t$ and the mesh are fixed first, then $K$ and the slots, and the detector scales last, so that the allowance $a$ may depend on the final contradiction gap without affecting the slots.
--
--   **Formalization Note** Transcribed verbatim from the source. `reservedLoss` is an `abbrev`; the structure field `P` has type `DetectorScales reservedLoss K rmin ellMin allowance`. The source's derived inequalities about these objects (for example `conductorCap_pos`, `TunedData.high_budget`) are theorems and are not included here.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/TunedData.lean, reservedLoss (L17), conductorCap (L18), structure TunedData (L35-L53): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/TunedData.lean#L17-L53

import Mathlib
import Definitions.Def_Transport_PhysicalHigh_Parameters
import Definitions.Def_Transport_PhysicalHigh_EnergyMesh

set_option autoImplicit false

/-!
# Complete tuned high-side scalar data

The reserved high loss and capacity are fixed first. The energy mesh is
therefore fixed before K. The slot construction allows any prior lower
bound on K. The positive allowance may depend on the later contradiction
gap; it only affects post-slot errors, not the selected slots.
-/

namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators

abbrev reservedLoss : ℝ := 1 / 1000000000000000
noncomputable def conductorCap : ℝ := TunedCandidate.h + TunedCandidate.zeta + 2 * reservedLoss

structure TunedData (Kmin : ℕ) (allowance : ℝ) where
  K : ℕ
  K_large : Kmin ≤ K
  K_pos : 0 < K
  K_even : Even K
  ell : Fin K → ℝ
  ellMin : ℝ
  rmin : ℝ
  ellMin_eq : ellMin = TunedCandidate.ell / (2 * K)
  rmin_eq : rmin = ellMin / conductorCap
  ellMin_pos : 0 < ellMin
  rmin_pos : 0 < rmin
  slots_injective : Function.Injective ell
  slots_sum : (∑ j, ell j) = TunedCandidate.ell
  slots_pos : ∀ j, 0 < ell j
  slots_lower : ∀ j, ellMin ≤ ell j
  slots_upper : ∀ j, ell j ≤ (1 / 200 : ℝ) * reservedLoss
  slots_fine : ∀ j, ell j ≤ plainMesh reservedLoss / 200
  P : DetectorScales reservedLoss K rmin ellMin allowance

end
end RH.Transport.PhysicalHigh


