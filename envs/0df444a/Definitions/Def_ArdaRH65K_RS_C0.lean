-- Prove2me | Definitions.Def_ArdaRH65K_RS_C0
-- name    : ArdaRH65K_RS_C0
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:32:32.751633+00:00
-- url     : https://prove2.me/theorems/be37b451-ed5d-4504-b1b4-7b14d9ffe061
-- title:
--   Riemann–Siegel saddle integral
-- statement:
--   For real $p$, let $D(z)=e^{\pi iz}-e^{-\pi iz}$. This bundle defines
--
--   $$J(p)=\int_{\mathbb R}\frac{e^{2\pi i(v(1+i))^2}}{D(p+v(1+i))}(1+i)\,dv.$$
--
--   Complex division and integration use the total formal conventions. Later bounds
--   apply this integral for $0<p<1$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_C0.lean

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
/-  RS_C0.lean -- lane RS, brick B3 (the Riemann-Siegel remainder), part 1: RIEMANN'S Psi.
    Mathlib-only (imports `RS_B2`).

    The main term of the Riemann-Siegel remainder is the Mordell integral with Gaussian e^{2 pi i w^2}
    (tau = 2):
        rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / (e^{i pi (p+w)} - e^{-i pi (p+w)})),   0 < p < 1.
    Its value is not elementary, but the combination that enters Z(t) is:

        2 Re(e^{-i pi/8} rsJ p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p) = Psi(p)   (Gabcke's C0).

    Proof (no residue theorem): write e^{i pi w^2} as a Gaussian Fourier integral along the (1-i)
    line, swap the two line integrals (Fubini), evaluate the inner one by the tau = 1 Mordell closed
    form (RS_Kernel), split the outer one into a tau = -1 Mordell integral (closed form by conjugation
    and one pole crossing) and a tau = -2 integral that is the conjugate of rsJ itself (symmetry
    rsJ(1-p) = rsJ(p)).  This gives rsJ + e^{i pi/4} conj(rsJ) = elementary, whose real part after the
    phase e^{-i pi/8} is Psi.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Linearity for `lineDn`, translations -/









/-! ## 2. The Gaussian as a Fourier integral along the (1-i) line -/





/-! ## 3. The tau = 2 Mordell integral and its symmetry -/

/-- The tau = 2 Mordell integral: `rsJ p = lineUp 0 (w |-> e^{2 pi i w^2} / rsD (p + w))`. -/
def rsJ (p : ℝ) : ℂ := lineUp 0 (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w))













/-! ## 4. Fubini: rsJ as an iterated integral -/



/-! ## 5. The inner integral: the tau = 1 Mordell closed form -/



/-! ## 6. The outer integral splits into T1 - T2 -/









/-! ## 7. T2 is the conjugate of rsJ; T1 by one pole crossing and the Mordell formula -/







/-! ## 8. Riemann's Psi -/



end RSInt


def ArdaRH65K_RS_C0 : Nat := 0


