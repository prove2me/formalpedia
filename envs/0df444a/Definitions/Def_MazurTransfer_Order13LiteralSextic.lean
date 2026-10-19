-- Prove2me | Definitions.Def_MazurTransfer_Order13LiteralSextic
-- name    : MazurTransfer_Order13LiteralSextic
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T10:06:23.68293+00:00
-- url     : https://prove2.me/theorems/8374caa5-9738-4d11-abfc-d962d6fa6c51
-- title:
--   The literal order-thirteen sextic over every commutative ring
-- statement:
--   For any commutative ring $R$, the original sextic evaluation is $$s(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1.$$ This is the fixed polynomial used by both the actual diamond coordinate substitution and the Pell certificate for the order-thirteen curve.
-- source:
--   Original complete sextic declaration and body from MazurTheorem Order13PellChartCertificate.lean, Apache-2.0, Vas and contributors. Coefficients originate in MazurTorsion/NumberTheory/XOneThirteenDescent.lean at pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, retained source SHA256 10a30be619946d1c2a3207bffb758840f80ff71dcbb0ee5c3dd0d068cc80961f. The single full original closed type and data value are kernel-compared. Native, strict and complete frontend checks pass with standard axioms only. Named downstream consumers: actual diamond coordinate transformation and the Pell polynomial certificate.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Polynomial from MazurTheorem XOneThirteenDescent.lean at source pin
54d43d8dda8a6fcf069cc02a815f850d762c5c0c, SHA256
10a30be619946d1c2a3207bffb758840f80ff71dcbb0ee5c3dd0d068cc80961f.
Design boundary: the original sextic evaluation over every commutative ring.
Named downstream consumers: the actual diamond substitution and Pell certificate. -/
import Mathlib
noncomputable section
universe u
namespace MazurTransfer.Order13PellChartCertificate
variable {R : Type u} [CommRing R]
def sextic (x : R) : R :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1
end MazurTransfer.Order13PellChartCertificate
#print axioms MazurTransfer.Order13PellChartCertificate.sextic


