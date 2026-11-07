-- Prove2me | Definitions.Def_HeilmanMax3Cut_Est
-- name    : HeilmanMax3Cut_Est
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:11.789194+00:00
-- url     : https://prove2.me/theorems/bb8087c6-76ba-46cf-8bfb-9ac8aa8c6de6
-- title:
--   The mean-zero kernel $E_*$
-- statement:
--   For $t,s>0$,
--
--   $$E_*(t,s)=K_*(t,s)-u_*(s)-u_*(t)+C_*.$$
--
--   For $z$ with $\int_0^\infty z\,d\nu=0$, $\langle z,E_*z\rangle=\langle z,K_*z\rangle$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (110), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Kst
import Definitions.Def_HeilmanMax3Cut_ust
import Definitions.Def_HeilmanMax3Cut_Cst

namespace HeilmanMax3Cut

/-- **The mean-zero kernel `E_*`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (110), p.31:
`E_*(t, s) = K_*(t, s) − u_*(s) − u_*(t) + C_*`, `t, s > 0`. -/
noncomputable def Est (σ t s : ℝ) : ℝ :=
  Kst σ t s - ust σ s - ust σ t + Cst σ

end HeilmanMax3Cut


