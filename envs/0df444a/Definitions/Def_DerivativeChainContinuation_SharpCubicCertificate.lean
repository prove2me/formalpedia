-- Prove2me | Definitions.Def_DerivativeChainContinuation_SharpCubicCertificate
-- name    : DerivativeChainContinuation_SharpCubicCertificate
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T23:09:49.175711+00:00
-- url     : https://prove2.me/theorems/e5b955be-4d64-45c0-9bcc-99e0eebc0f7b
-- title:
--   Cubic side squares and an explicit polynomial certificate
-- statement:
--   For real $k,s$, define
--
--   $$U=\frac{(3-k)^2+s^2(k+1)^2}4,\quad V=\frac{(3+k)^2+s^2(k-1)^2}4,\quad W=k^2+s^2.$$
--
--   These are the three squared side lengths of the accompanying centered configuration. The bundle also defines the explicit real polynomial certificate in variables $k,t$ by its full rational-coefficient expression. Separate lemmas establish the parameter-dependent sign and geometric inequalities; the definition stores the polynomial data.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicCertificate.lean#L10-L17; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicCertificate.lean#L6-L6; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicCertificate.lean#L7-L7; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpCubicCertificate.lean#L8-L8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainContinuation

noncomputable def cubicSideU (k s : ℝ) : ℝ := ((3-k)^2+s^2*(k+1)^2)/4
noncomputable def cubicSideV (k s : ℝ) : ℝ := ((3+k)^2+s^2*(k-1)^2)/4
noncomputable def cubicSideW (k s : ℝ) : ℝ := k^2+s^2

noncomputable def sharpCubicCertificate (k t : ℝ) : ℝ :=
  (1-k)/10*(
    1*k^0*(1-k)^5*(3040*t^0 + 20480*t^1 + 26920*t^2 + 20480*t^3 + 11440*t^4 + 4520*t^5 + 970*t^6 + 140*t^7 + 10*t^8) +
    5*k^1*(1-k)^4*(1920*t^0 + 19392*t^1 + 25392*t^2 + 19392*t^3 + 11568*t^4 + 4992*t^5 + 1164*t^6 + 168*t^7 + 12*t^8) +
    10*k^2*(1-k)^3*(1216*t^0 + 19136*t^1 + 25672*t^2 + 20216*t^3 + 12532*t^4 + 5552*t^5 + 1306*t^6 + 182*t^7 + 13*t^8) +
    10*k^3*(1-k)^2*(768*t^0 + 18816*t^1 + 27264*t^2 + 23136*t^3 + 14448*t^4 + 6144*t^5 + 1344*t^6 + 168*t^7 + 12*t^8) +
    5*k^4*(1-k)^1*(512*t^0 + 17920*t^1 + 30272*t^2 + 28864*t^3 + 17696*t^4 + 6784*t^5 + 1232*t^6 + 112*t^7 + 8*t^8) +
    1*k^5*(1-k)^0*(15360*t^1 + 34560*t^2 + 38400*t^3 + 23040*t^4 + 7680*t^5 + 960*t^6))







end DerivativeChainContinuation


