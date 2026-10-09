-- Prove2me | Definitions.Def_actuarial_annualReserveGain
-- name    : actuarial_annualReserveGain
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:16:04.631225+00:00
-- url     : https://prove2.me/theorems/bbb678b1-8660-47f0-b3e0-4bc2ef0f1f10
-- title:
--   Yearly cashflow and prospective reserve release gain
-- statement:
--   Annual insurer net outgo plus discounted closing reserve less opening reserve at the year's start.
--
--   **Mathematical statement**
--
--   $$
--   G_k(\omega)=C_k(\omega)+vR_{k+1}-R_k
--   $$
-- source:
--   Gerber (1997), Life Insurance Mathematics, third edition, §6.7 equations (6.7.3), (6.7.6)-(6.7.10); Bladt et al., An elementary derivation of Hattendorff's theorem (2021), https://doi.org/10.1007/s13385-020-00256-9; R. Norberg (1992), Hattendorff's theorem and Thiele's differential equation generalized, https://doi.org/10.1080/03461238.1992.10413894

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def annualReserveGain {Ω : Type*}
  (C : ℕ → Ω → ℝ) (R : ℕ → ℝ) (v : ℝ)
  (k : ℕ) (ω : Ω) : ℝ :=
  C k ω + v * R (k + 1) - R k

end ActuarialValuation


