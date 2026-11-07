-- Prove2me | Definitions.Def_NSWBetter_corrFrac
-- name    : NSWBetter_corrFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:03.050418+00:00
-- url     : https://prove2.me/theorems/ee92699b-e31c-4664-acd7-95697c83ea75
-- title:
--   Corresponding fractional allocation $x_{ig}=\sum_{S\ni g}y_{i,S}$
-- statement:
--   The **corresponding fractional allocation** of a configuration LP solution $y$ is $x_{ig}=\sum_{S:\,g\in S}y_{i,S}$ (Eq. (7)).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4.2, p.19, Eq. (7)

import Mathlib

namespace NSWBetter

open Classical in
/-- **Corresponding fractional allocation (7).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4.2, p.19, Eq. (7): "xig = Σ_(S:g∈S) yi,S." -/
noncomputable def corrFrac {n m : ℕ} (y : Fin n → Finset (Fin m) → ℝ) : Fin n → Fin m → ℝ :=
  fun i g => ∑ S ∈ Finset.univ.filter (fun S => g ∈ S), y i S

end NSWBetter


