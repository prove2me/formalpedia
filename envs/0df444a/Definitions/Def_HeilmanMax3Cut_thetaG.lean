-- Prove2me | Definitions.Def_HeilmanMax3Cut_thetaG
-- name    : HeilmanMax3Cut_thetaG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:02.057609+00:00
-- url     : https://prove2.me/theorems/536894e0-487b-40d8-9d7a-74ea633ae7b6
-- title:
--   The first-mode gain $\theta(a)$
-- statement:
--   For $a\ge0$,
--
--   $$\theta(a)=\frac{j^{(1)}}{2}\,\frac{a\,e^{-a}}{I_0(a)},$$
--
--   the gain in the joint arc bound obtained from the first angular mode (Corollary 8.4).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (92), p.29

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI
import Definitions.Def_HeilmanMax3Cut_j1
open QueueingFundamentals.Transient

namespace HeilmanMax3Cut

/-- **The first-mode gain `θ(a)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (92), p.29: `θ(a) := (j^{(1)}/2) · a e^{−a} / I₀(a)`
for `a ≥ 0`.

**Formalization Note.** `I₀` is the published `QueueingFundamentals.Transient.besselI 0`
(`I₀(a) ≥ 1`). Named `thetaG` to keep it apart from the partition `Θ`. -/
noncomputable def thetaG (a : ℝ) : ℝ :=
  j1 / 2 * a * Real.exp (-a) / besselI 0 a

end HeilmanMax3Cut


