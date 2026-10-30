-- Prove2me | Definitions.Def_HellingerSubadd_hellinger
-- name    : HellingerSubadd_hellinger
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:27.587929+00:00
-- url     : https://prove2.me/theorems/5deeafbe-c886-491b-aabb-fdafe23c1969
-- title:
--   Hellinger distance $D_{\mathrm H}(\mu,\nu)=\sqrt{D^2_{\mathrm H}(\mu,\nu)}$
-- statement:
--   For measures $\mu,\nu$ on a measurable space, the **Hellinger distance** is the square root of the squared Hellinger distance:
--
--   $$
--   D_{\mathrm H}(\mu,\nu)=\sqrt{D^2_{\mathrm H}(\mu,\nu)}.
--   $$
--
--   It is the quantity for which the proof of Lemma A.13 invokes the triangle inequality.
--
--   **Formalization Note** The value is the real number $\sqrt{\cdot}$ of the real part of $D^2_{\mathrm H}(\mu,\nu)\in[0,\infty]$. For finite measures $D^2_{\mathrm H}(\mu,\nu)\le\mu(\Omega)+\nu(\Omega)<\infty$, so nothing is lost; the mission uses $D_{\mathrm H}$ only for finite measures.
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Section 2, eq. (5), p. 10; proof of Lemma A.13, p. 73

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Hellinger distance** `D_H(μ, ν) = √(D²_H(μ, ν))`.
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Section 2, eq. (5), p. 10 (the square root of the squared Hellinger
distance), as used in the proof of Lemma A.13, p. 73.

**Formalization Note.** The real number `√(toReal (D²_H(μ, ν)))`. For finite measures
`D²_H(μ, ν) ≤ μ(univ) + ν(univ) < ∞`, so `toReal` loses nothing; every theorem of the mission
uses `hellinger` only for finite measures. -/
noncomputable def hellinger {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  Real.sqrt (hellingerSq μ ν).toReal

end HellingerSubadd


