-- Prove2me | Definitions.Def_GnpColoring_accelSingle
-- name    : GnpColoring_accelSingle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:12.002703+00:00
-- url     : https://prove2.me/theorems/31bbe644-b37b-4a30-ae93-7f53b02c3521
-- title:
--   The accelerated singleton generator $H_s=a_sL_s$
-- statement:
--   $H_sf(\sigma)=a_s(\sigma)\,L_sf(\sigma)$: the singleton generator sped up by the number of available colours.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.2, p.16

import Mathlib
import Definitions.Def_GnpColoring_availCount
import Definitions.Def_mm_transport
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **The accelerated singleton generator** `H_s = a_s L_s` (pointwise product).

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.2, p.16: "L̃ = Σ_{s∈S} H_s + q Σ_{B∈𝓑} L_B, where H_s = a_s L_s". -/
noncomputable def accelSingle {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (s : Fin n)
    (f : (Fin n → Fin q) → ℝ) : (Fin n → Fin q) → ℝ :=
  fun x => (availCount G x s : ℝ) * SpinGirth5.singleLap (MarkovMixing.properColoringDist G q) s f x

end GnpColoring


