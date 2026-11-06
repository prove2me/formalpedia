-- Prove2me | Definitions.Def_GnpColoring_bochnerOp
-- name    : GnpColoring_bochnerOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:16.877603+00:00
-- url     : https://prove2.me/theorems/e54eb874-5ee5-4c10-a83b-6020cf8c9a1c
-- title:
--   The Bochner operator $B_\kappa=\tilde L^2-\kappa q\tilde L$
-- statement:
--   For real $\kappa$, $B_\kappa=\tilde L^2-\kappa q\tilde L$, i.e. $B_\kappa f=\tilde L(\tilde Lf)-\kappa q\,\tilde Lf$. Its positivity yields the spectral gap of the block dynamics (Lemma 3.4).
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.2, p.16

import Mathlib
import Definitions.Def_GnpColoring_accelGen

open scoped Classical
open Finset

namespace GnpColoring

/-- **The Bochner operator** `B_κ = L̃² − κ q L̃`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.2, p.16: "Expanding the Bochner operator B_κ = L̃² − κqL̃". -/
noncomputable def bochnerOp {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (S : Finset (Fin n)) (κ : ℝ)
    (f : (Fin n → Fin q) → ℝ) : (Fin n → Fin q) → ℝ :=
  fun x => accelGen G q S (accelGen G q S f) x - κ * (q : ℝ) * accelGen G q S f x

end GnpColoring


